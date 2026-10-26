import V185TrunkScan23Chunk0558

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3304827 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4]
def baseStart_3304827 : Nat := 118140960795 + 3304827 * 2 ^ 59
def prefixEnd_3304827 : Nat := 4983230072969 + 3 ^ 40 * 3304827 * 2
def baseEnd_3304827 : Nat := 1696964730956446582863883

theorem tailTrace_3304827 : CollatzResearch.WordTrace tailWord_3304827 prefixEnd_3304827 1696964730956446582863883 := by
  unfold tailWord_3304827
  simp only [CollatzResearch.WordTrace]
  refine ⟨120536943198183673360976735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80357962132122448907317823 120536943198183673360976735)
  ·
    refine ⟨180805414797275510041465103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120536943198183673360976735 180805414797275510041465103)
    ·
      refine ⟨271208122195913265062197655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180805414797275510041465103 271208122195913265062197655)
      ·
        refine ⟨406812183293869897593296483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271208122195913265062197655 406812183293869897593296483)
        ·
          refine ⟨610218274940804846389944725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406812183293869897593296483 610218274940804846389944725)
          ·
            refine ⟨28603981637850227174528659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 610218274940804846389944725 28603981637850227174528659)
            ·
              refine ⟨42905972456775340761792989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28603981637850227174528659 42905972456775340761792989)
              ·
                refine ⟨16089739671290752785672371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42905972456775340761792989 16089739671290752785672371)
                ·
                  refine ⟨24134609506936129178508557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16089739671290752785672371 24134609506936129178508557)
                  ·
                    refine ⟨9050478565101048441940709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24134609506936129178508557 9050478565101048441940709)
                    ·
                      refine ⟨1696964730956446582863883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9050478565101048441940709 1696964730956446582863883)
                      ·
                        rfl

theorem cell23_3304827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_3304827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304827 prefixEnd_3304827 := by exact prefixLift 3304827
  have htrace : WordTrace (prefixWord ++ tailWord_3304827) baseStart_3304827 baseEnd_3304827 := by
    simpa [prefixWord, tailWord_3304827, baseEnd_3304827] using wordTrace_append hprefix tailTrace_3304827
  have hstable : (prefixWord ++ tailWord_3304827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304827).length < 2 ^ (prefixWord ++ tailWord_3304827).sum := by decide
  have hdescent : baseEnd_3304827 < baseStart_3304827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304844 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3304844 : Nat := 118140960795 + 3304844 * 2 ^ 59
def prefixEnd_3304844 : Nat := 4983230072969 + 3 ^ 40 * 3304844 * 2
def baseEnd_3304844 : Nat := 1696973460127573016351305

theorem tailTrace_3304844 : CollatzResearch.WordTrace tailWord_3304844 prefixEnd_3304844 1696973460127573016351305 := by
  unfold tailWord_3304844
  simp only [CollatzResearch.WordTrace]
  refine ⟨60268781619561042632172793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80358375492748056842897057 60268781619561042632172793)
  ·
    refine ⟨45201586214670781974129595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60268781619561042632172793 45201586214670781974129595)
    ·
      refine ⟨67802379322006172961194393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45201586214670781974129595 67802379322006172961194393)
      ·
        refine ⟨50851784491504629720895795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67802379322006172961194393 50851784491504629720895795)
        ·
          refine ⟨76277676737256944581343693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50851784491504629720895795 76277676737256944581343693)
          ·
            refine ⟨28604128776471354218003885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76277676737256944581343693 28604128776471354218003885)
            ·
              refine ⟨10726548291176757831751457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28604128776471354218003885 10726548291176757831751457)
              ·
                refine ⟨8044911218382568373813593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10726548291176757831751457 8044911218382568373813593)
                ·
                  refine ⟨6033683413786926280360195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8044911218382568373813593 6033683413786926280360195)
                  ·
                    refine ⟨9050525120680389420540293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6033683413786926280360195 9050525120680389420540293)
                    ·
                      refine ⟨1696973460127573016351305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9050525120680389420540293 1696973460127573016351305)
                      ·
                        rfl

theorem cell23_3304844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3304844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304844 prefixEnd_3304844 := by exact prefixLift 3304844
  have htrace : WordTrace (prefixWord ++ tailWord_3304844) baseStart_3304844 baseEnd_3304844 := by
    simpa [prefixWord, tailWord_3304844, baseEnd_3304844] using wordTrace_append hprefix tailTrace_3304844
  have hstable : (prefixWord ++ tailWord_3304844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304844).length < 2 ^ (prefixWord ++ tailWord_3304844).sum := by decide
  have hdescent : baseEnd_3304844 < baseStart_3304844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304847 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 3]
def baseStart_3304847 : Nat := 118140960795 + 3304847 * 2 ^ 59
def prefixEnd_3304847 : Nat := 4983230072969 + 3 ^ 40 * 3304847 * 2
def baseEnd_3304847 : Nat := 1696975000569536504613791

theorem tailTrace_3304847 : CollatzResearch.WordTrace tailWord_3304847 prefixEnd_3304847 1696975000569536504613791 := by
  unfold tailWord_3304847
  simp only [CollatzResearch.WordTrace]
  refine ⟨120537672658111216776704795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80358448438740811184469863 120537672658111216776704795)
  ·
    refine ⟨180806508987166825165057193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120537672658111216776704795 180806508987166825165057193)
    ·
      refine ⟨135604881740375118873792895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180806508987166825165057193 135604881740375118873792895)
      ·
        refine ⟨203407322610562678310689343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135604881740375118873792895 203407322610562678310689343)
        ·
          refine ⟨305110983915844017466034015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203407322610562678310689343 305110983915844017466034015)
          ·
            refine ⟨457666475873766026199051023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305110983915844017466034015 457666475873766026199051023)
            ·
              refine ⟨686499713810649039298576535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457666475873766026199051023 686499713810649039298576535)
              ·
                refine ⟨1029749570715973558947864803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686499713810649039298576535 1029749570715973558947864803)
                ·
                  refine ⟨1544624356073960338421797205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029749570715973558947864803 1544624356073960338421797205)
                  ·
                    refine ⟨4525266668185430678970109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1544624356073960338421797205 4525266668185430678970109)
                    ·
                      refine ⟨1696975000569536504613791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525266668185430678970109 1696975000569536504613791)
                      ·
                        rfl

theorem cell23_3304847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_3304847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304847 prefixEnd_3304847 := by exact prefixLift 3304847
  have htrace : WordTrace (prefixWord ++ tailWord_3304847) baseStart_3304847 baseEnd_3304847 := by
    simpa [prefixWord, tailWord_3304847, baseEnd_3304847] using wordTrace_append hprefix tailTrace_3304847
  have hstable : (prefixWord ++ tailWord_3304847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304847).length < 2 ^ (prefixWord ++ tailWord_3304847).sum := by decide
  have hdescent : baseEnd_3304847 < baseStart_3304847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304864 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3]
def baseStart_3304864 : Nat := 118140960795 + 3304864 * 2 ^ 59
def prefixEnd_3304864 : Nat := 4983230072969 + 3 ^ 40 * 3304864 * 2
def baseEnd_3304864 : Nat := 1696983729740662938101213

theorem tailTrace_3304864 : CollatzResearch.WordTrace tailWord_3304864 prefixEnd_3304864 1696983729740662938101213 := by
  unfold tailWord_3304864
  simp only [CollatzResearch.WordTrace]
  refine ⟨60269146349524814340036823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80358861799366419120049097 60269146349524814340036823)
  ·
    refine ⟨90403719524287221510055235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60269146349524814340036823 90403719524287221510055235)
    ·
      refine ⟨135605579286430832265082853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90403719524287221510055235 135605579286430832265082853)
      ·
        refine ⟨25426046116205781049703035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135605579286430832265082853 25426046116205781049703035)
        ·
          refine ⟨38139069174308671574554553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25426046116205781049703035 38139069174308671574554553)
          ·
            refine ⟨28604301880731503680915915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38139069174308671574554553 28604301880731503680915915)
            ·
              refine ⟨42906452821097255521373873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28604301880731503680915915 42906452821097255521373873)
              ·
                refine ⟨32179839615822941641030405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42906452821097255521373873 32179839615822941641030405)
                ·
                  refine ⟨6033719927966801557693201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32179839615822941641030405 6033719927966801557693201)
                  ·
                    refine ⟨4525289945975101168269901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6033719927966801557693201 4525289945975101168269901)
                    ·
                      refine ⟨1696983729740662938101213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525289945975101168269901 1696983729740662938101213)
                      ·
                        rfl

theorem cell23_3304864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_3304864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304864 prefixEnd_3304864 := by exact prefixLift 3304864
  have htrace : WordTrace (prefixWord ++ tailWord_3304864) baseStart_3304864 baseEnd_3304864 := by
    simpa [prefixWord, tailWord_3304864, baseEnd_3304864] using wordTrace_append hprefix tailTrace_3304864
  have hstable : (prefixWord ++ tailWord_3304864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304864).length < 2 ^ (prefixWord ++ tailWord_3304864).sum := by decide
  have hdescent : baseEnd_3304864 < baseStart_3304864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304881 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3304881 : Nat := 118140960795 + 3304881 * 2 ^ 59
def prefixEnd_3304881 : Nat := 4983230072969 + 3 ^ 40 * 3304881 * 2
def baseEnd_3304881 : Nat := 1696992458911789371588635

theorem tailTrace_3304881 : CollatzResearch.WordTrace tailWord_3304881 prefixEnd_3304881 1696992458911789371588635 := by
  unfold tailWord_3304881
  simp only [CollatzResearch.WordTrace]
  refine ⟨120538912739988040583442497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80359275159992027055628331 120538912739988040583442497)
  ·
    refine ⟨90404184554991030437581873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120538912739988040583442497 90404184554991030437581873)
    ·
      refine ⟨67803138416243272828186405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90404184554991030437581873 67803138416243272828186405)
      ·
        refine ⟨12713088453045613655284951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67803138416243272828186405 12713088453045613655284951)
        ·
          refine ⟨19069632679568420482927427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12713088453045613655284951 19069632679568420482927427)
          ·
            refine ⟨28604449019352630724391141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19069632679568420482927427 28604449019352630724391141)
            ·
              refine ⟨5363334191128618260823339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28604449019352630724391141 5363334191128618260823339)
              ·
                refine ⟨8045001286692927391235009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363334191128618260823339 8045001286692927391235009)
                ·
                  refine ⟨6033750965019695543426257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045001286692927391235009 6033750965019695543426257)
                  ·
                    refine ⟨4525313223764771657569693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6033750965019695543426257 4525313223764771657569693)
                    ·
                      refine ⟨1696992458911789371588635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525313223764771657569693 1696992458911789371588635)
                      ·
                        rfl

theorem cell23_3304881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3304881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304881 prefixEnd_3304881 := by exact prefixLift 3304881
  have htrace : WordTrace (prefixWord ++ tailWord_3304881) baseStart_3304881 baseEnd_3304881 := by
    simpa [prefixWord, tailWord_3304881, baseEnd_3304881] using wordTrace_append hprefix tailTrace_3304881
  have hstable : (prefixWord ++ tailWord_3304881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304881).length < 2 ^ (prefixWord ++ tailWord_3304881).sum := by decide
  have hdescent : baseEnd_3304881 < baseStart_3304881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304938 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_3304938 : Nat := 118140960795 + 3304938 * 2 ^ 59
def prefixEnd_3304938 : Nat := 4983230072969 + 3 ^ 40 * 3304938 * 2
def baseEnd_3304938 : Nat := 1697021727309095648575873

theorem tailTrace_3304938 : CollatzResearch.WordTrace tailWord_3304938 prefixEnd_3304938 1697021727309095648575873 := by
  unfold tailWord_3304938
  simp only [CollatzResearch.WordTrace]
  refine ⟨30135247925195384829566867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80360661133854359545511645 30135247925195384829566867)
  ·
    refine ⟨45202871887793077244350301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30135247925195384829566867 45202871887793077244350301)
    ·
      refine ⟨16951076957922403966631363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45202871887793077244350301 16951076957922403966631363)
      ·
        refine ⟨25426615436883605949947045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16951076957922403966631363 25426615436883605949947045)
        ·
          refine ⟨4767490394415676115615071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25426615436883605949947045 4767490394415676115615071)
          ·
            refine ⟨7151235591623514173422607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767490394415676115615071 7151235591623514173422607)
            ·
              refine ⟨10726853387435271260133911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151235591623514173422607 10726853387435271260133911)
              ·
                refine ⟨16090280081152906890200867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10726853387435271260133911 16090280081152906890200867)
                ·
                  refine ⟨24135420121729360335301301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16090280081152906890200867 24135420121729360335301301)
                  ·
                    refine ⟨2262695636412127531434497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24135420121729360335301301 2262695636412127531434497)
                    ·
                      refine ⟨1697021727309095648575873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2262695636412127531434497 1697021727309095648575873)
                      ·
                        rfl

theorem cell23_3304938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_3304938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304938 prefixEnd_3304938 := by exact prefixLift 3304938
  have htrace : WordTrace (prefixWord ++ tailWord_3304938) baseStart_3304938 baseEnd_3304938 := by
    simpa [prefixWord, tailWord_3304938, baseEnd_3304938] using wordTrace_append hprefix tailTrace_3304938
  have hstable : (prefixWord ++ tailWord_3304938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304938).length < 2 ^ (prefixWord ++ tailWord_3304938).sum := by decide
  have hdescent : baseEnd_3304938 < baseStart_3304938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304944 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 1, 6]
def baseStart_3304944 : Nat := 118140960795 + 3304944 * 2 ^ 59
def prefixEnd_3304944 : Nat := 4983230072969 + 3 ^ 40 * 3304944 * 2
def baseEnd_3304944 : Nat := 565674936064340875033615

theorem tailTrace_3304944 : CollatzResearch.WordTrace tailWord_3304944 prefixEnd_3304944 565674936064340875033615 := by
  unfold tailWord_3304944
  simp only [CollatzResearch.WordTrace]
  refine ⟨60270605269379901171492943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80360807025839868228657257 60270605269379901171492943)
  ·
    refine ⟨90405907904069851757239415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60270605269379901171492943 90405907904069851757239415)
    ·
      refine ⟨135608861856104777635859123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90405907904069851757239415 135608861856104777635859123)
      ·
        refine ⟨203413292784157166453788685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135608861856104777635859123 203413292784157166453788685)
        ·
          refine ⟨76279984794058937420170757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203413292784157166453788685 76279984794058937420170757)
          ·
            refine ⟨14302497148886050766282017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76279984794058937420170757 14302497148886050766282017)
            ·
              refine ⟨10726872861664538074711513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14302497148886050766282017 10726872861664538074711513)
              ·
                refine ⟨8045154646248403556033635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10726872861664538074711513 8045154646248403556033635)
                ·
                  refine ⟨12067731969372605334050453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045154646248403556033635 12067731969372605334050453)
                  ·
                    refine ⟨565674936064340875033615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12067731969372605334050453 565674936064340875033615)
                    ·
                      rfl

theorem cell23_3304944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_3304944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304944 prefixEnd_3304944 := by exact prefixLift 3304944
  have htrace : WordTrace (prefixWord ++ tailWord_3304944) baseStart_3304944 baseEnd_3304944 := by
    simpa [prefixWord, tailWord_3304944, baseEnd_3304944] using wordTrace_append hprefix tailTrace_3304944
  have hstable : (prefixWord ++ tailWord_3304944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304944).length < 2 ^ (prefixWord ++ tailWord_3304944).sum := by decide
  have hdescent : baseEnd_3304944 < baseStart_3304944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304945 : List Nat := [1, 2, 2, 2, 3, 3, 2, 3, 1, 1, 3]
def baseStart_3304945 : Nat := 118140960795 + 3304945 * 2 ^ 59
def prefixEnd_3304945 : Nat := 4983230072969 + 3 ^ 40 * 3304945 * 2
def baseEnd_3304945 : Nat := 1697025321673677121188341

theorem tailTrace_3304945 : CollatzResearch.WordTrace tailWord_3304945 prefixEnd_3304945 1697025321673677121188341 := by
  unfold tailWord_3304945
  simp only [CollatzResearch.WordTrace]
  refine ⟨120541247011756179513772289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80360831341170786342514859 120541247011756179513772289)
  ·
    refine ⟨90405935258817134635329217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120541247011756179513772289 90405935258817134635329217)
    ·
      refine ⟨67804451444112850976496913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90405935258817134635329217 67804451444112850976496913)
      ·
        refine ⟨50853338583084638232372685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67804451444112850976496913 50853338583084638232372685)
        ·
          refine ⟨19070001968656739337139757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50853338583084638232372685 19070001968656739337139757)
          ·
            refine ⟨7151250738246277251427409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19070001968656739337139757 7151250738246277251427409)
            ·
              refine ⟨5363438053684707938570557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151250738246277251427409 5363438053684707938570557)
              ·
                refine ⟨2011289270131765476963959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5363438053684707938570557 2011289270131765476963959)
                ·
                  refine ⟨3016933905197648215445939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011289270131765476963959 3016933905197648215445939)
                  ·
                    refine ⟨4525400857796472323168909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3016933905197648215445939 4525400857796472323168909)
                    ·
                      refine ⟨1697025321673677121188341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525400857796472323168909 1697025321673677121188341)
                      ·
                        rfl

theorem cell23_3304945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_3304945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304945 prefixEnd_3304945 := by exact prefixLift 3304945
  have htrace : WordTrace (prefixWord ++ tailWord_3304945) baseStart_3304945 baseEnd_3304945 := by
    simpa [prefixWord, tailWord_3304945, baseEnd_3304945] using wordTrace_append hprefix tailTrace_3304945
  have hstable : (prefixWord ++ tailWord_3304945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304945).length < 2 ^ (prefixWord ++ tailWord_3304945).sum := by decide
  have hdescent : baseEnd_3304945 < baseStart_3304945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304954 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_3304954 : Nat := 118140960795 + 3304954 * 2 ^ 59
def prefixEnd_3304954 : Nat := 4983230072969 + 3 ^ 40 * 3304954 * 2
def baseEnd_3304954 : Nat := 1697029942999567585975799

theorem tailTrace_3304954 : CollatzResearch.WordTrace tailWord_3304954 prefixEnd_3304954 1697029942999567585975799 := by
  unfold tailWord_3304954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30135393817180893512712479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80361050179149049367233277 30135393817180893512712479)
  ·
    refine ⟨45203090725771340269068719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30135393817180893512712479 45203090725771340269068719)
    ·
      refine ⟨67804636088657010403603079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45203090725771340269068719 67804636088657010403603079)
      ·
        refine ⟨101706954132985515605404619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67804636088657010403603079 101706954132985515605404619)
        ·
          refine ⟨152560431199478273408106929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101706954132985515605404619 152560431199478273408106929)
          ·
            refine ⟨114420323399608705056080197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152560431199478273408106929 114420323399608705056080197)
            ·
              refine ⟨21453810637426632198015037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114420323399608705056080197 21453810637426632198015037)
              ·
                refine ⟨8045178989034987074255639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21453810637426632198015037 8045178989034987074255639)
                ·
                  refine ⟨12067768483552480611383459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045178989034987074255639 12067768483552480611383459)
                  ·
                    refine ⟨18101652725328720917075189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12067768483552480611383459 18101652725328720917075189)
                    ·
                      refine ⟨1697029942999567585975799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18101652725328720917075189 1697029942999567585975799)
                      ·
                        rfl

theorem cell23_3304954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_3304954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304954 prefixEnd_3304954 := by exact prefixLift 3304954
  have htrace : WordTrace (prefixWord ++ tailWord_3304954) baseStart_3304954 baseEnd_3304954 := by
    simpa [prefixWord, tailWord_3304954, baseEnd_3304954] using wordTrace_append hprefix tailTrace_3304954
  have hstable : (prefixWord ++ tailWord_3304954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304954).length < 2 ^ (prefixWord ++ tailWord_3304954).sum := by decide
  have hdescent : baseEnd_3304954 < baseStart_3304954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304962 : List Nat := [3, 4, 1, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3304962 : Nat := 118140960795 + 3304962 * 2 ^ 59
def prefixEnd_3304962 : Nat := 4983230072969 + 3 ^ 40 * 3304962 * 2
def baseEnd_3304962 : Nat := 1697034050844803554675763

theorem tailTrace_3304962 : CollatzResearch.WordTrace tailWord_3304962 prefixEnd_3304962 1697034050844803554675763 := by
  unfold tailWord_3304962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30135466763173647854285285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80361244701796394278094093 30135466763173647854285285)
  ·
    refine ⟨5650400018095058972678491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30135466763173647854285285 5650400018095058972678491)
    ·
      refine ⟨8475600027142588459017737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650400018095058972678491 8475600027142588459017737)
      ·
        refine ⟨6356700020356941344263303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8475600027142588459017737 6356700020356941344263303)
        ·
          refine ⟨9535050030535412016394955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6356700020356941344263303 9535050030535412016394955)
          ·
            refine ⟨14302575045803118024592433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535050030535412016394955 14302575045803118024592433)
            ·
              refine ⟨10726931284352338518444325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14302575045803118024592433 10726931284352338518444325)
              ·
                refine ⟨2011299615816063472208311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10726931284352338518444325 2011299615816063472208311)
                ·
                  refine ⟨3016949423724095208312467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011299615816063472208311 3016949423724095208312467)
                  ·
                    refine ⟨4525424135586142812468701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3016949423724095208312467 4525424135586142812468701)
                    ·
                      refine ⟨1697034050844803554675763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525424135586142812468701 1697034050844803554675763)
                      ·
                        rfl

theorem cell23_3304962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3304962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304962 prefixEnd_3304962 := by exact prefixLift 3304962
  have htrace : WordTrace (prefixWord ++ tailWord_3304962) baseStart_3304962 baseEnd_3304962 := by
    simpa [prefixWord, tailWord_3304962, baseEnd_3304962] using wordTrace_append hprefix tailTrace_3304962
  have hstable : (prefixWord ++ tailWord_3304962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304962).length < 2 ^ (prefixWord ++ tailWord_3304962).sum := by decide
  have hdescent : baseEnd_3304962 < baseStart_3304962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304968 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_3304968 : Nat := 118140960795 + 3304968 * 2 ^ 59
def prefixEnd_3304968 : Nat := 4983230072969 + 3 ^ 40 * 3304968 * 2
def baseEnd_3304968 : Nat := 1697037131728730531200735

theorem tailTrace_3304968 : CollatzResearch.WordTrace tailWord_3304968 prefixEnd_3304968 1697037131728730531200735 := by
  unfold tailWord_3304968
  simp only [CollatzResearch.WordTrace]
  refine ⟨60271042945336427220929779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80361390593781902961239705 60271042945336427220929779)
  ·
    refine ⟨90406564418004640831394669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60271042945336427220929779 90406564418004640831394669)
    ·
      refine ⟨33902461656751740311773001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90406564418004640831394669 33902461656751740311773001)
      ·
        refine ⟨25426846242563805233829751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33902461656751740311773001 25426846242563805233829751)
        ·
          refine ⟨38140269363845707850744627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25426846242563805233829751 38140269363845707850744627)
          ·
            refine ⟨57210404045768561776116941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38140269363845707850744627 57210404045768561776116941)
            ·
              refine ⟨21453901517163210666043853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57210404045768561776116941 21453901517163210666043853)
              ·
                refine ⟨8045213068936203999766445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21453901517163210666043853 8045213068936203999766445)
                ·
                  refine ⟨3016954900851076499912417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8045213068936203999766445 3016954900851076499912417)
                  ·
                    refine ⟨2262716175638307374934313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3016954900851076499912417 2262716175638307374934313)
                    ·
                      refine ⟨1697037131728730531200735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2262716175638307374934313 1697037131728730531200735)
                      ·
                        rfl

theorem cell23_3304968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_3304968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304968 prefixEnd_3304968 := by exact prefixLift 3304968
  have htrace : WordTrace (prefixWord ++ tailWord_3304968) baseStart_3304968 baseEnd_3304968 := by
    simpa [prefixWord, tailWord_3304968, baseEnd_3304968] using wordTrace_append hprefix tailTrace_3304968
  have hstable : (prefixWord ++ tailWord_3304968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304968).length < 2 ^ (prefixWord ++ tailWord_3304968).sum := by decide
  have hdescent : baseEnd_3304968 < baseStart_3304968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304971 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 5]
def baseStart_3304971 : Nat := 118140960795 + 3304971 * 2 ^ 59
def prefixEnd_3304971 : Nat := 4983230072969 + 3 ^ 40 * 3304971 * 2
def baseEnd_3304971 : Nat := 1697038672170694019463221

theorem tailTrace_3304971 : CollatzResearch.WordTrace tailWord_3304971 prefixEnd_3304971 1697038672170694019463221 := by
  unfold tailWord_3304971
  simp only [CollatzResearch.WordTrace]
  refine ⟨120542195309661985954218767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80361463539774657302812511 120542195309661985954218767)
  ·
    refine ⟨180813292964492978931328151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120542195309661985954218767 180813292964492978931328151)
    ·
      refine ⟨271219939446739468396992227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180813292964492978931328151 271219939446739468396992227)
      ·
        refine ⟨406829909170109202595488341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271219939446739468396992227 406829909170109202595488341)
        ·
          refine ⟨4767537998087217217915879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 406829909170109202595488341 4767537998087217217915879)
          ·
            refine ⟨7151306997130825826873819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767537998087217217915879 7151306997130825826873819)
            ·
              refine ⟨10726960495696238740310729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151306997130825826873819 10726960495696238740310729)
              ·
                refine ⟨8045220371772179055233047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10726960495696238740310729 8045220371772179055233047)
                ·
                  refine ⟨12067830557658268582849571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045220371772179055233047 12067830557658268582849571)
                  ·
                    refine ⟨18101745836487402874274357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12067830557658268582849571 18101745836487402874274357)
                    ·
                      refine ⟨1697038672170694019463221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18101745836487402874274357 1697038672170694019463221)
                      ·
                        rfl

theorem cell23_3304971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 5].length) (baseStart_3304971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304971 prefixEnd_3304971 := by exact prefixLift 3304971
  have htrace : WordTrace (prefixWord ++ tailWord_3304971) baseStart_3304971 baseEnd_3304971 := by
    simpa [prefixWord, tailWord_3304971, baseEnd_3304971] using wordTrace_append hprefix tailTrace_3304971
  have hstable : (prefixWord ++ tailWord_3304971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304971).length < 2 ^ (prefixWord ++ tailWord_3304971).sum := by decide
  have hdescent : baseEnd_3304971 < baseStart_3304971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304981 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_3304981 : Nat := 118140960795 + 3304981 * 2 ^ 59
def prefixEnd_3304981 : Nat := 4983230072969 + 3 ^ 40 * 3304981 * 2
def baseEnd_3304981 : Nat := 1697043806977238980338175

theorem tailTrace_3304981 : CollatzResearch.WordTrace tailWord_3304981 prefixEnd_3304981 1697043806977238980338175 := by
  unfold tailWord_3304981
  simp only [CollatzResearch.WordTrace]
  refine ⟨120542560039625757662082797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80361706693083838441388531 120542560039625757662082797)
  ·
    refine ⟨45203460014859659123281049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120542560039625757662082797 45203460014859659123281049)
    ·
      refine ⟨33902595011144744342460787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45203460014859659123281049 33902595011144744342460787)
      ·
        refine ⟨50853892516717116513691181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33902595011144744342460787 50853892516717116513691181)
        ·
          refine ⟨19070209693768918692634193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50853892516717116513691181 19070209693768918692634193)
          ·
            refine ⟨14302657270326689019475645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19070209693768918692634193 14302657270326689019475645)
            ·
              refine ⟨5363496476372508382303367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14302657270326689019475645 5363496476372508382303367)
              ·
                refine ⟨8045244714558762573455051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363496476372508382303367 8045244714558762573455051)
                ·
                  refine ⟨12067867071838143860182577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045244714558762573455051 12067867071838143860182577)
                  ·
                    refine ⟨9050900303878607895136933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12067867071838143860182577 9050900303878607895136933)
                    ·
                      refine ⟨1697043806977238980338175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9050900303878607895136933 1697043806977238980338175)
                      ·
                        rfl

theorem cell23_3304981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_3304981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304981 prefixEnd_3304981 := by exact prefixLift 3304981
  have htrace : WordTrace (prefixWord ++ tailWord_3304981) baseStart_3304981 baseEnd_3304981 := by
    simpa [prefixWord, tailWord_3304981, baseEnd_3304981] using wordTrace_append hprefix tailTrace_3304981
  have hstable : (prefixWord ++ tailWord_3304981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304981).length < 2 ^ (prefixWord ++ tailWord_3304981).sum := by decide
  have hdescent : baseEnd_3304981 < baseStart_3304981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3304988 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_3304988 : Nat := 118140960795 + 3304988 * 2 ^ 59
def prefixEnd_3304988 : Nat := 4983230072969 + 3 ^ 40 * 3304988 * 2
def baseEnd_3304988 : Nat := 1697047401341820452950643

theorem tailTrace_3304988 : CollatzResearch.WordTrace tailWord_3304988 prefixEnd_3304988 1697047401341820452950643 := by
  unfold tailWord_3304988
  simp only [CollatzResearch.WordTrace]
  refine ⟨60271407675300198928793809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80361876900400265238391745 60271407675300198928793809)
  ·
    refine ⟨45203555756475149196595357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60271407675300198928793809 45203555756475149196595357)
    ·
      refine ⟨16951333408678180948723259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45203555756475149196595357 16951333408678180948723259)
      ·
        refine ⟨25427000113017271423084889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16951333408678180948723259 25427000113017271423084889)
        ·
          refine ⟨19070250084762953567313667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25427000113017271423084889 19070250084762953567313667)
          ·
            refine ⟨28605375127144430350970501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19070250084762953567313667 28605375127144430350970501)
            ·
              refine ⟨5363507836339580690806969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28605375127144430350970501 5363507836339580690806969)
              ·
                refine ⟨4022630877254685518105227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5363507836339580690806969 4022630877254685518105227)
                ·
                  refine ⟨6033946315882028277157841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022630877254685518105227 6033946315882028277157841)
                  ·
                    refine ⟨4525459736911521207868381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6033946315882028277157841 4525459736911521207868381)
                    ·
                      refine ⟨1697047401341820452950643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525459736911521207868381 1697047401341820452950643)
                      ·
                        rfl

theorem cell23_3304988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_3304988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3304988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3304988 prefixEnd_3304988 := by exact prefixLift 3304988
  have htrace : WordTrace (prefixWord ++ tailWord_3304988) baseStart_3304988 baseEnd_3304988 := by
    simpa [prefixWord, tailWord_3304988, baseEnd_3304988] using wordTrace_append hprefix tailTrace_3304988
  have hstable : (prefixWord ++ tailWord_3304988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3304988).length < 2 ^ (prefixWord ++ tailWord_3304988).sum := by decide
  have hdescent : baseEnd_3304988 < baseStart_3304988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3304988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305018 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_3305018 : Nat := 118140960795 + 3305018 * 2 ^ 59
def prefixEnd_3305018 : Nat := 4983230072969 + 3 ^ 40 * 3305018 * 2
def baseEnd_3305018 : Nat := 1697062805761455335575505

theorem tailTrace_3305018 : CollatzResearch.WordTrace tailWord_3305018 prefixEnd_3305018 1697062805761455335575505 := by
  unfold tailWord_3305018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30135977385122928245294927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80362606360327808654119805 30135977385122928245294927)
  ·
    refine ⟨45203966077684392367942391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30135977385122928245294927 45203966077684392367942391)
    ·
      refine ⟨67805949116526588551913587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45203966077684392367942391 67805949116526588551913587)
      ·
        refine ⟨101708923674789882827870381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67805949116526588551913587 101708923674789882827870381)
        ·
          refine ⟨38140846378046206060451393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101708923674789882827870381 38140846378046206060451393)
          ·
            refine ⟨28605634783534654545338545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38140846378046206060451393 28605634783534654545338545)
            ·
              refine ⟨21454226087650990909003909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28605634783534654545338545 21454226087650990909003909)
              ·
                refine ⟨4022667391434560795438233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21454226087650990909003909 4022667391434560795438233)
                ·
                  refine ⟨3017000543575920596578675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022667391434560795438233 3017000543575920596578675)
                  ·
                    refine ⟨4525500815363880894868013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017000543575920596578675 4525500815363880894868013)
                    ·
                      refine ⟨1697062805761455335575505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525500815363880894868013 1697062805761455335575505)
                      ·
                        rfl

theorem cell23_3305018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_3305018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305018 prefixEnd_3305018 := by exact prefixLift 3305018
  have htrace : WordTrace (prefixWord ++ tailWord_3305018) baseStart_3305018 baseEnd_3305018 := by
    simpa [prefixWord, tailWord_3305018, baseEnd_3305018] using wordTrace_append hprefix tailTrace_3305018
  have hstable : (prefixWord ++ tailWord_3305018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305018).length < 2 ^ (prefixWord ++ tailWord_3305018).sum := by decide
  have hdescent : baseEnd_3305018 < baseStart_3305018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305024 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_3305024 : Nat := 118140960795 + 3305024 * 2 ^ 59
def prefixEnd_3305024 : Nat := 4983230072969 + 3 ^ 40 * 3305024 * 2
def baseEnd_3305024 : Nat := 1697065886645382312100477

theorem tailTrace_3305024 : CollatzResearch.WordTrace tailWord_3305024 prefixEnd_3305024 1697065886645382312100477 := by
  unfold tailWord_3305024
  simp only [CollatzResearch.WordTrace]
  refine ⟨60272064189234988002949063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80362752252313317337265417 60272064189234988002949063)
  ·
    refine ⟨90408096283852482004423595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60272064189234988002949063 90408096283852482004423595)
    ·
      refine ⟨135612144425778723006635393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90408096283852482004423595 135612144425778723006635393)
      ·
        refine ⟨101709108319334042254976545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135612144425778723006635393 101709108319334042254976545)
        ·
          refine ⟨76281831239500531691232409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101709108319334042254976545 76281831239500531691232409)
          ·
            refine ⟨57211373429625398768424307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76281831239500531691232409 57211373429625398768424307)
            ·
              refine ⟨85817060144438098152636461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57211373429625398768424307 85817060144438098152636461)
              ·
                refine ⟨32181397554164286807238673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85817060144438098152636461 32181397554164286807238673)
                ·
                  refine ⟨24136048165623215105429005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32181397554164286807238673 24136048165623215105429005)
                  ·
                    refine ⟨9051018062108705664535877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24136048165623215105429005 9051018062108705664535877)
                    ·
                      refine ⟨1697065886645382312100477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9051018062108705664535877 1697065886645382312100477)
                      ·
                        rfl

theorem cell23_3305024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_3305024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305024 prefixEnd_3305024 := by exact prefixLift 3305024
  have htrace : WordTrace (prefixWord ++ tailWord_3305024) baseStart_3305024 baseEnd_3305024 := by
    simpa [prefixWord, tailWord_3305024, baseEnd_3305024] using wordTrace_append hprefix tailTrace_3305024
  have hstable : (prefixWord ++ tailWord_3305024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305024).length < 2 ^ (prefixWord ++ tailWord_3305024).sum := by decide
  have hdescent : baseEnd_3305024 < baseStart_3305024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305034 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_3305034 : Nat := 118140960795 + 3305034 * 2 ^ 59
def prefixEnd_3305034 : Nat := 4983230072969 + 3 ^ 40 * 3305034 * 2
def baseEnd_3305034 : Nat := 565690340483975757658477

theorem tailTrace_3305034 : CollatzResearch.WordTrace tailWord_3305034 prefixEnd_3305034 565690340483975757658477 := by
  unfold tailWord_3305034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30136123277108436928440539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80362995405622498475841437 30136123277108436928440539)
  ·
    refine ⟨45204184915662655392660809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30136123277108436928440539 45204184915662655392660809)
    ·
      refine ⟨33903138686746991544495607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45204184915662655392660809 33903138686746991544495607)
      ·
        refine ⟨50854708030120487316743411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33903138686746991544495607 50854708030120487316743411)
        ·
          refine ⟨76282062045180730975115117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50854708030120487316743411 76282062045180730975115117)
          ·
            refine ⟨28605773266942774115668169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76282062045180730975115117 28605773266942774115668169)
            ·
              refine ⟨21454329950207080586751127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28605773266942774115668169 21454329950207080586751127)
              ·
                refine ⟨32181494925310620880126691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21454329950207080586751127 32181494925310620880126691)
                ·
                  refine ⟨48272242387965931320190037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32181494925310620880126691 48272242387965931320190037)
                  ·
                    refine ⟨565690340483975757658477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48272242387965931320190037 565690340483975757658477)
                    ·
                      rfl

theorem cell23_3305034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_3305034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305034 prefixEnd_3305034 := by exact prefixLift 3305034
  have htrace : WordTrace (prefixWord ++ tailWord_3305034) baseStart_3305034 baseEnd_3305034 := by
    simpa [prefixWord, tailWord_3305034, baseEnd_3305034] using wordTrace_append hprefix tailTrace_3305034
  have hstable : (prefixWord ++ tailWord_3305034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305034).length < 2 ^ (prefixWord ++ tailWord_3305034).sum := by decide
  have hdescent : baseEnd_3305034 < baseStart_3305034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305061 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3305061 : Nat := 118140960795 + 3305061 * 2 ^ 59
def prefixEnd_3305061 : Nat := 4983230072969 + 3 ^ 40 * 3305061 * 2
def baseEnd_3305061 : Nat := 1697084885429598667337807

theorem tailTrace_3305061 : CollatzResearch.WordTrace tailWord_3305061 prefixEnd_3305061 1697084885429598667337807 := by
  unfold tailWord_3305061
  simp only [CollatzResearch.WordTrace]
  refine ⟨120545477879335931324995037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80363651919557287549996691 120545477879335931324995037)
  ·
    refine ⟨45204554204750974246873139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120545477879335931324995037 45204554204750974246873139)
    ·
      refine ⟨67806831307126461370309709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45204554204750974246873139 67806831307126461370309709)
      ·
        refine ⟨25427561740172423013866141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67806831307126461370309709 25427561740172423013866141)
        ·
          refine ⟨9535335652564658630199803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25427561740172423013866141 9535335652564658630199803)
          ·
            refine ⟨14303003478846987945299705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535335652564658630199803 14303003478846987945299705)
            ·
              refine ⟨10727252609135240958974779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14303003478846987945299705 10727252609135240958974779)
              ·
                refine ⟨16090878913702861438462169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10727252609135240958974779 16090878913702861438462169)
                ·
                  refine ⟨12068159185277146078846627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16090878913702861438462169 12068159185277146078846627)
                  ·
                    refine ⟨18102238777915719118269941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12068159185277146078846627 18102238777915719118269941)
                    ·
                      refine ⟨1697084885429598667337807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18102238777915719118269941 1697084885429598667337807)
                      ·
                        rfl

theorem cell23_3305061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3305061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305061 prefixEnd_3305061 := by exact prefixLift 3305061
  have htrace : WordTrace (prefixWord ++ tailWord_3305061) baseStart_3305061 baseEnd_3305061 := by
    simpa [prefixWord, tailWord_3305061, baseEnd_3305061] using wordTrace_append hprefix tailTrace_3305061
  have hstable : (prefixWord ++ tailWord_3305061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305061).length < 2 ^ (prefixWord ++ tailWord_3305061).sum := by decide
  have hdescent : baseEnd_3305061 < baseStart_3305061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305078 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3305078 : Nat := 118140960795 + 3305078 * 2 ^ 59
def prefixEnd_3305078 : Nat := 4983230072969 + 3 ^ 40 * 3305078 * 2
def baseEnd_3305078 : Nat := 1697093614600725100825229

theorem tailTrace_3305078 : CollatzResearch.WordTrace tailWord_3305078 prefixEnd_3305078 1697093614600725100825229 := by
  unfold tailWord_3305078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534131120017146451772743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80364065280182895485575925 7534131120017146451772743)
  ·
    refine ⟨11301196680025719677659115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7534131120017146451772743 11301196680025719677659115)
    ·
      refine ⟨16951795020038579516488673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11301196680025719677659115 16951795020038579516488673)
      ·
        refine ⟨12713846265028934637366505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16951795020038579516488673 12713846265028934637366505)
        ·
          refine ⟨9535384698771700978024879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12713846265028934637366505 9535384698771700978024879)
          ·
            refine ⟨14303077048157551467037319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535384698771700978024879 14303077048157551467037319)
            ·
              refine ⟨21454615572236327200555979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14303077048157551467037319 21454615572236327200555979)
              ·
                refine ⟨32181923358354490800833969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21454615572236327200555979 32181923358354490800833969)
                ·
                  refine ⟨24136442518765868100625477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32181923358354490800833969 24136442518765868100625477)
                  ·
                    refine ⟨4525582972268600268867277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24136442518765868100625477 4525582972268600268867277)
                    ·
                      refine ⟨1697093614600725100825229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525582972268600268867277 1697093614600725100825229)
                      ·
                        rfl

theorem cell23_3305078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3305078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305078 prefixEnd_3305078 := by exact prefixLift 3305078
  have htrace : WordTrace (prefixWord ++ tailWord_3305078) baseStart_3305078 baseEnd_3305078 := by
    simpa [prefixWord, tailWord_3305078, baseEnd_3305078] using wordTrace_append hprefix tailTrace_3305078
  have hstable : (prefixWord ++ tailWord_3305078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305078).length < 2 ^ (prefixWord ++ tailWord_3305078).sum := by decide
  have hdescent : baseEnd_3305078 < baseStart_3305078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305084 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3305084 : Nat := 118140960795 + 3305084 * 2 ^ 59
def prefixEnd_3305084 : Nat := 4983230072969 + 3 ^ 40 * 3305084 * 2
def baseEnd_3305084 : Nat := 1697096695484652077350201

theorem tailTrace_3305084 : CollatzResearch.WordTrace tailWord_3305084 prefixEnd_3305084 1697096695484652077350201 := by
  unfold tailWord_3305084
  simp only [CollatzResearch.WordTrace]
  refine ⟨60273158379126303126541153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80364211172168404168721537 60273158379126303126541153)
  ·
    refine ⟨45204868784344727344905865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60273158379126303126541153 45204868784344727344905865)
    ·
      refine ⟨33903651588258545508679399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45204868784344727344905865 33903651588258545508679399)
      ·
        refine ⟨50855477382387818263019099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33903651588258545508679399 50855477382387818263019099)
        ·
          refine ⟨76283216073581727394528649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50855477382387818263019099 76283216073581727394528649)
          ·
            refine ⟨57212412055186295545896487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76283216073581727394528649 57212412055186295545896487)
            ·
              refine ⟨85818618082779443318844731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57212412055186295545896487 85818618082779443318844731)
              ·
                refine ⟨128727927124169164978267097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85818618082779443318844731 128727927124169164978267097)
                ·
                  refine ⟨96545945343126873733700323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128727927124169164978267097 96545945343126873733700323)
                  ·
                    refine ⟨144818918014690310600550485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96545945343126873733700323 144818918014690310600550485)
                    ·
                      refine ⟨1697096695484652077350201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 144818918014690310600550485 1697096695484652077350201)
                      ·
                        rfl

theorem cell23_3305084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3305084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305084 prefixEnd_3305084 := by exact prefixLift 3305084
  have htrace : WordTrace (prefixWord ++ tailWord_3305084) baseStart_3305084 baseEnd_3305084 := by
    simpa [prefixWord, tailWord_3305084, baseEnd_3305084] using wordTrace_append hprefix tailTrace_3305084
  have hstable : (prefixWord ++ tailWord_3305084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305084).length < 2 ^ (prefixWord ++ tailWord_3305084).sum := by decide
  have hdescent : baseEnd_3305084 < baseStart_3305084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305104 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_3305104 : Nat := 118140960795 + 3305104 * 2 ^ 59
def prefixEnd_3305104 : Nat := 4983230072969 + 3 ^ 40 * 3305104 * 2
def baseEnd_3305104 : Nat := 1697106965097741999100109

theorem tailTrace_3305104 : CollatzResearch.WordTrace tailWord_3305104 prefixEnd_3305104 1697106965097741999100109 := by
  unfold tailWord_3305104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60273523109090074834405183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80364697478786766445873577 60273523109090074834405183)
  ·
    refine ⟨90410284663635112251607775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60273523109090074834405183 90410284663635112251607775)
    ·
      refine ⟨135615426995452668377411663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90410284663635112251607775 135615426995452668377411663)
      ·
        refine ⟨203423140493179002566117495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135615426995452668377411663 203423140493179002566117495)
        ·
          refine ⟨305134710739768503849176243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203423140493179002566117495 305134710739768503849176243)
          ·
            refine ⟨457702066109652755773764365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305134710739768503849176243 457702066109652755773764365)
            ·
              refine ⟨171638274791119783415161637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457702066109652755773764365 171638274791119783415161637)
              ·
                refine ⟨32182176523334959390342807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171638274791119783415161637 32182176523334959390342807)
                ·
                  refine ⟨48273264785002439085514211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32182176523334959390342807 48273264785002439085514211)
                  ·
                    refine ⟨72409897177503658628271317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48273264785002439085514211 72409897177503658628271317)
                    ·
                      refine ⟨1697106965097741999100109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72409897177503658628271317 1697106965097741999100109)
                      ·
                        rfl

theorem cell23_3305104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_3305104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305104 prefixEnd_3305104 := by exact prefixLift 3305104
  have htrace : WordTrace (prefixWord ++ tailWord_3305104) baseStart_3305104 baseEnd_3305104 := by
    simpa [prefixWord, tailWord_3305104, baseEnd_3305104] using wordTrace_append hprefix tailTrace_3305104
  have hstable : (prefixWord ++ tailWord_3305104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305104).length < 2 ^ (prefixWord ++ tailWord_3305104).sum := by decide
  have hdescent : baseEnd_3305104 < baseStart_3305104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305111 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 1, 7]
def baseStart_3305111 : Nat := 118140960795 + 3305111 * 2 ^ 59
def prefixEnd_3305111 : Nat := 4983230072969 + 3 ^ 40 * 3305111 * 2
def baseEnd_3305111 : Nat := 565703519820774490570859

theorem tailTrace_3305111 : CollatzResearch.WordTrace tailWord_3305111 prefixEnd_3305111 565703519820774490570859 := by
  unfold tailWord_3305111
  simp only [CollatzResearch.WordTrace]
  refine ⟨120547301529154789864315187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80364867686103193242876791 120547301529154789864315187)
  ·
    refine ⟨180820952293732184796472781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120547301529154789864315187 180820952293732184796472781)
    ·
      refine ⟨67807857110149569298677293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180820952293732184796472781 67807857110149569298677293)
      ·
        refine ⟨25427946416306088487003985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67807857110149569298677293 25427946416306088487003985)
        ·
          refine ⟨19070959812229566365252989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25427946416306088487003985 19070959812229566365252989)
          ·
            refine ⟨7151609929586087386969871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19070959812229566365252989 7151609929586087386969871)
            ·
              refine ⟨10727414894379131080454807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151609929586087386969871 10727414894379131080454807)
              ·
                refine ⟨16091122341568696620682211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10727414894379131080454807 16091122341568696620682211)
                ·
                  refine ⟨24136683512353044931023317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16091122341568696620682211 24136683512353044931023317)
                  ·
                    refine ⟨565703519820774490570859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24136683512353044931023317 565703519820774490570859)
                    ·
                      rfl

theorem cell23_3305111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_3305111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305111 prefixEnd_3305111 := by exact prefixLift 3305111
  have htrace : WordTrace (prefixWord ++ tailWord_3305111) baseStart_3305111 baseEnd_3305111 := by
    simpa [prefixWord, tailWord_3305111, baseEnd_3305111] using wordTrace_append hprefix tailTrace_3305111
  have hstable : (prefixWord ++ tailWord_3305111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305111).length < 2 ^ (prefixWord ++ tailWord_3305111).sum := by decide
  have hdescent : baseEnd_3305111 < baseStart_3305111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305151 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 3]
def baseStart_3305151 : Nat := 118140960795 + 3305151 * 2 ^ 59
def prefixEnd_3305151 : Nat := 4983230072969 + 3 ^ 40 * 3305151 * 2
def baseEnd_3305151 : Nat := 1697131098688503315212393

theorem tailTrace_3305151 : CollatzResearch.WordTrace tailWord_3305151 prefixEnd_3305151 1697131098688503315212393 := by
  unfold tailWord_3305151
  simp only [CollatzResearch.WordTrace]
  refine ⟨120548760449009876695771307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80365840299339917797180871 120548760449009876695771307)
  ·
    refine ⟨180823140673514815043656961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120548760449009876695771307 180823140673514815043656961)
    ·
      refine ⟨135617355505136111282742721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180823140673514815043656961 135617355505136111282742721)
      ·
        refine ⟨101713016628852083462057041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135617355505136111282742721 101713016628852083462057041)
        ·
          refine ⟨76284762471639062596542781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101713016628852083462057041 76284762471639062596542781)
          ·
            refine ⟨28606785926864648473703543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76284762471639062596542781 28606785926864648473703543)
            ·
              refine ⟨42910178890296972710555315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28606785926864648473703543 42910178890296972710555315)
              ·
                refine ⟨64365268335445459065832973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42910178890296972710555315 64365268335445459065832973)
                ·
                  refine ⟨24136975625792047149687365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64365268335445459065832973 24136975625792047149687365)
                  ·
                    refine ⟨4525682929836008840566381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24136975625792047149687365 4525682929836008840566381)
                    ·
                      refine ⟨1697131098688503315212393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525682929836008840566381 1697131098688503315212393)
                      ·
                        rfl

theorem cell23_3305151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_3305151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305151 prefixEnd_3305151 := by exact prefixLift 3305151
  have htrace : WordTrace (prefixWord ++ tailWord_3305151) baseStart_3305151 baseEnd_3305151 := by
    simpa [prefixWord, tailWord_3305151, baseEnd_3305151] using wordTrace_append hprefix tailTrace_3305151
  have hstable : (prefixWord ++ tailWord_3305151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305151).length < 2 ^ (prefixWord ++ tailWord_3305151).sum := by decide
  have hdescent : baseEnd_3305151 < baseStart_3305151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305165 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3305165 : Nat := 118140960795 + 3305165 * 2 ^ 59
def prefixEnd_3305165 : Nat := 4983230072969 + 3 ^ 40 * 3305165 * 2
def baseEnd_3305165 : Nat := 1697138287417666260437329

theorem tailTrace_3305165 : CollatzResearch.WordTrace tailWord_3305165 prefixEnd_3305165 1697138287417666260437329 := by
  unfold tailWord_3305165
  simp only [CollatzResearch.WordTrace]
  refine ⟨120549271070959157086780949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80366180713972771391187299 120549271070959157086780949)
  ·
    refine ⟨5650747081451210488442857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120549271070959157086780949 5650747081451210488442857)
    ·
      refine ⟨4238060311088407866332143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5650747081451210488442857 4238060311088407866332143)
      ·
        refine ⟨6357090466632611799498215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238060311088407866332143 6357090466632611799498215)
        ·
          refine ⟨9535635699948917699247323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357090466632611799498215 9535635699948917699247323)
          ·
            refine ⟨14303453549923376548870985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535635699948917699247323 14303453549923376548870985)
            ·
              refine ⟨10727590162442532411653239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14303453549923376548870985 10727590162442532411653239)
              ·
                refine ⟨16091385243663798617479859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10727590162442532411653239 16091385243663798617479859)
                ·
                  refine ⟨24137077865495697926219789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16091385243663798617479859 24137077865495697926219789)
                  ·
                    refine ⟨9051404199560886722332421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24137077865495697926219789 9051404199560886722332421)
                    ·
                      refine ⟨1697138287417666260437329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9051404199560886722332421 1697138287417666260437329)
                      ·
                        rfl

theorem cell23_3305165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3305165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305165 prefixEnd_3305165 := by exact prefixLift 3305165
  have htrace : WordTrace (prefixWord ++ tailWord_3305165) baseStart_3305165 baseEnd_3305165 := by
    simpa [prefixWord, tailWord_3305165, baseEnd_3305165] using wordTrace_append hprefix tailTrace_3305165
  have hstable : (prefixWord ++ tailWord_3305165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305165).length < 2 ^ (prefixWord ++ tailWord_3305165).sum := by decide
  have hdescent : baseEnd_3305165 < baseStart_3305165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305185 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_3305185 : Nat := 118140960795 + 3305185 * 2 ^ 59
def prefixEnd_3305185 : Nat := 4983230072969 + 3 ^ 40 * 3305185 * 2
def baseEnd_3305185 : Nat := 1697148557030756182187237

theorem tailTrace_3305185 : CollatzResearch.WordTrace tailWord_3305185 prefixEnd_3305185 1697148557030756182187237 := by
  unfold tailWord_3305185
  simp only [CollatzResearch.WordTrace]
  refine ⟨120550000530886700502509009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80366667020591133668339339 120550000530886700502509009)
  ·
    refine ⟨90412500398165025376881757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120550000530886700502509009 90412500398165025376881757)
    ·
      refine ⟨33904687649311884516330659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90412500398165025376881757 33904687649311884516330659)
      ·
        refine ⟨50857031473967826774495989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33904687649311884516330659 50857031473967826774495989)
        ·
          refine ⟨4767846700684483760108999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50857031473967826774495989 4767846700684483760108999)
          ·
            refine ⟨7151770051026725640163499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767846700684483760108999 7151770051026725640163499)
            ·
              refine ⟨10727655076540088460245249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151770051026725640163499 10727655076540088460245249)
              ·
                refine ⟨8045741307405066345183937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10727655076540088460245249 8045741307405066345183937)
                ·
                  refine ⟨6034305980553799758887953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045741307405066345183937 6034305980553799758887953)
                  ·
                    refine ⟨4525729485415349819165965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6034305980553799758887953 4525729485415349819165965)
                    ·
                      refine ⟨1697148557030756182187237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525729485415349819165965 1697148557030756182187237)
                      ·
                        rfl

theorem cell23_3305185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_3305185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305185 prefixEnd_3305185 := by exact prefixLift 3305185
  have htrace : WordTrace (prefixWord ++ tailWord_3305185) baseStart_3305185 baseEnd_3305185 := by
    simpa [prefixWord, tailWord_3305185, baseEnd_3305185] using wordTrace_append hprefix tailTrace_3305185
  have hstable : (prefixWord ++ tailWord_3305185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305185).length < 2 ^ (prefixWord ++ tailWord_3305185).sum := by decide
  have hdescent : baseEnd_3305185 < baseStart_3305185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305208 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 1, 5, 2]
def baseStart_3305208 : Nat := 118140960795 + 3305208 * 2 ^ 59
def prefixEnd_3305208 : Nat := 4983230072969 + 3 ^ 40 * 3305208 * 2
def baseEnd_3305208 : Nat := 1697160367085809592199631

theorem tailTrace_3305208 : CollatzResearch.WordTrace tailWord_3305208 prefixEnd_3305208 1697160367085809592199631 := by
  unfold tailWord_3305208
  simp only [CollatzResearch.WordTrace]
  refine ⟨60275419704901687715298139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80367226273202250287064185 60275419704901687715298139)
  ·
    refine ⟨90413129557352531572947209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60275419704901687715298139 90413129557352531572947209)
    ·
      refine ⟨67809847168014398679710407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90413129557352531572947209 67809847168014398679710407)
      ·
        refine ⟨101714770752021598019565611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67809847168014398679710407 101714770752021598019565611)
        ·
          refine ⟨152572156128032397029348417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101714770752021598019565611 152572156128032397029348417)
          ·
            refine ⟨114429117096024297772011313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152572156128032397029348417 114429117096024297772011313)
            ·
              refine ⟨85821837822018223329008485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114429117096024297772011313 85821837822018223329008485)
              ·
                refine ⟨16091594591628416874189091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85821837822018223329008485 16091594591628416874189091)
                ·
                  refine ⟨24137391887442625311283637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16091594591628416874189091 24137391887442625311283637)
                  ·
                    refine ⟨2262880489447746122932841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24137391887442625311283637 2262880489447746122932841)
                    ·
                      refine ⟨1697160367085809592199631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2262880489447746122932841 1697160367085809592199631)
                      ·
                        rfl

theorem cell23_3305208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_3305208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305208 prefixEnd_3305208 := by exact prefixLift 3305208
  have htrace : WordTrace (prefixWord ++ tailWord_3305208) baseStart_3305208 baseEnd_3305208 := by
    simpa [prefixWord, tailWord_3305208, baseEnd_3305208] using wordTrace_append hprefix tailTrace_3305208
  have hstable : (prefixWord ++ tailWord_3305208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305208).length < 2 ^ (prefixWord ++ tailWord_3305208).sum := by decide
  have hdescent : baseEnd_3305208 < baseStart_3305208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305249 : List Nat := [1, 2, 3, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_3305249 : Nat := 118140960795 + 3305249 * 2 ^ 59
def prefixEnd_3305249 : Nat := 4983230072969 + 3 ^ 40 * 3305249 * 2
def baseEnd_3305249 : Nat := 1697181419792643931786943

theorem tailTrace_3305249 : CollatzResearch.WordTrace tailWord_3305249 prefixEnd_3305249 1697181419792643931786943 := by
  unfold tailWord_3305249
  simp only [CollatzResearch.WordTrace]
  refine ⟨120552334802654839432838801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80368223201769892955225867 120552334802654839432838801)
  ·
    refine ⟨90414251101991129574629101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120552334802654839432838801 90414251101991129574629101)
    ·
      refine ⟨33905344163246673590485913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90414251101991129574629101 33905344163246673590485913)
      ·
        refine ⟨25429008122435005192864435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33905344163246673590485913 25429008122435005192864435)
        ·
          refine ⟨38143512183652507789296653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25429008122435005192864435 38143512183652507789296653)
          ·
            refine ⟨14303817068869690420986245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38143512183652507789296653 14303817068869690420986245)
            ·
              refine ⟨2681965700413066953934921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14303817068869690420986245 2681965700413066953934921)
              ·
                refine ⟨2011474275309800215451191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2681965700413066953934921 2011474275309800215451191)
                ·
                  refine ⟨3017211412964700323176787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011474275309800215451191 3017211412964700323176787)
                  ·
                    refine ⟨4525817119447050484765181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017211412964700323176787 4525817119447050484765181)
                    ·
                      refine ⟨1697181419792643931786943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525817119447050484765181 1697181419792643931786943)
                      ·
                        rfl

theorem cell23_3305249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_3305249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305249 prefixEnd_3305249 := by exact prefixLift 3305249
  have htrace : WordTrace (prefixWord ++ tailWord_3305249) baseStart_3305249 baseEnd_3305249 := by
    simpa [prefixWord, tailWord_3305249, baseEnd_3305249] using wordTrace_append hprefix tailTrace_3305249
  have hstable : (prefixWord ++ tailWord_3305249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305249).length < 2 ^ (prefixWord ++ tailWord_3305249).sum := by decide
  have hdescent : baseEnd_3305249 < baseStart_3305249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305251 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3305251 : Nat := 118140960795 + 3305251 * 2 ^ 59
def prefixEnd_3305251 : Nat := 4983230072969 + 3 ^ 40 * 3305251 * 2
def baseEnd_3305251 : Nat := 1697182446753952923961933

theorem tailTrace_3305251 : CollatzResearch.WordTrace tailWord_3305251 prefixEnd_3305251 1697182446753952923961933 := by
  unfold tailWord_3305251
  simp only [CollatzResearch.WordTrace]
  refine ⟨120552407748647593774411607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80368271832431729182941071 120552407748647593774411607)
  ·
    refine ⟨180828611622971390661617411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120552407748647593774411607 180828611622971390661617411)
    ·
      refine ⟨271242917434457085992426117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180828611622971390661617411 271242917434457085992426117)
      ·
        refine ⟨50858047018960703623579897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271242917434457085992426117 50858047018960703623579897)
        ·
          refine ⟨38143535264220527717684923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50858047018960703623579897 38143535264220527717684923)
          ·
            refine ⟨57215302896330791576527385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38143535264220527717684923 57215302896330791576527385)
            ·
              refine ⟨42911477172248093682395539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57215302896330791576527385 42911477172248093682395539)
              ·
                refine ⟨64367215758372140523593309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42911477172248093682395539 64367215758372140523593309)
                ·
                  refine ⟨24137705909389552696347491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64367215758372140523593309 24137705909389552696347491)
                  ·
                    refine ⟨36206558864084329044521237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24137705909389552696347491 36206558864084329044521237)
                    ·
                      refine ⟨1697182446753952923961933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36206558864084329044521237 1697182446753952923961933)
                      ·
                        rfl

theorem cell23_3305251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3305251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305251 prefixEnd_3305251 := by exact prefixLift 3305251
  have htrace : WordTrace (prefixWord ++ tailWord_3305251) baseStart_3305251 baseEnd_3305251 := by
    simpa [prefixWord, tailWord_3305251, baseEnd_3305251] using wordTrace_append hprefix tailTrace_3305251
  have hstable : (prefixWord ++ tailWord_3305251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305251).length < 2 ^ (prefixWord ++ tailWord_3305251).sum := by decide
  have hdescent : baseEnd_3305251 < baseStart_3305251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305265 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 2, 4]
def baseStart_3305265 : Nat := 118140960795 + 3305265 * 2 ^ 59
def prefixEnd_3305265 : Nat := 4983230072969 + 3 ^ 40 * 3305265 * 2
def baseEnd_3305265 : Nat := 565729878494371956395623

theorem tailTrace_3305265 : CollatzResearch.WordTrace tailWord_3305265 prefixEnd_3305265 565729878494371956395623 := by
  unfold tailWord_3305265
  simp only [CollatzResearch.WordTrace]
  refine ⟨120552918370596874165421249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80368612247064582776947499 120552918370596874165421249)
  ·
    refine ⟨90414688777947655624065937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120552918370596874165421249 90414688777947655624065937)
    ·
      refine ⟨67811016583460741718049453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90414688777947655624065937 67811016583460741718049453)
      ·
        refine ⟨25429131218797778144268545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67811016583460741718049453 25429131218797778144268545)
        ·
          refine ⟨19071848414098333608201409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25429131218797778144268545 19071848414098333608201409)
          ·
            refine ⟨14303886310573750206151057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19071848414098333608201409 14303886310573750206151057)
            ·
              refine ⟨10727914732930312654613293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14303886310573750206151057 10727914732930312654613293)
              ·
                refine ⟨4022968024848867245479985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10727914732930312654613293 4022968024848867245479985)
                ·
                  refine ⟨3017226018636650434109989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022968024848867245479985 3017226018636650434109989)
                  ·
                    refine ⟨565729878494371956395623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017226018636650434109989 565729878494371956395623)
                    ·
                      rfl

theorem cell23_3305265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_3305265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305265 prefixEnd_3305265 := by exact prefixLift 3305265
  have htrace : WordTrace (prefixWord ++ tailWord_3305265) baseStart_3305265 baseEnd_3305265 := by
    simpa [prefixWord, tailWord_3305265, baseEnd_3305265] using wordTrace_append hprefix tailTrace_3305265
  have hstable : (prefixWord ++ tailWord_3305265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305265).length < 2 ^ (prefixWord ++ tailWord_3305265).sum := by decide
  have hdescent : baseEnd_3305265 < baseStart_3305265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305272 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 3, 2, 2]
def baseStart_3305272 : Nat := 118140960795 + 3305272 * 2 ^ 59
def prefixEnd_3305272 : Nat := 4983230072969 + 3 ^ 40 * 3305272 * 2
def baseEnd_3305272 : Nat := 1697193229847697341799337

theorem tailTrace_3305272 : CollatzResearch.WordTrace tailWord_3305272 prefixEnd_3305272 1697193229847697341799337 := by
  unfold tailWord_3305272
  simp only [CollatzResearch.WordTrace]
  refine ⟨60276586840785757180463035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80368782454381009573950713 60276586840785757180463035)
  ·
    refine ⟨90414880261178635770694553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60276586840785757180463035 90414880261178635770694553)
    ·
      refine ⟨67811160195883976828020915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90414880261178635770694553 67811160195883976828020915)
      ·
        refine ⟨101716740293825965242031373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67811160195883976828020915 101716740293825965242031373)
        ·
          refine ⟨38143777610184736965761765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101716740293825965242031373 38143777610184736965761765)
          ·
            refine ⟨7151958301909638181080331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38143777610184736965761765 7151958301909638181080331)
            ·
              refine ⟨10727937452864457271620497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151958301909638181080331 10727937452864457271620497)
              ·
                refine ⟨8045953089648342953715373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10727937452864457271620497 8045953089648342953715373)
                ·
                  refine ⟨3017232408618128607643265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8045953089648342953715373 3017232408618128607643265)
                  ·
                    refine ⟨2262924306463596455732449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3017232408618128607643265 2262924306463596455732449)
                    ·
                      refine ⟨1697193229847697341799337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2262924306463596455732449 1697193229847697341799337)
                      ·
                        rfl

theorem cell23_3305272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_3305272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305272 prefixEnd_3305272 := by exact prefixLift 3305272
  have htrace : WordTrace (prefixWord ++ tailWord_3305272) baseStart_3305272 baseEnd_3305272 := by
    simpa [prefixWord, tailWord_3305272, baseEnd_3305272] using wordTrace_append hprefix tailTrace_3305272
  have hstable : (prefixWord ++ tailWord_3305272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305272).length < 2 ^ (prefixWord ++ tailWord_3305272).sum := by decide
  have hdescent : baseEnd_3305272 < baseStart_3305272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305286 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3305286 : Nat := 118140960795 + 3305286 * 2 ^ 59
def prefixEnd_3305286 : Nat := 4983230072969 + 3 ^ 40 * 3305286 * 2
def baseEnd_3305286 : Nat := 565733472858953429008091

theorem tailTrace_3305286 : CollatzResearch.WordTrace tailWord_3305286 prefixEnd_3305286 565733472858953429008091 := by
  unfold tailWord_3305286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767302634485024835997991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80369122869013863167957141 3767302634485024835997991)
  ·
    refine ⟨5650953951727537253996987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3767302634485024835997991 5650953951727537253996987)
    ·
      refine ⟨8476430927591305880995481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650953951727537253996987 8476430927591305880995481)
      ·
        refine ⟨6357323195693479410746611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8476430927591305880995481 6357323195693479410746611)
        ·
          refine ⟨9535984793540219116119917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357323195693479410746611 9535984793540219116119917)
          ·
            refine ⟨3575994297577582168544969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9535984793540219116119917 3575994297577582168544969)
            ·
              refine ⟨2681995723183186626408727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575994297577582168544969 2681995723183186626408727)
              ·
                refine ⟨4022993584774779939613091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681995723183186626408727 4022993584774779939613091)
                ·
                  refine ⟨6034490377162169909419637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022993584774779939613091 6034490377162169909419637)
                  ·
                    refine ⟨565733472858953429008091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6034490377162169909419637 565733472858953429008091)
                    ·
                      rfl

theorem cell23_3305286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3305286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305286 prefixEnd_3305286 := by exact prefixLift 3305286
  have htrace : WordTrace (prefixWord ++ tailWord_3305286) baseStart_3305286 baseEnd_3305286 := by
    simpa [prefixWord, tailWord_3305286, baseEnd_3305286] using wordTrace_append hprefix tailTrace_3305286
  have hstable : (prefixWord ++ tailWord_3305286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305286).length < 2 ^ (prefixWord ++ tailWord_3305286).sum := by decide
  have hdescent : baseEnd_3305286 < baseStart_3305286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305289 : List Nat := [1, 2, 1, 1, 2, 4, 4, 3, 1, 2, 2]
def baseStart_3305289 : Nat := 118140960795 + 3305289 * 2 ^ 59
def prefixEnd_3305289 : Nat := 4983230072969 + 3 ^ 40 * 3305289 * 2
def baseEnd_3305289 : Nat := 1697201959018823775286759

theorem tailTrace_3305289 : CollatzResearch.WordTrace tailWord_3305289 prefixEnd_3305289 1697201959018823775286759 := by
  unfold tailWord_3305289
  simp only [CollatzResearch.WordTrace]
  refine ⟨120553793722509926264294921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80369195815006617509529947 120553793722509926264294921)
  ·
    refine ⟨90415345291882444698221191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120553793722509926264294921 90415345291882444698221191)
    ·
      refine ⟨135623017937823667047331787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90415345291882444698221191 135623017937823667047331787)
      ·
        refine ⟨203434526906735500570997681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135623017937823667047331787 203434526906735500570997681)
        ·
          refine ⟨152575895180051625428248261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203434526906735500570997681 152575895180051625428248261)
          ·
            refine ⟨28607980346259679767796549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152575895180051625428248261 28607980346259679767796549)
            ·
              refine ⟨5363996314923689956461853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28607980346259679767796549 5363996314923689956461853)
              ·
                refine ⟨2011498618096383733673195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5363996314923689956461853 2011498618096383733673195)
                ·
                  refine ⟨3017247927144575600509793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011498618096383733673195 3017247927144575600509793)
                  ·
                    refine ⟨2262935945358431700382345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3017247927144575600509793 2262935945358431700382345)
                    ·
                      refine ⟨1697201959018823775286759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2262935945358431700382345 1697201959018823775286759)
                      ·
                        rfl

theorem cell23_3305289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 2, 2].length) (baseStart_3305289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305289 prefixEnd_3305289 := by exact prefixLift 3305289
  have htrace : WordTrace (prefixWord ++ tailWord_3305289) baseStart_3305289 baseEnd_3305289 := by
    simpa [prefixWord, tailWord_3305289, baseEnd_3305289] using wordTrace_append hprefix tailTrace_3305289
  have hstable : (prefixWord ++ tailWord_3305289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305289).length < 2 ^ (prefixWord ++ tailWord_3305289).sum := by decide
  have hdescent : baseEnd_3305289 < baseStart_3305289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305292 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3305292 : Nat := 118140960795 + 3305292 * 2 ^ 59
def prefixEnd_3305292 : Nat := 4983230072969 + 3 ^ 40 * 3305292 * 2
def baseEnd_3305292 : Nat := 1697203499460787263549245

theorem tailTrace_3305292 : CollatzResearch.WordTrace tailWord_3305292 prefixEnd_3305292 1697203499460787263549245 := by
  unfold tailWord_3305292
  simp only [CollatzResearch.WordTrace]
  refine ⟨60276951570749528888327065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80369268760999371851102753 60276951570749528888327065)
  ·
    refine ⟨45207713678062146666245299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60276951570749528888327065 45207713678062146666245299)
    ·
      refine ⟨67811570517093219999367949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45207713678062146666245299 67811570517093219999367949)
      ·
        refine ⟨25429338943909957499762981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67811570517093219999367949 25429338943909957499762981)
        ·
          refine ⟨4768001051983117031205559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25429338943909957499762981 4768001051983117031205559)
          ·
            refine ⟨7152001577974675546808339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768001051983117031205559 7152001577974675546808339)
            ·
              refine ⟨10728002366962013320212509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152001577974675546808339 10728002366962013320212509)
              ·
                refine ⟨4023000887610754995079691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10728002366962013320212509 4023000887610754995079691)
                ·
                  refine ⟨6034501331416132492619537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023000887610754995079691 6034501331416132492619537)
                  ·
                    refine ⟨4525875998562099369464653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6034501331416132492619537 4525875998562099369464653)
                    ·
                      refine ⟨1697203499460787263549245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525875998562099369464653 1697203499460787263549245)
                      ·
                        rfl

theorem cell23_3305292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3305292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305292 prefixEnd_3305292 := by exact prefixLift 3305292
  have htrace : WordTrace (prefixWord ++ tailWord_3305292) baseStart_3305292 baseEnd_3305292 := by
    simpa [prefixWord, tailWord_3305292, baseEnd_3305292] using wordTrace_append hprefix tailTrace_3305292
  have hstable : (prefixWord ++ tailWord_3305292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305292).length < 2 ^ (prefixWord ++ tailWord_3305292).sum := by decide
  have hdescent : baseEnd_3305292 < baseStart_3305292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305305 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 3]
def baseStart_3305305 : Nat := 118140960795 + 3305305 * 2 ^ 59
def prefixEnd_3305305 : Nat := 4983230072969 + 3 ^ 40 * 3305305 * 2
def baseEnd_3305305 : Nat := 1697210174709295712686685

theorem tailTrace_3305305 : CollatzResearch.WordTrace tailWord_3305305 prefixEnd_3305305 1697210174709295712686685 := by
  unfold tailWord_3305305
  simp only [CollatzResearch.WordTrace]
  refine ⟨120554377290451960996877369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80369584860301307331251579 120554377290451960996877369)
  ·
    refine ⟨90415782967838970747658027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120554377290451960996877369 90415782967838970747658027)
    ·
      refine ⟨135623674451758456121487041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90415782967838970747658027 135623674451758456121487041)
      ·
        refine ⟨101717755838818842091115281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135623674451758456121487041 101717755838818842091115281)
        ·
          refine ⟨76288316879114131568336461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101717755838818842091115281 76288316879114131568336461)
          ·
            refine ⟨28608118829667799338126173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76288316879114131568336461 28608118829667799338126173)
            ·
              refine ⟨10728044561125424751797315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28608118829667799338126173 10728044561125424751797315)
              ·
                refine ⟨16092066841688137127695973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10728044561125424751797315 16092066841688137127695973)
                ·
                  refine ⟨3017262532816525711442995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16092066841688137127695973 3017262532816525711442995)
                  ·
                    refine ⟨4525893799224788567164493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017262532816525711442995 4525893799224788567164493)
                    ·
                      refine ⟨1697210174709295712686685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4525893799224788567164493 1697210174709295712686685)
                      ·
                        rfl

theorem cell23_3305305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_3305305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305305 prefixEnd_3305305 := by exact prefixLift 3305305
  have htrace : WordTrace (prefixWord ++ tailWord_3305305) baseStart_3305305 baseEnd_3305305 := by
    simpa [prefixWord, tailWord_3305305, baseEnd_3305305] using wordTrace_append hprefix tailTrace_3305305
  have hstable : (prefixWord ++ tailWord_3305305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305305).length < 2 ^ (prefixWord ++ tailWord_3305305).sum := by decide
  have hdescent : baseEnd_3305305 < baseStart_3305305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305348 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3305348 : Nat := 118140960795 + 3305348 * 2 ^ 59
def prefixEnd_3305348 : Nat := 4983230072969 + 3 ^ 40 * 3305348 * 2
def baseEnd_3305348 : Nat := 1697232254377439044448987

theorem tailTrace_3305348 : CollatzResearch.WordTrace tailWord_3305348 prefixEnd_3305348 1697232254377439044448987 := by
  unfold tailWord_3305348
  simp only [CollatzResearch.WordTrace]
  refine ⟨60277972814648089670346349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80370630419530786227128465 60277972814648089670346349)
  ·
    refine ⟨22604239805493033626379881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60277972814648089670346349 22604239805493033626379881)
    ·
      refine ⟨16953179854119775219784911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22604239805493033626379881 16953179854119775219784911)
      ·
        refine ⟨25429769781179662829677367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16953179854119775219784911 25429769781179662829677367)
        ·
          refine ⟨38144654671769494244516051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25429769781179662829677367 38144654671769494244516051)
          ·
            refine ⟨57216982007654241366774077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38144654671769494244516051 57216982007654241366774077)
            ·
              refine ⟨21456368252870340512540279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57216982007654241366774077 21456368252870340512540279)
              ·
                refine ⟨32184552379305510768810419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21456368252870340512540279 32184552379305510768810419)
                ·
                  refine ⟨48276828568958266153215629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32184552379305510768810419 48276828568958266153215629)
                  ·
                    refine ⟨18103810713359349807455861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48276828568958266153215629 18103810713359349807455861)
                    ·
                      refine ⟨1697232254377439044448987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18103810713359349807455861 1697232254377439044448987)
                      ·
                        rfl

theorem cell23_3305348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3305348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305348 prefixEnd_3305348 := by exact prefixLift 3305348
  have htrace : WordTrace (prefixWord ++ tailWord_3305348) baseStart_3305348 baseEnd_3305348 := by
    simpa [prefixWord, tailWord_3305348, baseEnd_3305348] using wordTrace_append hprefix tailTrace_3305348
  have hstable : (prefixWord ++ tailWord_3305348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305348).length < 2 ^ (prefixWord ++ tailWord_3305348).sum := by decide
  have hdescent : baseEnd_3305348 < baseStart_3305348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305396 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_3305396 : Nat := 118140960795 + 3305396 * 2 ^ 59
def prefixEnd_3305396 : Nat := 4983230072969 + 3 ^ 40 * 3305396 * 2
def baseEnd_3305396 : Nat := 1697256901448854856648767

theorem tailTrace_3305396 : CollatzResearch.WordTrace tailWord_3305396 prefixEnd_3305396 1697256901448854856648767 := by
  unfold tailWord_3305396
  simp only [CollatzResearch.WordTrace]
  refine ⟨60278848166561141769220021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80371797555414855692293361 60278848166561141769220021)
  ·
    refine ⟨5651142015615107040864377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60278848166561141769220021 5651142015615107040864377)
    ·
      refine ⟨4238356511711330280648283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5651142015615107040864377 4238356511711330280648283)
      ·
        refine ⟨6357534767566995420972425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238356511711330280648283 6357534767566995420972425)
        ·
          refine ⟨4768151075675246565729319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6357534767566995420972425 4768151075675246565729319)
          ·
            refine ⟨7152226613512869848593979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768151075675246565729319 7152226613512869848593979)
            ·
              refine ⟨10728339920269304772890969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152226613512869848593979 10728339920269304772890969)
              ·
                refine ⟨8046254940201978579668227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10728339920269304772890969 8046254940201978579668227)
                ·
                  refine ⟨12069382410302967869502341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046254940201978579668227 12069382410302967869502341)
                  ·
                    refine ⟨2263009201931806475531689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12069382410302967869502341 2263009201931806475531689)
                    ·
                      refine ⟨1697256901448854856648767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263009201931806475531689 1697256901448854856648767)
                      ·
                        rfl

theorem cell23_3305396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_3305396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305396 prefixEnd_3305396 := by exact prefixLift 3305396
  have htrace : WordTrace (prefixWord ++ tailWord_3305396) baseStart_3305396 baseEnd_3305396 := by
    simpa [prefixWord, tailWord_3305396, baseEnd_3305396] using wordTrace_append hprefix tailTrace_3305396
  have hstable : (prefixWord ++ tailWord_3305396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305396).length < 2 ^ (prefixWord ++ tailWord_3305396).sum := by decide
  have hdescent : baseEnd_3305396 < baseStart_3305396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305408 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_3305408 : Nat := 118140960795 + 3305408 * 2 ^ 59
def prefixEnd_3305408 : Nat := 4983230072969 + 3 ^ 40 * 3305408 * 2
def baseEnd_3305408 : Nat := 1697263063216708809698711

theorem tailTrace_3305408 : CollatzResearch.WordTrace tailWord_3305408 prefixEnd_3305408 1697263063216708809698711 := by
  unfold tailWord_3305408
  simp only [CollatzResearch.WordTrace]
  refine ⟨60279067004539404793938439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80372089339385873058584585 60279067004539404793938439)
  ·
    refine ⟨90418600506809107190907659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60279067004539404793938439 90418600506809107190907659)
    ·
      refine ⟨135627900760213660786361489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90418600506809107190907659 135627900760213660786361489)
      ·
        refine ⟨101720925570160245589771117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135627900760213660786361489 101720925570160245589771117)
        ·
          refine ⟨38145347088810092096164169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101720925570160245589771117 38145347088810092096164169)
          ·
            refine ⟨28609010316607569072123127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38145347088810092096164169 28609010316607569072123127)
            ·
              refine ⟨42913515474911353608184691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28609010316607569072123127 42913515474911353608184691)
              ·
                refine ⟨64370273212367030412277037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42913515474911353608184691 64370273212367030412277037)
                ·
                  refine ⟨24138852454637636404603889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64370273212367030412277037 24138852454637636404603889)
                  ·
                    refine ⟨18104139340978227303452917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24138852454637636404603889 18104139340978227303452917)
                    ·
                      refine ⟨1697263063216708809698711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18104139340978227303452917 1697263063216708809698711)
                      ·
                        rfl

theorem cell23_3305408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_3305408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305408 prefixEnd_3305408 := by exact prefixLift 3305408
  have htrace : WordTrace (prefixWord ++ tailWord_3305408) baseStart_3305408 baseEnd_3305408 := by
    simpa [prefixWord, tailWord_3305408, baseEnd_3305408] using wordTrace_append hprefix tailTrace_3305408
  have hstable : (prefixWord ++ tailWord_3305408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305408).length < 2 ^ (prefixWord ++ tailWord_3305408).sum := by decide
  have hdescent : baseEnd_3305408 < baseStart_3305408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305455 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 3]
def baseStart_3305455 : Nat := 118140960795 + 3305455 * 2 ^ 59
def prefixEnd_3305455 : Nat := 4983230072969 + 3 ^ 40 * 3305455 * 2
def baseEnd_3305455 : Nat := 1697287196807470125810995

theorem tailTrace_3305455 : CollatzResearch.WordTrace tailWord_3305455 prefixEnd_3305455 1697287196807470125810995 := by
  unfold tailWord_3305455
  simp only [CollatzResearch.WordTrace]
  refine ⟨120559848239908536614837819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80373232159939024409891879 120559848239908536614837819)
  ·
    refine ⟨180839772359862804922256729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120559848239908536614837819 180839772359862804922256729)
    ·
      refine ⟨135629829269897103691692547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180839772359862804922256729 135629829269897103691692547)
      ·
        refine ⟨203444743904845655537538821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135629829269897103691692547 203444743904845655537538821)
        ·
          refine ⟨38145889482158560413288529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203444743904845655537538821 38145889482158560413288529)
          ·
            refine ⟨28609417111618920309966397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38145889482158560413288529 28609417111618920309966397)
            ·
              refine ⟨10728531416857095116237399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28609417111618920309966397 10728531416857095116237399)
              ·
                refine ⟨16092797125285642674356099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10728531416857095116237399 16092797125285642674356099)
                ·
                  refine ⟨24139195687928464011534149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16092797125285642674356099 24139195687928464011534149)
                  ·
                    refine ⟨4526099191486587002162653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24139195687928464011534149 4526099191486587002162653)
                    ·
                      refine ⟨1697287196807470125810995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4526099191486587002162653 1697287196807470125810995)
                      ·
                        rfl

theorem cell23_3305455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_3305455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305455 prefixEnd_3305455 := by exact prefixLift 3305455
  have htrace : WordTrace (prefixWord ++ tailWord_3305455) baseStart_3305455 baseEnd_3305455 := by
    simpa [prefixWord, tailWord_3305455, baseEnd_3305455] using wordTrace_append hprefix tailTrace_3305455
  have hstable : (prefixWord ++ tailWord_3305455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305455).length < 2 ^ (prefixWord ++ tailWord_3305455).sum := by decide
  have hdescent : baseEnd_3305455 < baseStart_3305455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305479 : List Nat := [1, 1, 4, 3, 1, 2, 2, 4, 1, 4]
def baseStart_3305479 : Nat := 118140960795 + 3305479 * 2 ^ 59
def prefixEnd_3305479 : Nat := 4983230072969 + 3 ^ 40 * 3305479 * 2
def baseEnd_3305479 : Nat := 565766506781059343970295

theorem tailTrace_3305479 : CollatzResearch.WordTrace tailWord_3305479 prefixEnd_3305479 565766506781059343970295 := by
  unfold tailWord_3305479
  simp only [CollatzResearch.WordTrace]
  refine ⟨120560723591821588713711491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80373815727881059142474327 120560723591821588713711491)
  ·
    refine ⟨180841085387732383070567237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120560723591821588713711491 180841085387732383070567237)
    ·
      refine ⟨33907703510199821825731357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180841085387732383070567237 33907703510199821825731357)
      ·
        refine ⟨12715388816324933184649259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33907703510199821825731357 12715388816324933184649259)
        ·
          refine ⟨19073083224487399776973889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12715388816324933184649259 19073083224487399776973889)
          ·
            refine ⟨14304812418365549832730417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19073083224487399776973889 14304812418365549832730417)
            ·
              refine ⟨10728609313774162374547813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14304812418365549832730417 10728609313774162374547813)
              ·
                refine ⟨2011614246332655445227715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10728609313774162374547813 2011614246332655445227715)
                ·
                  refine ⟨3017421369498983167841573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011614246332655445227715 3017421369498983167841573)
                  ·
                    refine ⟨565766506781059343970295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017421369498983167841573 565766506781059343970295)
                    ·
                      rfl

theorem cell23_3305479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_3305479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305479 prefixEnd_3305479 := by exact prefixLift 3305479
  have htrace : WordTrace (prefixWord ++ tailWord_3305479) baseStart_3305479 baseEnd_3305479 := by
    simpa [prefixWord, tailWord_3305479, baseEnd_3305479] using wordTrace_append hprefix tailTrace_3305479
  have hstable : (prefixWord ++ tailWord_3305479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305479).length < 2 ^ (prefixWord ++ tailWord_3305479).sum := by decide
  have hdescent : baseEnd_3305479 < baseStart_3305479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305519 : List Nat := [1, 1, 2, 1, 2, 1, 1, 9, 1, 1, 3]
def baseStart_3305519 : Nat := 118140960795 + 3305519 * 2 ^ 59
def prefixEnd_3305519 : Nat := 4983230072969 + 3 ^ 40 * 3305519 * 2
def baseEnd_3305519 : Nat := 1697320059569357875410701

theorem tailTrace_3305519 : CollatzResearch.WordTrace tailWord_3305519 prefixEnd_3305519 1697320059569357875410701 := by
  unfold tailWord_3305519
  simp only [CollatzResearch.WordTrace]
  refine ⟨120562182511676675545167611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80374788341117783696778407 120562182511676675545167611)
  ·
    refine ⟨180843273767515013317751417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120562182511676675545167611 180843273767515013317751417)
    ·
      refine ⟨135632455325636259988313563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180843273767515013317751417 135632455325636259988313563)
      ·
        refine ⟨203448682988454389982470345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135632455325636259988313563 203448682988454389982470345)
        ·
          refine ⟨152586512241340792486852759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203448682988454389982470345 152586512241340792486852759)
          ·
            refine ⟨228879768362011188730279139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152586512241340792486852759 228879768362011188730279139)
            ·
              refine ⟨343319652543016783095418709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228879768362011188730279139 343319652543016783095418709)
              ·
                refine ⟨2011638589119238963449719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 343319652543016783095418709 2011638589119238963449719)
                ·
                  refine ⟨3017457883678858445174579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011638589119238963449719 3017457883678858445174579)
                  ·
                    refine ⟨4526186825518287667761869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017457883678858445174579 4526186825518287667761869)
                    ·
                      refine ⟨1697320059569357875410701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4526186825518287667761869 1697320059569357875410701)
                      ·
                        rfl

theorem cell23_3305519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 1, 3].length) (baseStart_3305519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305519 prefixEnd_3305519 := by exact prefixLift 3305519
  have htrace : WordTrace (prefixWord ++ tailWord_3305519) baseStart_3305519 baseEnd_3305519 := by
    simpa [prefixWord, tailWord_3305519, baseEnd_3305519] using wordTrace_append hprefix tailTrace_3305519
  have hstable : (prefixWord ++ tailWord_3305519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305519).length < 2 ^ (prefixWord ++ tailWord_3305519).sum := by decide
  have hdescent : baseEnd_3305519 < baseStart_3305519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305522 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_3305522 : Nat := 118140960795 + 3305522 * 2 ^ 59
def prefixEnd_3305522 : Nat := 4983230072969 + 3 ^ 40 * 3305522 * 2
def baseEnd_3305522 : Nat := 565773866670440454557729

theorem tailTrace_3305522 : CollatzResearch.WordTrace tailWord_3305522 prefixEnd_3305522 565773866670440454557729 := by
  unfold tailWord_3305522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30140572982666451764381705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80374861287110538038351213 30140572982666451764381705)
  ·
    refine ⟨22605429736999838823286279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30140572982666451764381705 22605429736999838823286279)
    ·
      refine ⟨33908144605499758234929419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22605429736999838823286279 33908144605499758234929419)
      ·
        refine ⟨50862216908249637352394129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33908144605499758234929419 50862216908249637352394129)
        ·
          refine ⟨38146662681187228014295597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50862216908249637352394129 38146662681187228014295597)
          ·
            refine ⟨14304998505445210505360849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38146662681187228014295597 14304998505445210505360849)
            ·
              refine ⟨10728748879083907879020637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14304998505445210505360849 10728748879083907879020637)
              ·
                refine ⟨4023280829656465454632739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10728748879083907879020637 4023280829656465454632739)
                ·
                  refine ⟨6034921244484698181949109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023280829656465454632739 6034921244484698181949109)
                  ·
                    refine ⟨565773866670440454557729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6034921244484698181949109 565773866670440454557729)
                    ·
                      rfl

theorem cell23_3305522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_3305522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305522 prefixEnd_3305522 := by exact prefixLift 3305522
  have htrace : WordTrace (prefixWord ++ tailWord_3305522) baseStart_3305522 baseEnd_3305522 := by
    simpa [prefixWord, tailWord_3305522, baseEnd_3305522] using wordTrace_append hprefix tailTrace_3305522
  have hstable : (prefixWord ++ tailWord_3305522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305522).length < 2 ^ (prefixWord ++ tailWord_3305522).sum := by decide
  have hdescent : baseEnd_3305522 < baseStart_3305522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305545 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_3305545 : Nat := 118140960795 + 3305545 * 2 ^ 59
def prefixEnd_3305545 : Nat := 4983230072969 + 3 ^ 40 * 3305545 * 2
def baseEnd_3305545 : Nat := 1697333410066374773685581

theorem tailTrace_3305545 : CollatzResearch.WordTrace tailWord_3305545 prefixEnd_3305545 1697333410066374773685581 := by
  unfold tailWord_3305545
  simp only [CollatzResearch.WordTrace]
  refine ⟨120563130809582481985614089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80375420539721654657076059 120563130809582481985614089)
  ·
    refine ⟨90422348107186861489210567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120563130809582481985614089 90422348107186861489210567)
    ·
      refine ⟨135633522160780292233815851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90422348107186861489210567 135633522160780292233815851)
      ·
        refine ⟨203450283241170438350723777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135633522160780292233815851 203450283241170438350723777)
        ·
          refine ⟨152587712430877828763042833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203450283241170438350723777 152587712430877828763042833)
          ·
            refine ⟨114440784323158371572282125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152587712430877828763042833 114440784323158371572282125)
            ·
              refine ⟨42915294121184389339605797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114440784323158371572282125 42915294121184389339605797)
              ·
                refine ⟨8046617647722073001176087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42915294121184389339605797 8046617647722073001176087)
                ·
                  refine ⟨12069926471583109501764131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046617647722073001176087 12069926471583109501764131)
                  ·
                    refine ⟨18104889707374664252646197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12069926471583109501764131 18104889707374664252646197)
                    ·
                      refine ⟨1697333410066374773685581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18104889707374664252646197 1697333410066374773685581)
                      ·
                        rfl

theorem cell23_3305545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_3305545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305545 prefixEnd_3305545 := by exact prefixLift 3305545
  have htrace : WordTrace (prefixWord ++ tailWord_3305545) baseStart_3305545 baseEnd_3305545 := by
    simpa [prefixWord, tailWord_3305545, baseEnd_3305545] using wordTrace_append hprefix tailTrace_3305545
  have hstable : (prefixWord ++ tailWord_3305545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305545).length < 2 ^ (prefixWord ++ tailWord_3305545).sum := by decide
  have hdescent : baseEnd_3305545 < baseStart_3305545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305559 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 3, 2, 2]
def baseStart_3305559 : Nat := 118140960795 + 3305559 * 2 ^ 59
def prefixEnd_3305559 : Nat := 4983230072969 + 3 ^ 40 * 3305559 * 2
def baseEnd_3305559 : Nat := 1697340598795537718910517

theorem tailTrace_3305559 : CollatzResearch.WordTrace tailWord_3305559 prefixEnd_3305559 1697340598795537718910517 := by
  unfold tailWord_3305559
  simp only [CollatzResearch.WordTrace]
  refine ⟨120563641431531762376623731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80375760954354508251082487 120563641431531762376623731)
  ·
    refine ⟨180845462147297643564935597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120563641431531762376623731 180845462147297643564935597)
    ·
      refine ⟨67817048305236616336850849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180845462147297643564935597 67817048305236616336850849)
      ·
        refine ⟨50862786228927462252638137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67817048305236616336850849 50862786228927462252638137)
        ·
          refine ⟨38147089671695596689478603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50862786228927462252638137 38147089671695596689478603)
          ·
            refine ⟨57220634507543395034217905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38147089671695596689478603 57220634507543395034217905)
            ·
              refine ⟨42915475880657546275663429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57220634507543395034217905 42915475880657546275663429)
              ·
                refine ⟨8046651727623289926686893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42915475880657546275663429 8046651727623289926686893)
                ·
                  refine ⟨3017494397858733722507585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8046651727623289926686893 3017494397858733722507585)
                  ·
                    refine ⟨2263120798394050291880689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3017494397858733722507585 2263120798394050291880689)
                    ·
                      refine ⟨1697340598795537718910517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263120798394050291880689 1697340598795537718910517)
                      ·
                        rfl

theorem cell23_3305559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_3305559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305559 prefixEnd_3305559 := by exact prefixLift 3305559
  have htrace : WordTrace (prefixWord ++ tailWord_3305559) baseStart_3305559 baseEnd_3305559 := by
    simpa [prefixWord, tailWord_3305559, baseEnd_3305559] using wordTrace_append hprefix tailTrace_3305559
  have hstable : (prefixWord ++ tailWord_3305559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305559).length < 2 ^ (prefixWord ++ tailWord_3305559).sum := by decide
  have hdescent : baseEnd_3305559 < baseStart_3305559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305562 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_3305562 : Nat := 118140960795 + 3305562 * 2 ^ 59
def prefixEnd_3305562 : Nat := 4983230072969 + 3 ^ 40 * 3305562 * 2
def baseEnd_3305562 : Nat := 1697342139237501207173003

theorem tailTrace_3305562 : CollatzResearch.WordTrace tailWord_3305562 prefixEnd_3305562 1697342139237501207173003 := by
  unfold tailWord_3305562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30140937712630223472245735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80375833900347262592655293 30140937712630223472245735)
  ·
    refine ⟨45211406568945335208368603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30140937712630223472245735 45211406568945335208368603)
    ·
      refine ⟨67817109853418002812552905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45211406568945335208368603 67817109853418002812552905)
      ·
        refine ⟨50862832390063502109414679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67817109853418002812552905 50862832390063502109414679)
        ·
          refine ⟨76294248585095253164122019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50862832390063502109414679 76294248585095253164122019)
          ·
            refine ⟨114441372877642879746183029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76294248585095253164122019 114441372877642879746183029)
            ·
              refine ⟨10728878707279019976204659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114441372877642879746183029 10728878707279019976204659)
              ·
                refine ⟨16093318060918529964306989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10728878707279019976204659 16093318060918529964306989)
                ·
                  refine ⟨6034994272844448736615121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16093318060918529964306989 6034994272844448736615121)
                  ·
                    refine ⟨4526245704633336552461341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6034994272844448736615121 4526245704633336552461341)
                    ·
                      refine ⟨1697342139237501207173003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4526245704633336552461341 1697342139237501207173003)
                      ·
                        rfl

theorem cell23_3305562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_3305562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305562 prefixEnd_3305562 := by exact prefixLift 3305562
  have htrace : WordTrace (prefixWord ++ tailWord_3305562) baseStart_3305562 baseEnd_3305562 := by
    simpa [prefixWord, tailWord_3305562, baseEnd_3305562] using wordTrace_append hprefix tailTrace_3305562
  have hstable : (prefixWord ++ tailWord_3305562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305562).length < 2 ^ (prefixWord ++ tailWord_3305562).sum := by decide
  have hdescent : baseEnd_3305562 < baseStart_3305562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305593 : List Nat := [1, 2, 1, 3, 4, 2, 1, 4, 1, 2, 2]
def baseStart_3305593 : Nat := 118140960795 + 3305593 * 2 ^ 59
def prefixEnd_3305593 : Nat := 4983230072969 + 3 ^ 40 * 3305593 * 2
def baseEnd_3305593 : Nat := 1697358057137790585885361

theorem tailTrace_3305593 : CollatzResearch.WordTrace tailWord_3305593 prefixEnd_3305593 1697358057137790585885361 := by
  unfold tailWord_3305593
  simp only [CollatzResearch.WordTrace]
  refine ⟨120564881513408586183361433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80376587675605724122240955 120564881513408586183361433)
  ·
    refine ⟨90423661135056439637521075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120564881513408586183361433 90423661135056439637521075)
    ·
      refine ⟨135635491702584659456281613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90423661135056439637521075 135635491702584659456281613)
      ·
        refine ⟨50863309388469247296105605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135635491702584659456281613 50863309388469247296105605)
        ·
          refine ⟨9536870510337983868019801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50863309388469247296105605 9536870510337983868019801)
          ·
            refine ⟨7152652882753487901014851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9536870510337983868019801 7152652882753487901014851)
            ·
              refine ⟨10728979324130231851522277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152652882753487901014851 10728979324130231851522277)
              ·
                refine ⟨2011683623274418472160427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10728979324130231851522277 2011683623274418472160427)
                ·
                  refine ⟨3017525434911627708240641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011683623274418472160427 3017525434911627708240641)
                  ·
                    refine ⟨2263144076183720781180481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3017525434911627708240641 2263144076183720781180481)
                    ·
                      refine ⟨1697358057137790585885361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263144076183720781180481 1697358057137790585885361)
                      ·
                        rfl

theorem cell23_3305593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_3305593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305593 prefixEnd_3305593 := by exact prefixLift 3305593
  have htrace : WordTrace (prefixWord ++ tailWord_3305593) baseStart_3305593 baseEnd_3305593 := by
    simpa [prefixWord, tailWord_3305593, baseEnd_3305593] using wordTrace_append hprefix tailTrace_3305593
  have hstable : (prefixWord ++ tailWord_3305593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305593).length < 2 ^ (prefixWord ++ tailWord_3305593).sum := by decide
  have hdescent : baseEnd_3305593 < baseStart_3305593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305609 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 3]
def baseStart_3305609 : Nat := 118140960795 + 3305609 * 2 ^ 59
def prefixEnd_3305609 : Nat := 4983230072969 + 3 ^ 40 * 3305609 * 2
def baseEnd_3305609 : Nat := 1697366272828262523285287

theorem tailTrace_3305609 : CollatzResearch.WordTrace tailWord_3305609 prefixEnd_3305609 1697366272828262523285287 := by
  unfold tailWord_3305609
  simp only [CollatzResearch.WordTrace]
  refine ⟨120565465081350620915943881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80376976720900413943962587 120565465081350620915943881)
  ·
    refine ⟨90424098811012965686957911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120565465081350620915943881 90424098811012965686957911)
    ·
      refine ⟨135636148216519448530436867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90424098811012965686957911 135636148216519448530436867)
      ·
        refine ⟨203454222324779172795655301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135636148216519448530436867 203454222324779172795655301)
        ·
          refine ⟨38147666685896094899185369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203454222324779172795655301 38147666685896094899185369)
          ·
            refine ⟨28610750014422071174389027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38147666685896094899185369 28610750014422071174389027)
            ·
              refine ⟨42916125021633106761583541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28610750014422071174389027 42916125021633106761583541)
              ·
                refine ⟨4023386720778103758898457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42916125021633106761583541 4023386720778103758898457)
                ·
                  refine ⟨3017540040583577819173843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4023386720778103758898457 3017540040583577819173843)
                  ·
                    refine ⟨4526310060875366728760765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017540040583577819173843 4526310060875366728760765)
                    ·
                      refine ⟨1697366272828262523285287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4526310060875366728760765 1697366272828262523285287)
                      ·
                        rfl

theorem cell23_3305609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 1, 3].length) (baseStart_3305609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305609 prefixEnd_3305609 := by exact prefixLift 3305609
  have htrace : WordTrace (prefixWord ++ tailWord_3305609) baseStart_3305609 baseEnd_3305609 := by
    simpa [prefixWord, tailWord_3305609, baseEnd_3305609] using wordTrace_append hprefix tailTrace_3305609
  have hstable : (prefixWord ++ tailWord_3305609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305609).length < 2 ^ (prefixWord ++ tailWord_3305609).sum := by decide
  have hdescent : baseEnd_3305609 < baseStart_3305609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305619 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 1, 3, 2]
def baseStart_3305619 : Nat := 118140960795 + 3305619 * 2 ^ 59
def prefixEnd_3305619 : Nat := 4983230072969 + 3 ^ 40 * 3305619 * 2
def baseEnd_3305619 : Nat := 1697371407634807484160241

theorem tailTrace_3305619 : CollatzResearch.WordTrace tailWord_3305619 prefixEnd_3305619 1697371407634807484160241 := by
  unfold tailWord_3305619
  simp only [CollatzResearch.WordTrace]
  refine ⟨120565829811314392623807911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80377219874209595082538607 120565829811314392623807911)
  ·
    refine ⟨180848744716971588935711867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120565829811314392623807911 180848744716971588935711867)
    ·
      refine ⟨271273117075457383403567801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180848744716971588935711867 271273117075457383403567801)
      ·
        refine ⟨203454837806593037552675851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271273117075457383403567801 203454837806593037552675851)
        ·
          refine ⟨305182256709889556329013777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203454837806593037552675851 305182256709889556329013777)
          ·
            refine ⟨228886692532417167246760333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305182256709889556329013777 228886692532417167246760333)
            ·
              refine ⟨85832509699656437717535125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228886692532417167246760333 85832509699656437717535125)
              ·
                refine ⟨4023398892171395518009459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85832509699656437717535125 4023398892171395518009459)
                ·
                  refine ⟨6035098338257093277014189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023398892171395518009459 6035098338257093277014189)
                  ·
                    refine ⟨2263161876846409978880321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6035098338257093277014189 2263161876846409978880321)
                    ·
                      refine ⟨1697371407634807484160241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263161876846409978880321 1697371407634807484160241)
                      ·
                        rfl

theorem cell23_3305619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 3, 2].length) (baseStart_3305619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305619 prefixEnd_3305619 := by exact prefixLift 3305619
  have htrace : WordTrace (prefixWord ++ tailWord_3305619) baseStart_3305619 baseEnd_3305619 := by
    simpa [prefixWord, tailWord_3305619, baseEnd_3305619] using wordTrace_append hprefix tailTrace_3305619
  have hstable : (prefixWord ++ tailWord_3305619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305619).length < 2 ^ (prefixWord ++ tailWord_3305619).sum := by decide
  have hdescent : baseEnd_3305619 < baseStart_3305619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305630 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_3305630 : Nat := 118140960795 + 3305630 * 2 ^ 59
def prefixEnd_3305630 : Nat := 4983230072969 + 3 ^ 40 * 3305630 * 2
def baseEnd_3305630 : Nat := 1697377055922006941122691

theorem tailTrace_3305630 : CollatzResearch.WordTrace tailWord_3305630 prefixEnd_3305630 1697377055922006941122691 := by
  unfold tailWord_3305630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15070778876784317687807293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80377487342849694334972229 15070778876784317687807293)
  ·
    refine ⟨5651542078794119132927735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15070778876784317687807293 5651542078794119132927735)
    ·
      refine ⟨8477313118191178699391603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651542078794119132927735 8477313118191178699391603)
      ·
        refine ⟨12715969677286768049087405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8477313118191178699391603 12715969677286768049087405)
        ·
          refine ⟨4768488628982538018407777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12715969677286768049087405 4768488628982538018407777)
          ·
            refine ⟨3576366471736903513805833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4768488628982538018407777 3576366471736903513805833)
            ·
              refine ⟨2682274853802677635354375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3576366471736903513805833 2682274853802677635354375)
              ·
                refine ⟨4023412280704016453031563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682274853802677635354375 4023412280704016453031563)
                ·
                  refine ⟨6035118421056024679547345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023412280704016453031563 6035118421056024679547345)
                  ·
                    refine ⟨4526338815792018509660509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6035118421056024679547345 4526338815792018509660509)
                    ·
                      refine ⟨1697377055922006941122691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4526338815792018509660509 1697377055922006941122691)
                      ·
                        rfl

theorem cell23_3305630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_3305630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305630 prefixEnd_3305630 := by exact prefixLift 3305630
  have htrace : WordTrace (prefixWord ++ tailWord_3305630) baseStart_3305630 baseEnd_3305630 := by
    simpa [prefixWord, tailWord_3305630, baseEnd_3305630] using wordTrace_append hprefix tailTrace_3305630
  have hstable : (prefixWord ++ tailWord_3305630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305630).length < 2 ^ (prefixWord ++ tailWord_3305630).sum := by decide
  have hdescent : baseEnd_3305630 < baseStart_3305630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305686 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3305686 : Nat := 118140960795 + 3305686 * 2 ^ 59
def prefixEnd_3305686 : Nat := 4983230072969 + 3 ^ 40 * 3305686 * 2
def baseEnd_3305686 : Nat := 1697405810838658722022433

theorem tailTrace_3305686 : CollatzResearch.WordTrace tailWord_3305686 prefixEnd_3305686 1697405810838658722022433 := by
  unfold tailWord_3305686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535517093879478941656057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80378849001381108710997941 7535517093879478941656057)
  ·
    refine ⟨5651637820409609206242043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7535517093879478941656057 5651637820409609206242043)
    ·
      refine ⟨8477456730614413809363065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651637820409609206242043 8477456730614413809363065)
      ·
        refine ⟨6358092547960810357022299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8477456730614413809363065 6358092547960810357022299)
        ·
          refine ⟨9537138821941215535533449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358092547960810357022299 9537138821941215535533449)
          ·
            refine ⟨7152854116455911651650087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9537138821941215535533449 7152854116455911651650087)
            ·
              refine ⟨10729281174683867477475131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152854116455911651650087 10729281174683867477475131)
              ·
                refine ⟨16093921762025801216212697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10729281174683867477475131 16093921762025801216212697)
                ·
                  refine ⟨12070441321519350912159523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16093921762025801216212697 12070441321519350912159523)
                  ·
                    refine ⟨18105661982279026368239285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12070441321519350912159523 18105661982279026368239285)
                    ·
                      refine ⟨1697405810838658722022433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18105661982279026368239285 1697405810838658722022433)
                      ·
                        rfl

theorem cell23_3305686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3305686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305686 prefixEnd_3305686 := by exact prefixLift 3305686
  have htrace : WordTrace (prefixWord ++ tailWord_3305686) baseStart_3305686 baseEnd_3305686 := by
    simpa [prefixWord, tailWord_3305686, baseEnd_3305686] using wordTrace_append hprefix tailTrace_3305686
  have hstable : (prefixWord ++ tailWord_3305686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305686).length < 2 ^ (prefixWord ++ tailWord_3305686).sum := by decide
  have hdescent : baseEnd_3305686 < baseStart_3305686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305689 : List Nat := [1, 2, 1, 2, 3, 1, 5, 3, 5]
def baseStart_3305689 : Nat := 118140960795 + 3305689 * 2 ^ 59
def prefixEnd_3305689 : Nat := 4983230072969 + 3 ^ 40 * 3305689 * 2
def baseEnd_3305689 : Nat := 188600816808958023364991

theorem tailTrace_3305689 : CollatzResearch.WordTrace tailWord_3305689 prefixEnd_3305689 188600816808958023364991 := by
  unfold tailWord_3305689
  simp only [CollatzResearch.WordTrace]
  refine ⟨120568382921060794578856121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80378921947373863052570747 120568382921060794578856121)
  ·
    refine ⟨90426287190795595934142091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120568382921060794578856121 90426287190795595934142091)
    ·
      refine ⟨135639430786193393901213137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90426287190795595934142091 135639430786193393901213137)
      ·
        refine ⟨101729573089645045425909853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135639430786193393901213137 101729573089645045425909853)
        ·
          refine ⟨38148589908616892034716195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101729573089645045425909853 38148589908616892034716195)
          ·
            refine ⟨57222884862925338052074293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38148589908616892034716195 57222884862925338052074293)
            ·
              refine ⟨5364645455899250442381965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57222884862925338052074293 5364645455899250442381965)
              ·
                refine ⟨2011742045962218915893237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5364645455899250442381965 2011742045962218915893237)
                ·
                  refine ⟨188600816808958023364991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2011742045962218915893237 188600816808958023364991)
                  ·
                    rfl

theorem cell23_3305689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 5].length) (baseStart_3305689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305689 prefixEnd_3305689 := by exact prefixLift 3305689
  have htrace : WordTrace (prefixWord ++ tailWord_3305689) baseStart_3305689 baseEnd_3305689 := by
    simpa [prefixWord, tailWord_3305689, baseEnd_3305689] using wordTrace_append hprefix tailTrace_3305689
  have hstable : (prefixWord ++ tailWord_3305689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305689).length < 2 ^ (prefixWord ++ tailWord_3305689).sum := by decide
  have hdescent : baseEnd_3305689 < baseStart_3305689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305706 : List Nat := [3, 1, 3, 1, 1, 2, 5, 2, 5]
def baseStart_3305706 : Nat := 118140960795 + 3305706 * 2 ^ 59
def prefixEnd_3305706 : Nat := 4983230072969 + 3 ^ 40 * 3305706 * 2
def baseEnd_3305706 : Nat := 188601786716860960419149

theorem tailTrace_3305706 : CollatzResearch.WordTrace tailWord_3305706 prefixEnd_3305706 188601786716860960419149 := by
  unfold tailWord_3305706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30142250740499801620556243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80379335307999470988149981 30142250740499801620556243)
  ·
    refine ⟨45213376110749702430834365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30142250740499801620556243 45213376110749702430834365)
    ·
      refine ⟨16955016041531138411562887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45213376110749702430834365 16955016041531138411562887)
      ·
        refine ⟨25432524062296707617344331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16955016041531138411562887 25432524062296707617344331)
        ·
          refine ⟨38148786093445061426016497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25432524062296707617344331 38148786093445061426016497)
          ·
            refine ⟨28611589570083796069512373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38148786093445061426016497 28611589570083796069512373)
            ·
              refine ⟨2682336522195355881516785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28611589570083796069512373 2682336522195355881516785)
              ·
                refine ⟨2011752391646516911137589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682336522195355881516785 2011752391646516911137589)
                ·
                  refine ⟨188601786716860960419149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2011752391646516911137589 188601786716860960419149)
                  ·
                    rfl

theorem cell23_3305706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_3305706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305706 prefixEnd_3305706 := by exact prefixLift 3305706
  have htrace : WordTrace (prefixWord ++ tailWord_3305706) baseStart_3305706 baseEnd_3305706 := by
    simpa [prefixWord, tailWord_3305706, baseEnd_3305706] using wordTrace_append hprefix tailTrace_3305706
  have hstable : (prefixWord ++ tailWord_3305706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305706).length < 2 ^ (prefixWord ++ tailWord_3305706).sum := by decide
  have hdescent : baseEnd_3305706 < baseStart_3305706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305739 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 4]
def baseStart_3305739 : Nat := 118140960795 + 3305739 * 2 ^ 59
def prefixEnd_3305739 : Nat := 4983230072969 + 3 ^ 40 * 3305739 * 2
def baseEnd_3305739 : Nat := 1697433025313347014659689

theorem tailTrace_3305739 : CollatzResearch.WordTrace tailWord_3305739 prefixEnd_3305739 1697433025313347014659689 := by
  unfold tailWord_3305739
  simp only [CollatzResearch.WordTrace]
  refine ⟨120570206570879653118176271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80380137713919768745450847 120570206570879653118176271)
  ·
    refine ⟨180855309856319479677264407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120570206570879653118176271 180855309856319479677264407)
    ·
      refine ⟨271282964784479219515896611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180855309856319479677264407 271282964784479219515896611)
      ·
        refine ⟨406924447176718829273844917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271282964784479219515896611 406924447176718829273844917)
        ·
          refine ⟨38149166922817390244422961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 406924447176718829273844917 38149166922817390244422961)
          ·
            refine ⟨28611875192113042683317221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38149166922817390244422961 28611875192113042683317221)
            ·
              refine ⟨5364726598521195503121979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28611875192113042683317221 5364726598521195503121979)
              ·
                refine ⟨8047089897781793254682969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364726598521195503121979 8047089897781793254682969)
                ·
                  refine ⟨6035317423336344941012227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8047089897781793254682969 6035317423336344941012227)
                  ·
                    refine ⟨9052976135004517411518341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6035317423336344941012227 9052976135004517411518341)
                    ·
                      refine ⟨1697433025313347014659689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9052976135004517411518341 1697433025313347014659689)
                      ·
                        rfl

theorem cell23_3305739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 4].length) (baseStart_3305739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305739 prefixEnd_3305739 := by exact prefixLift 3305739
  have htrace : WordTrace (prefixWord ++ tailWord_3305739) baseStart_3305739 baseEnd_3305739 := by
    simpa [prefixWord, tailWord_3305739, baseEnd_3305739] using wordTrace_append hprefix tailTrace_3305739
  have hstable : (prefixWord ++ tailWord_3305739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305739).length < 2 ^ (prefixWord ++ tailWord_3305739).sum := by decide
  have hdescent : baseEnd_3305739 < baseStart_3305739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305752 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3305752 : Nat := 118140960795 + 3305752 * 2 ^ 59
def prefixEnd_3305752 : Nat := 4983230072969 + 3 ^ 40 * 3305752 * 2
def baseEnd_3305752 : Nat := 1697439700561855463797129

theorem tailTrace_3305752 : CollatzResearch.WordTrace tailWord_3305752 prefixEnd_3305752 1697439700561855463797129 := by
  unfold tailWord_3305752
  simp only [CollatzResearch.WordTrace]
  refine ⟨60285340359916278169199755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80380453813221704225599673 60285340359916278169199755)
  ·
    refine ⟨90428010539874417253799633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60285340359916278169199755 90428010539874417253799633)
    ·
      refine ⟨67821007904905812940349725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90428010539874417253799633 67821007904905812940349725)
      ·
        refine ⟨25432877964339679852631147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67821007904905812940349725 25432877964339679852631147)
        ·
          refine ⟨38149316946509519778946721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25432877964339679852631147 38149316946509519778946721)
          ·
            refine ⟨28611987709882139834210041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38149316946509519778946721 28611987709882139834210041)
            ·
              refine ⟨21458990782411604875657531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28611987709882139834210041 21458990782411604875657531)
              ·
                refine ⟨32188486173617407313486297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21458990782411604875657531 32188486173617407313486297)
                ·
                  refine ⟨24141364630213055485114723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32188486173617407313486297 24141364630213055485114723)
                  ·
                    refine ⟨36212046945319583227672085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24141364630213055485114723 36212046945319583227672085)
                    ·
                      refine ⟨1697439700561855463797129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36212046945319583227672085 1697439700561855463797129)
                      ·
                        rfl

theorem cell23_3305752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3305752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305752 prefixEnd_3305752 := by exact prefixLift 3305752
  have htrace : WordTrace (prefixWord ++ tailWord_3305752) baseStart_3305752 baseEnd_3305752 := by
    simpa [prefixWord, tailWord_3305752, baseEnd_3305752] using wordTrace_append hprefix tailTrace_3305752
  have hstable : (prefixWord ++ tailWord_3305752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305752).length < 2 ^ (prefixWord ++ tailWord_3305752).sum := by decide
  have hdescent : baseEnd_3305752 < baseStart_3305752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305802 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3305802 : Nat := 118140960795 + 3305802 * 2 ^ 59
def prefixEnd_3305802 : Nat := 4983230072969 + 3 ^ 40 * 3305802 * 2
def baseEnd_3305802 : Nat := 1697465374594580268171899

theorem tailTrace_3305802 : CollatzResearch.WordTrace tailWord_3305802 prefixEnd_3305802 1697465374594580268171899 := by
  unfold tailWord_3305802
  simp only [CollatzResearch.WordTrace]
  refine ⟨30143126092412853719429915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80381669579767609918479773 30143126092412853719429915)
  ·
    refine ⟨45214689138619280579144873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30143126092412853719429915 45214689138619280579144873)
    ·
      refine ⟨33911016853964460434358655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45214689138619280579144873 33911016853964460434358655)
      ·
        refine ⟨50866525280946690651537983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33911016853964460434358655 50866525280946690651537983)
        ·
          refine ⟨76299787921420035977306975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50866525280946690651537983 76299787921420035977306975)
          ·
            refine ⟨114449681882130053965960463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76299787921420035977306975 114449681882130053965960463)
            ·
              refine ⟨171674522823195080948940695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114449681882130053965960463 171674522823195080948940695)
              ·
                refine ⟨257511784234792621423411043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171674522823195080948940695 257511784234792621423411043)
                ·
                  refine ⟨386267676352188932135116565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257511784234792621423411043 386267676352188932135116565)
                  ·
                    refine ⟨18106297329008856193833589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 386267676352188932135116565 18106297329008856193833589)
                    ·
                      refine ⟨1697465374594580268171899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18106297329008856193833589 1697465374594580268171899)
                      ·
                        rfl

theorem cell23_3305802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3305802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305802 prefixEnd_3305802 := by exact prefixLift 3305802
  have htrace : WordTrace (prefixWord ++ tailWord_3305802) baseStart_3305802 baseEnd_3305802 := by
    simpa [prefixWord, tailWord_3305802, baseEnd_3305802] using wordTrace_append hprefix tailTrace_3305802
  have hstable : (prefixWord ++ tailWord_3305802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305802).length < 2 ^ (prefixWord ++ tailWord_3305802).sum := by decide
  have hdescent : baseEnd_3305802 < baseStart_3305802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305813 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 6]
def baseStart_3305813 : Nat := 118140960795 + 3305813 * 2 ^ 59
def prefixEnd_3305813 : Nat := 4983230072969 + 3 ^ 40 * 3305813 * 2
def baseEnd_3305813 : Nat := 188607891431308858348261

theorem tailTrace_3305813 : CollatzResearch.WordTrace tailWord_3305813 prefixEnd_3305813 188607891431308858348261 := by
  unfold tailWord_3305813
  simp only [CollatzResearch.WordTrace]
  refine ⟨120572905572611563756370093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80381937048407709170913395 120572905572611563756370093)
  ·
    refine ⟨45214839589729336408638785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120572905572611563756370093 45214839589729336408638785)
    ·
      refine ⟨33911129692297002306479089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45214839589729336408638785 33911129692297002306479089)
      ·
        refine ⟨25433347269222751729859317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33911129692297002306479089 25433347269222751729859317)
        ·
          refine ⟨2384376306489632974674311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25433347269222751729859317 2384376306489632974674311)
          ·
            refine ⟨3576564459734449462011467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384376306489632974674311 3576564459734449462011467)
            ·
              refine ⟨5364846689601674193017201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576564459734449462011467 5364846689601674193017201)
              ·
                refine ⟨4023635017201255644762901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364846689601674193017201 4023635017201255644762901)
                ·
                  refine ⟨188607891431308858348261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4023635017201255644762901 188607891431308858348261)
                  ·
                    rfl

theorem cell23_3305813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_3305813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305813 prefixEnd_3305813 := by exact prefixLift 3305813
  have htrace : WordTrace (prefixWord ++ tailWord_3305813) baseStart_3305813 baseEnd_3305813 := by
    simpa [prefixWord, tailWord_3305813, baseEnd_3305813] using wordTrace_append hprefix tailTrace_3305813
  have hstable : (prefixWord ++ tailWord_3305813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305813).length < 2 ^ (prefixWord ++ tailWord_3305813).sum := by decide
  have hdescent : baseEnd_3305813 < baseStart_3305813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305823 : List Nat := [1, 1, 2, 3, 1, 2, 4, 4, 1, 1, 3]
def baseStart_3305823 : Nat := 118140960795 + 3305823 * 2 ^ 59
def prefixEnd_3305823 : Nat := 4983230072969 + 3 ^ 40 * 3305823 * 2
def baseEnd_3305823 : Nat := 1697476157688324686009303

theorem tailTrace_3305823 : CollatzResearch.WordTrace tailWord_3305823 prefixEnd_3305823 1697476157688324686009303 := by
  unfold tailWord_3305823
  simp only [CollatzResearch.WordTrace]
  refine ⟨120573270302575335464234123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80382180201716890309489415 120573270302575335464234123)
  ·
    refine ⟨180859905453863003196351185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120573270302575335464234123 180859905453863003196351185)
    ·
      refine ⟨135644929090397252397263389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180859905453863003196351185 135644929090397252397263389)
      ·
        refine ⟨50866848408898969648973771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135644929090397252397263389 50866848408898969648973771)
        ·
          refine ⟨76300272613348454473460657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50866848408898969648973771 76300272613348454473460657)
          ·
            refine ⟨57225204460011340855095493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76300272613348454473460657 57225204460011340855095493)
            ·
              refine ⟨10729725836252126410330405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57225204460011340855095493 10729725836252126410330405)
              ·
                refine ⟨2011823594297273701936951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10729725836252126410330405 2011823594297273701936951)
                ·
                  refine ⟨3017735391445910552905427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011823594297273701936951 3017735391445910552905427)
                  ·
                    refine ⟨4526603087168865829358141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017735391445910552905427 4526603087168865829358141)
                    ·
                      refine ⟨1697476157688324686009303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4526603087168865829358141 1697476157688324686009303)
                      ·
                        rfl

theorem cell23_3305823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_3305823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305823 prefixEnd_3305823 := by exact prefixLift 3305823
  have htrace : WordTrace (prefixWord ++ tailWord_3305823) baseStart_3305823 baseEnd_3305823 := by
    simpa [prefixWord, tailWord_3305823, baseEnd_3305823] using wordTrace_append hprefix tailTrace_3305823
  have hstable : (prefixWord ++ tailWord_3305823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305823).length < 2 ^ (prefixWord ++ tailWord_3305823).sum := by decide
  have hdescent : baseEnd_3305823 < baseStart_3305823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305857 : List Nat := [1, 2, 4, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_3305857 : Nat := 118140960795 + 3305857 * 2 ^ 59
def prefixEnd_3305857 : Nat := 4983230072969 + 3 ^ 40 * 3305857 * 2
def baseEnd_3305857 : Nat := 1697493616030577552984147

theorem tailTrace_3305857 : CollatzResearch.WordTrace tailWord_3305857 prefixEnd_3305857 1697493616030577552984147 := by
  unfold tailWord_3305857
  simp only [CollatzResearch.WordTrace]
  refine ⟨120574510384452159270971825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80383006922968106180647883 120574510384452159270971825)
  ·
    refine ⟨90430882788339119453228869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120574510384452159270971825 90430882788339119453228869)
    ·
      refine ⟨16955790522813584897480413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90430882788339119453228869 16955790522813584897480413)
      ·
        refine ⟨6358421446055094336555155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16955790522813584897480413 6358421446055094336555155)
        ·
          refine ⟨9537632169082641504832733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358421446055094336555155 9537632169082641504832733)
          ·
            refine ⟨3576612063405990564312275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9537632169082641504832733 3576612063405990564312275)
            ·
              refine ⟨5364918095108985846468413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576612063405990564312275 5364918095108985846468413)
              ·
                refine ⟨2011844285665869692425655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5364918095108985846468413 2011844285665869692425655)
                ·
                  refine ⟨3017766428498804538638483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011844285665869692425655 3017766428498804538638483)
                  ·
                    refine ⟨4526649642748206807957725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017766428498804538638483 4526649642748206807957725)
                    ·
                      refine ⟨1697493616030577552984147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4526649642748206807957725 1697493616030577552984147)
                      ·
                        rfl

theorem cell23_3305857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_3305857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305857 prefixEnd_3305857 := by exact prefixLift 3305857
  have htrace : WordTrace (prefixWord ++ tailWord_3305857) baseStart_3305857 baseEnd_3305857 := by
    simpa [prefixWord, tailWord_3305857, baseEnd_3305857] using wordTrace_append hprefix tailTrace_3305857
  have hstable : (prefixWord ++ tailWord_3305857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305857).length < 2 ^ (prefixWord ++ tailWord_3305857).sum := by decide
  have hdescent : baseEnd_3305857 < baseStart_3305857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305872 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_3305872 : Nat := 118140960795 + 3305872 * 2 ^ 59
def prefixEnd_3305872 : Nat := 4983230072969 + 3 ^ 40 * 3305872 * 2
def baseEnd_3305872 : Nat := 1697501318240394994296577

theorem tailTrace_3305872 : CollatzResearch.WordTrace tailWord_3305872 prefixEnd_3305872 1697501318240394994296577 := by
  unfold tailWord_3305872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60287528739698908416383935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80383371652931877888511913 60287528739698908416383935)
  ·
    refine ⟨90431293109548362624575903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60287528739698908416383935 90431293109548362624575903)
    ·
      refine ⟨135646939664322543936863855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90431293109548362624575903 135646939664322543936863855)
      ·
        refine ⟨203470409496483815905295783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135646939664322543936863855 203470409496483815905295783)
        ·
          refine ⟨305205614244725723857943675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203470409496483815905295783 305205614244725723857943675)
          ·
            refine ⟨457808421367088585786915513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305205614244725723857943675 457808421367088585786915513)
            ·
              refine ⟨343356316025316439340186635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457808421367088585786915513 343356316025316439340186635)
              ·
                refine ⟨515034474037974659010279953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343356316025316439340186635 515034474037974659010279953)
                ·
                  refine ⟨386275855528480994257709965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515034474037974659010279953 386275855528480994257709965)
                  ·
                    refine ⟨144853445823180372846641237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386275855528480994257709965 144853445823180372846641237)
                    ·
                      refine ⟨1697501318240394994296577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 144853445823180372846641237 1697501318240394994296577)
                      ·
                        rfl

theorem cell23_3305872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_3305872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305872 prefixEnd_3305872 := by exact prefixLift 3305872
  have htrace : WordTrace (prefixWord ++ tailWord_3305872) baseStart_3305872 baseEnd_3305872 := by
    simpa [prefixWord, tailWord_3305872, baseEnd_3305872] using wordTrace_append hprefix tailTrace_3305872
  have hstable : (prefixWord ++ tailWord_3305872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305872).length < 2 ^ (prefixWord ++ tailWord_3305872).sum := by decide
  have hdescent : baseEnd_3305872 < baseStart_3305872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305880 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3305880 : Nat := 118140960795 + 3305880 * 2 ^ 59
def prefixEnd_3305880 : Nat := 4983230072969 + 3 ^ 40 * 3305880 * 2
def baseEnd_3305880 : Nat := 1697505426085630962996541

theorem tailTrace_3305880 : CollatzResearch.WordTrace tailWord_3305880 prefixEnd_3305880 1697505426085630962996541 := by
  unfold tailWord_3305880
  simp only [CollatzResearch.WordTrace]
  refine ⟨60287674631684417099529547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80383566175579222799372729 60287674631684417099529547)
  ·
    refine ⟨90431511947526625649294321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60287674631684417099529547 90431511947526625649294321)
    ·
      refine ⟨67823633960644969236970741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90431511947526625649294321 67823633960644969236970741)
      ·
        refine ⟨6358465683810465865966007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67823633960644969236970741 6358465683810465865966007)
        ·
          refine ⟨9537698525715698798949011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358465683810465865966007 9537698525715698798949011)
          ·
            refine ⟨14306547788573548198423517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9537698525715698798949011 14306547788573548198423517)
            ·
              refine ⟨5364955420715080574408819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14306547788573548198423517 5364955420715080574408819)
              ·
                refine ⟨8047433131072620861613229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364955420715080574408819 8047433131072620861613229)
                ·
                  refine ⟨3017787424152232823104961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8047433131072620861613229 3017787424152232823104961)
                  ·
                    refine ⟨2263340568114174617328721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3017787424152232823104961 2263340568114174617328721)
                    ·
                      refine ⟨1697505426085630962996541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263340568114174617328721 1697505426085630962996541)
                      ·
                        rfl

theorem cell23_3305880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3305880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305880 prefixEnd_3305880 := by exact prefixLift 3305880
  have htrace : WordTrace (prefixWord ++ tailWord_3305880) baseStart_3305880 baseEnd_3305880 := by
    simpa [prefixWord, tailWord_3305880, baseEnd_3305880] using wordTrace_append hprefix tailTrace_3305880
  have hstable : (prefixWord ++ tailWord_3305880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305880).length < 2 ^ (prefixWord ++ tailWord_3305880).sum := by decide
  have hdescent : baseEnd_3305880 < baseStart_3305880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305886 : List Nat := [4, 3, 1, 2, 1, 1, 1, 10]
def baseStart_3305886 : Nat := 118140960795 + 3305886 * 2 ^ 59
def prefixEnd_3305886 : Nat := 4983230072969 + 3 ^ 40 * 3305886 * 2
def baseEnd_3305886 : Nat := 62870685443316960723019

theorem tailTrace_3305886 : CollatzResearch.WordTrace tailWord_3305886 prefixEnd_3305886 62870685443316960723019 := by
  unfold tailWord_3305886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15071946012668387152972189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80383712067564731482518341 15071946012668387152972189)
  ·
    refine ⟨5651979754750645182364571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15071946012668387152972189 5651979754750645182364571)
    ·
      refine ⟨8477969632125967773546857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651979754750645182364571 8477969632125967773546857)
      ·
        refine ⟨6358477224094475830160143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8477969632125967773546857 6358477224094475830160143)
        ·
          refine ⟨9537715836141713745240215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358477224094475830160143 9537715836141713745240215)
          ·
            refine ⟨14306573754212570617860323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9537715836141713745240215 14306573754212570617860323)
            ·
              refine ⟨21459860631318855926790485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14306573754212570617860323 21459860631318855926790485)
              ·
                refine ⟨62870685443316960723019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21459860631318855926790485 62870685443316960723019)
                ·
                  rfl

theorem cell23_3305886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_3305886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305886 prefixEnd_3305886 := by exact prefixLift 3305886
  have htrace : WordTrace (prefixWord ++ tailWord_3305886) baseStart_3305886 baseEnd_3305886 := by
    simpa [prefixWord, tailWord_3305886, baseEnd_3305886] using wordTrace_append hprefix tailTrace_3305886
  have hstable : (prefixWord ++ tailWord_3305886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305886).length < 2 ^ (prefixWord ++ tailWord_3305886).sum := by decide
  have hdescent : baseEnd_3305886 < baseStart_3305886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3305953 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_3305953 : Nat := 118140960795 + 3305953 * 2 ^ 59
def prefixEnd_3305953 : Nat := 4983230072969 + 3 ^ 40 * 3305953 * 2
def baseEnd_3305953 : Nat := 1697542910173409177383705

theorem tailTrace_3305953 : CollatzResearch.WordTrace tailWord_3305953 prefixEnd_3305953 1697542910173409177383705 := by
  unfold tailWord_3305953
  simp only [CollatzResearch.WordTrace]
  refine ⟨120578011792104367666466513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80385341194736245110977675 120578011792104367666466513)
  ·
    refine ⟨90433508844078275749849885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120578011792104367666466513 90433508844078275749849885)
    ·
      refine ⟨33912565816529353406193707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90433508844078275749849885 33912565816529353406193707)
      ·
        refine ⟨50868848724794030109290561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33912565816529353406193707 50868848724794030109290561)
        ·
          refine ⟨38151636543595522581967921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50868848724794030109290561 38151636543595522581967921)
          ·
            refine ⟨28613727407696641936475941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38151636543595522581967921 28613727407696641936475941)
            ·
              refine ⟨5365073888943120363089239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28613727407696641936475941 5365073888943120363089239)
              ·
                refine ⟨8047610833414680544633859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365073888943120363089239 8047610833414680544633859)
                ·
                  refine ⟨12071416250122020816950789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8047610833414680544633859 12071416250122020816950789)
                  ·
                    refine ⟨2263390546897878903178273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12071416250122020816950789 2263390546897878903178273)
                    ·
                      refine ⟨1697542910173409177383705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263390546897878903178273 1697542910173409177383705)
                      ·
                        rfl

theorem cell23_3305953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_3305953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3305953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3305953 prefixEnd_3305953 := by exact prefixLift 3305953
  have htrace : WordTrace (prefixWord ++ tailWord_3305953) baseStart_3305953 baseEnd_3305953 := by
    simpa [prefixWord, tailWord_3305953, baseEnd_3305953] using wordTrace_append hprefix tailTrace_3305953
  have hstable : (prefixWord ++ tailWord_3305953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3305953).length < 2 ^ (prefixWord ++ tailWord_3305953).sum := by decide
  have hdescent : baseEnd_3305953 < baseStart_3305953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3305953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306053 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_3306053 : Nat := 118140960795 + 3306053 * 2 ^ 59
def prefixEnd_3306053 : Nat := 4983230072969 + 3 ^ 40 * 3306053 * 2
def baseEnd_3306053 : Nat := 565864752746286262044415

theorem tailTrace_3306053 : CollatzResearch.WordTrace tailWord_3306053 prefixEnd_3306053 565864752746286262044415 := by
  unfold tailWord_3306053
  simp only [CollatzResearch.WordTrace]
  refine ⟨120581659091742084745106813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80387772727828056496737875 120581659091742084745106813)
  ·
    refine ⟨45218122159403281779415055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120581659091742084745106813 45218122159403281779415055)
    ·
      refine ⟨67827183239104922669122583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45218122159403281779415055 67827183239104922669122583)
      ·
        refine ⟨101740774858657384003683875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67827183239104922669122583 101740774858657384003683875)
        ·
          refine ⟨152611162287986076005525813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101740774858657384003683875 152611162287986076005525813)
          ·
            refine ⟨14307296464498694625518045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152611162287986076005525813 14307296464498694625518045)
            ·
              refine ⟨5365236174187010484569267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14307296464498694625518045 5365236174187010484569267)
              ·
                refine ⟨8047854261280515726853901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365236174187010484569267 8047854261280515726853901)
                ·
                  refine ⟨3017945347980193397570213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8047854261280515726853901 3017945347980193397570213)
                  ·
                    refine ⟨565864752746286262044415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017945347980193397570213 565864752746286262044415)
                    ·
                      rfl

theorem cell23_3306053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_3306053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306053 prefixEnd_3306053 := by exact prefixLift 3306053
  have htrace : WordTrace (prefixWord ++ tailWord_3306053) baseStart_3306053 baseEnd_3306053 := by
    simpa [prefixWord, tailWord_3306053, baseEnd_3306053] using wordTrace_append hprefix tailTrace_3306053
  have hstable : (prefixWord ++ tailWord_3306053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306053).length < 2 ^ (prefixWord ++ tailWord_3306053).sum := by decide
  have hdescent : baseEnd_3306053 < baseStart_3306053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306144 : List Nat := [2, 1, 1, 4, 4, 1, 2, 3, 1, 1, 3]
def baseStart_3306144 : Nat := 118140960795 + 3306144 * 2 ^ 59
def prefixEnd_3306144 : Nat := 4983230072969 + 3 ^ 40 * 3306144 * 2
def baseEnd_3306144 : Nat := 1697640984978417930095327

theorem tailTrace_3306144 : CollatzResearch.WordTrace tailWord_3306144 prefixEnd_3306144 1697640984978417930095327 := by
  unfold tailWord_3306144
  simp only [CollatzResearch.WordTrace]
  refine ⟨60292489067206203643334743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80389985422941604857779657 60292489067206203643334743)
  ·
    refine ⟨90438733600809305465002115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60292489067206203643334743 90438733600809305465002115)
    ·
      refine ⟨135658100401213958197503173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90438733600809305465002115 135658100401213958197503173)
      ·
        refine ⟨25435893825227617162031845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135658100401213958197503173 25435893825227617162031845)
        ·
          refine ⟨4769230092230178217880971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25435893825227617162031845 4769230092230178217880971)
          ·
            refine ⟨7153845138345267326821457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769230092230178217880971 7153845138345267326821457)
            ·
              refine ⟨5365383853758950495116093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7153845138345267326821457 5365383853758950495116093)
              ·
                refine ⟨2012018945159606435668535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5365383853758950495116093 2012018945159606435668535)
                ·
                  refine ⟨3018028417739409653502803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012018945159606435668535 3018028417739409653502803)
                  ·
                    refine ⟨4527042626609114480254205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3018028417739409653502803 4527042626609114480254205)
                    ·
                      refine ⟨1697640984978417930095327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527042626609114480254205 1697640984978417930095327)
                      ·
                        rfl

theorem cell23_3306144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_3306144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306144 prefixEnd_3306144 := by exact prefixLift 3306144
  have htrace : WordTrace (prefixWord ++ tailWord_3306144) baseStart_3306144 baseEnd_3306144 := by
    simpa [prefixWord, tailWord_3306144, baseEnd_3306144] using wordTrace_append hprefix tailTrace_3306144
  have hstable : (prefixWord ++ tailWord_3306144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306144).length < 2 ^ (prefixWord ++ tailWord_3306144).sum := by decide
  have hdescent : baseEnd_3306144 < baseStart_3306144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306180 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3306180 : Nat := 118140960795 + 3306180 * 2 ^ 59
def prefixEnd_3306180 : Nat := 4983230072969 + 3 ^ 40 * 3306180 * 2
def baseEnd_3306180 : Nat := 1697659470281979789245161

theorem tailTrace_3306180 : CollatzResearch.WordTrace tailWord_3306180 prefixEnd_3306180 1697659470281979789245161 := by
  unfold tailWord_3306180
  simp only [CollatzResearch.WordTrace]
  refine ⟨60293145581140992717489997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80390860774854656956653329 60293145581140992717489997)
  ·
    refine ⟨22609929592927872269058749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60293145581140992717489997 22609929592927872269058749)
    ·
      refine ⟨8478723597347952100897031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22609929592927872269058749 8478723597347952100897031)
      ·
        refine ⟨12718085396021928151345547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8478723597347952100897031 12718085396021928151345547)
        ·
          refine ⟨19077128094032892227018321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12718085396021928151345547 19077128094032892227018321)
          ·
            refine ⟨14307846070524669170263741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19077128094032892227018321 14307846070524669170263741)
            ·
              refine ⟨5365442276446750938848903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14307846070524669170263741 5365442276446750938848903)
              ·
                refine ⟨8048163414670126408273355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365442276446750938848903 8048163414670126408273355)
                ·
                  refine ⟨12072245122005189612410033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048163414670126408273355 12072245122005189612410033)
                  ·
                    refine ⟨9054183841503892209307525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12072245122005189612410033 9054183841503892209307525)
                    ·
                      refine ⟨1697659470281979789245161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9054183841503892209307525 1697659470281979789245161)
                      ·
                        rfl

theorem cell23_3306180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3306180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306180 prefixEnd_3306180 := by exact prefixLift 3306180
  have htrace : WordTrace (prefixWord ++ tailWord_3306180) baseStart_3306180 baseEnd_3306180 := by
    simpa [prefixWord, tailWord_3306180, baseEnd_3306180] using wordTrace_append hprefix tailTrace_3306180
  have hstable : (prefixWord ++ tailWord_3306180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306180).length < 2 ^ (prefixWord ++ tailWord_3306180).sum := by decide
  have hdescent : baseEnd_3306180 < baseStart_3306180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306183 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_3306183 : Nat := 118140960795 + 3306183 * 2 ^ 59
def prefixEnd_3306183 : Nat := 4983230072969 + 3 ^ 40 * 3306183 * 2
def baseEnd_3306183 : Nat := 1697661010723943277507647

theorem tailTrace_3306183 : CollatzResearch.WordTrace tailWord_3306183 prefixEnd_3306183 1697661010723943277507647 := by
  unfold tailWord_3306183
  simp only [CollatzResearch.WordTrace]
  refine ⟨120586400581271116947339203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80390933720847411298226135 120586400581271116947339203)
  ·
    refine ⟨180879600871906675421008805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120586400581271116947339203 180879600871906675421008805)
    ·
      refine ⟨33914925163482501641439151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180879600871906675421008805 33914925163482501641439151)
      ·
        refine ⟨50872387745223752462158727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33914925163482501641439151 50872387745223752462158727)
        ·
          refine ⟨76308581617835628693238091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50872387745223752462158727 76308581617835628693238091)
          ·
            refine ⟨114462872426753443039857137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76308581617835628693238091 114462872426753443039857137)
            ·
              refine ⟨85847154320065082279892853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114462872426753443039857137 85847154320065082279892853)
              ·
                refine ⟨8048170717506101463739955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85847154320065082279892853 8048170717506101463739955)
                ·
                  refine ⟨12072256076259152195609933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048170717506101463739955 12072256076259152195609933)
                  ·
                    refine ⟨4527096028597182073353725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12072256076259152195609933 4527096028597182073353725)
                    ·
                      refine ⟨1697661010723943277507647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527096028597182073353725 1697661010723943277507647)
                      ·
                        rfl

theorem cell23_3306183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_3306183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306183 prefixEnd_3306183 := by exact prefixLift 3306183
  have htrace : WordTrace (prefixWord ++ tailWord_3306183) baseStart_3306183 baseEnd_3306183 := by
    simpa [prefixWord, tailWord_3306183, baseEnd_3306183] using wordTrace_append hprefix tailTrace_3306183
  have hstable : (prefixWord ++ tailWord_3306183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306183).length < 2 ^ (prefixWord ++ tailWord_3306183).sum := by decide
  have hdescent : baseEnd_3306183 < baseStart_3306183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306190 : List Nat := [4, 1, 1, 1, 3, 4, 2, 7]
def baseStart_3306190 : Nat := 118140960795 + 3306190 * 2 ^ 59
def prefixEnd_3306190 : Nat := 4983230072969 + 3 ^ 40 * 3306190 * 2
def baseEnd_3306190 : Nat := 62876466855130546300745

theorem tailTrace_3306190 : CollatzResearch.WordTrace tailWord_3306190 prefixEnd_3306190 62876466855130546300745 := by
  unfold tailWord_3306190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15073331986530719642855503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80391103928163838095229349 15073331986530719642855503)
  ·
    refine ⟨22609997979796079464283255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15073331986530719642855503 22609997979796079464283255)
    ·
      refine ⟨33914996969694119196424883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22609997979796079464283255 33914996969694119196424883)
      ·
        refine ⟨50872495454541178794637325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33914996969694119196424883 50872495454541178794637325)
        ·
          refine ⟨19077185795452942047988997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50872495454541178794637325 19077185795452942047988997)
          ·
            refine ⟨3576972336647426633997937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19077185795452942047988997 3576972336647426633997937)
            ·
              refine ⟨2682729252485569975498453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3576972336647426633997937 2682729252485569975498453)
              ·
                refine ⟨62876466855130546300745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2682729252485569975498453 62876466855130546300745)
                ·
                  rfl

theorem cell23_3306190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_3306190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306190 prefixEnd_3306190 := by exact prefixLift 3306190
  have htrace : WordTrace (prefixWord ++ tailWord_3306190) baseStart_3306190 baseEnd_3306190 := by
    simpa [prefixWord, tailWord_3306190, baseEnd_3306190] using wordTrace_append hprefix tailTrace_3306190
  have hstable : (prefixWord ++ tailWord_3306190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306190).length < 2 ^ (prefixWord ++ tailWord_3306190).sum := by decide
  have hdescent : baseEnd_3306190 < baseStart_3306190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306200 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_3306200 : Nat := 118140960795 + 3306200 * 2 ^ 59
def prefixEnd_3306200 : Nat := 4983230072969 + 3 ^ 40 * 3306200 * 2
def baseEnd_3306200 : Nat := 1697669739895069710995069

theorem tailTrace_3306200 : CollatzResearch.WordTrace tailWord_3306200 prefixEnd_3306200 1697669739895069710995069 := by
  unfold tailWord_3306200
  simp only [CollatzResearch.WordTrace]
  refine ⟨60293510311104764425354027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80391347081473019233805369 60293510311104764425354027)
  ·
    refine ⟨90440265466657146638031041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60293510311104764425354027 90440265466657146638031041)
    ·
      refine ⟨67830199099992859978523281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90440265466657146638031041 67830199099992859978523281)
      ·
        refine ⟨50872649324994644983892461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67830199099992859978523281 50872649324994644983892461)
        ·
          refine ⟨19077243496872991868959673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50872649324994644983892461 19077243496872991868959673)
          ·
            refine ⟨14307932622654743901719755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19077243496872991868959673 14307932622654743901719755)
            ·
              refine ⟨21461898933982115852579633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14307932622654743901719755 21461898933982115852579633)
              ·
                refine ⟨16096424200486586889434725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21461898933982115852579633 16096424200486586889434725)
                ·
                  refine ⟨3018079537591235041769011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16096424200486586889434725 3018079537591235041769011)
                  ·
                    refine ⟨4527119306386852562653517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3018079537591235041769011 4527119306386852562653517)
                    ·
                      refine ⟨1697669739895069710995069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527119306386852562653517 1697669739895069710995069)
                      ·
                        rfl

theorem cell23_3306200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_3306200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306200 prefixEnd_3306200 := by exact prefixLift 3306200
  have htrace : WordTrace (prefixWord ++ tailWord_3306200) baseStart_3306200 baseEnd_3306200 := by
    simpa [prefixWord, tailWord_3306200, baseEnd_3306200] using wordTrace_append hprefix tailTrace_3306200
  have hstable : (prefixWord ++ tailWord_3306200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306200).length < 2 ^ (prefixWord ++ tailWord_3306200).sum := by decide
  have hdescent : baseEnd_3306200 < baseStart_3306200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306228 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3306228 : Nat := 118140960795 + 3306228 * 2 ^ 59
def prefixEnd_3306228 : Nat := 4983230072969 + 3 ^ 40 * 3306228 * 2
def baseEnd_3306228 : Nat := 565894705784465200481647

theorem tailTrace_3306228 : CollatzResearch.WordTrace tailWord_3306228 prefixEnd_3306228 565894705784465200481647 := by
  unfold tailWord_3306228
  simp only [CollatzResearch.WordTrace]
  refine ⟨60294020933054044816363669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80392027910738726421818225 60294020933054044816363669)
  ·
    refine ⟨2826282231236908350767047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60294020933054044816363669 2826282231236908350767047)
    ·
      refine ⟨4239423346855362526150571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826282231236908350767047 4239423346855362526150571)
      ·
        refine ⟨6359135020283043789225857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239423346855362526150571 6359135020283043789225857)
        ·
          refine ⟨4769351265212282841919393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6359135020283043789225857 4769351265212282841919393)
          ·
            refine ⟨3577013448909212131439545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4769351265212282841919393 3577013448909212131439545)
            ·
              refine ⟨2682760086681909098579659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577013448909212131439545 2682760086681909098579659)
              ·
                refine ⟨4024140130022863647869489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682760086681909098579659 4024140130022863647869489)
                ·
                  refine ⟨3018105097517147735902117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024140130022863647869489 3018105097517147735902117)
                  ·
                    refine ⟨565894705784465200481647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018105097517147735902117 565894705784465200481647)
                    ·
                      rfl

theorem cell23_3306228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3306228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306228 prefixEnd_3306228 := by exact prefixLift 3306228
  have htrace : WordTrace (prefixWord ++ tailWord_3306228) baseStart_3306228 baseEnd_3306228 := by
    simpa [prefixWord, tailWord_3306228, baseEnd_3306228] using wordTrace_append hprefix tailTrace_3306228
  have hstable : (prefixWord ++ tailWord_3306228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306228).length < 2 ^ (prefixWord ++ tailWord_3306228).sum := by decide
  have hdescent : baseEnd_3306228 < baseStart_3306228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306274 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_3306274 : Nat := 118140960795 + 3306274 * 2 ^ 59
def prefixEnd_3306274 : Nat := 4983230072969 + 3 ^ 40 * 3306274 * 2
def baseEnd_3306274 : Nat := 1697707737463502421469729

theorem tailTrace_3306274 : CollatzResearch.WordTrace tailWord_3306274 prefixEnd_3306274 1697707737463502421469729 := by
  unfold tailWord_3306274
  simp only [CollatzResearch.WordTrace]
  refine ⟨30147429905985359872225469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80393146415960959659267917 30147429905985359872225469)
  ·
    refine ⟨11305286214744509952084551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30147429905985359872225469 11305286214744509952084551)
    ·
      refine ⟨16957929322116764928126827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11305286214744509952084551 16957929322116764928126827)
      ·
        refine ⟨25436893983175147392190241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16957929322116764928126827 25436893983175147392190241)
        ·
          refine ⟨19077670487381360544142681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25436893983175147392190241 19077670487381360544142681)
          ·
            refine ⟨14308252865536020408107011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19077670487381360544142681 14308252865536020408107011)
            ·
              refine ⟨21462379298304030612160517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14308252865536020408107011 21462379298304030612160517)
              ·
                refine ⟨4024196118432005739780097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21462379298304030612160517 4024196118432005739780097)
                ·
                  refine ⟨3018147088824004304835073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024196118432005739780097 3018147088824004304835073)
                  ·
                    refine ⟨2263610316618003228626305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018147088824004304835073 2263610316618003228626305)
                    ·
                      refine ⟨1697707737463502421469729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263610316618003228626305 1697707737463502421469729)
                      ·
                        rfl

theorem cell23_3306274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_3306274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306274 prefixEnd_3306274 := by exact prefixLift 3306274
  have htrace : WordTrace (prefixWord ++ tailWord_3306274) baseStart_3306274 baseEnd_3306274 := by
    simpa [prefixWord, tailWord_3306274, baseEnd_3306274] using wordTrace_append hprefix tailTrace_3306274
  have hstable : (prefixWord ++ tailWord_3306274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306274).length < 2 ^ (prefixWord ++ tailWord_3306274).sum := by decide
  have hdescent : baseEnd_3306274 < baseStart_3306274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306290 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_3306290 : Nat := 118140960795 + 3306290 * 2 ^ 59
def prefixEnd_3306290 : Nat := 4983230072969 + 3 ^ 40 * 3306290 * 2
def baseEnd_3306290 : Nat := 1697715953153974358869655

theorem tailTrace_3306290 : CollatzResearch.WordTrace tailWord_3306290 prefixEnd_3306290 1697715953153974358869655 := by
  unfold tailWord_3306290
  simp only [CollatzResearch.WordTrace]
  refine ⟨30147575797970868555371081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80393535461255649480989549 30147575797970868555371081)
  ·
    refine ⟨22610681848478151416528311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30147575797970868555371081 22610681848478151416528311)
    ·
      refine ⟨33916022772717227124792467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22610681848478151416528311 33916022772717227124792467)
      ·
        refine ⟨50874034159075840687188701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33916022772717227124792467 50874034159075840687188701)
        ·
          refine ⟨19077762809653440257695763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50874034159075840687188701 19077762809653440257695763)
          ·
            refine ⟨28616644214480160386543645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19077762809653440257695763 28616644214480160386543645)
            ·
              refine ⟨10731241580430060144953867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28616644214480160386543645 10731241580430060144953867)
              ·
                refine ⟨16096862370645090217430801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10731241580430060144953867 16096862370645090217430801)
                ·
                  refine ⟨12072646777983817663073101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16096862370645090217430801 12072646777983817663073101)
                  ·
                    refine ⟨4527242541743931623652413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12072646777983817663073101 4527242541743931623652413)
                    ·
                      refine ⟨1697715953153974358869655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527242541743931623652413 1697715953153974358869655)
                      ·
                        rfl

theorem cell23_3306290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_3306290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306290 prefixEnd_3306290 := by exact prefixLift 3306290
  have htrace : WordTrace (prefixWord ++ tailWord_3306290) baseStart_3306290 baseEnd_3306290 := by
    simpa [prefixWord, tailWord_3306290, baseEnd_3306290] using wordTrace_append hprefix tailTrace_3306290
  have hstable : (prefixWord ++ tailWord_3306290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306290).length < 2 ^ (prefixWord ++ tailWord_3306290).sum := by decide
  have hdescent : baseEnd_3306290 < baseStart_3306290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306300 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_3306300 : Nat := 118140960795 + 3306300 * 2 ^ 59
def prefixEnd_3306300 : Nat := 4983230072969 + 3 ^ 40 * 3306300 * 2
def baseEnd_3306300 : Nat := 1697721087960519319744609

theorem tailTrace_3306300 : CollatzResearch.WordTrace tailWord_3306300 prefixEnd_3306300 1697721087960519319744609 := by
  unfold tailWord_3306300
  simp only [CollatzResearch.WordTrace]
  refine ⟨60295333960923622964674177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80393778614564830619565569 60295333960923622964674177)
  ·
    refine ⟨45221500470692717223505633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60295333960923622964674177 45221500470692717223505633)
    ·
      refine ⟨33916125353019537917629225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45221500470692717223505633 33916125353019537917629225)
      ·
        refine ⟨25437094014764653438221919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33916125353019537917629225 25437094014764653438221919)
        ·
          refine ⟨38155641022146980157332879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25437094014764653438221919 38155641022146980157332879)
          ·
            refine ⟨57233461533220470235999319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38155641022146980157332879 57233461533220470235999319)
            ·
              refine ⟨85850192299830705353998979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57233461533220470235999319 85850192299830705353998979)
              ·
                refine ⟨128775288449746058030998469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85850192299830705353998979 128775288449746058030998469)
                ·
                  refine ⟨24145366584327385880812213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128775288449746058030998469 24145366584327385880812213)
                  ·
                    refine ⟨2263628117280692426326145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24145366584327385880812213 2263628117280692426326145)
                    ·
                      refine ⟨1697721087960519319744609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263628117280692426326145 1697721087960519319744609)
                      ·
                        rfl

theorem cell23_3306300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_3306300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306300 prefixEnd_3306300 := by exact prefixLift 3306300
  have htrace : WordTrace (prefixWord ++ tailWord_3306300) baseStart_3306300 baseEnd_3306300 := by
    simpa [prefixWord, tailWord_3306300, baseEnd_3306300] using wordTrace_append hprefix tailTrace_3306300
  have hstable : (prefixWord ++ tailWord_3306300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306300).length < 2 ^ (prefixWord ++ tailWord_3306300).sum := by decide
  have hdescent : baseEnd_3306300 < baseStart_3306300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306357 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3306357 : Nat := 118140960795 + 3306357 * 2 ^ 59
def prefixEnd_3306357 : Nat := 4983230072969 + 3 ^ 40 * 3306357 * 2
def baseEnd_3306357 : Nat := 565916785452608532243949

theorem tailTrace_3306357 : CollatzResearch.WordTrace tailWord_3306357 prefixEnd_3306357 565916785452608532243949 := by
  unfold tailWord_3306357
  simp only [CollatzResearch.WordTrace]
  refine ⟨120592746882640744664173325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80395164588427163109448883 120592746882640744664173325)
  ·
    refine ⟨45222280080990279249064997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120592746882640744664173325 45222280080990279249064997)
    ·
      refine ⟨8479177515185677359199687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45222280080990279249064997 8479177515185677359199687)
      ·
        refine ⟨12718766272778516038799531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479177515185677359199687 12718766272778516038799531)
        ·
          refine ⟨19078149409167774058199297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12718766272778516038799531 19078149409167774058199297)
          ·
            refine ⟨14308612056875830543649473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19078149409167774058199297 14308612056875830543649473)
            ·
              refine ⟨10731459042656872907737105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14308612056875830543649473 10731459042656872907737105)
              ·
                refine ⟨8048594281992654680802829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10731459042656872907737105 8048594281992654680802829)
                ·
                  refine ⟨3018222855747245505301061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8048594281992654680802829 3018222855747245505301061)
                  ·
                    refine ⟨565916785452608532243949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018222855747245505301061 565916785452608532243949)
                    ·
                      rfl

theorem cell23_3306357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3306357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306357 prefixEnd_3306357 := by exact prefixLift 3306357
  have htrace : WordTrace (prefixWord ++ tailWord_3306357) baseStart_3306357 baseEnd_3306357 := by
    simpa [prefixWord, tailWord_3306357, baseEnd_3306357] using wordTrace_append hprefix tailTrace_3306357
  have hstable : (prefixWord ++ tailWord_3306357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306357).length < 2 ^ (prefixWord ++ tailWord_3306357).sum := by decide
  have hdescent : baseEnd_3306357 < baseStart_3306357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306393 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3306393 : Nat := 118140960795 + 3306393 * 2 ^ 59
def prefixEnd_3306393 : Nat := 4983230072969 + 3 ^ 40 * 3306393 * 2
def baseEnd_3306393 : Nat := 1697768841661387455881681

theorem tailTrace_3306393 : CollatzResearch.WordTrace tailWord_3306393 prefixEnd_3306393 1697768841661387455881681 := by
  unfold tailWord_3306393
  simp only [CollatzResearch.WordTrace]
  refine ⟨120594059910510322812483833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80396039940340215208322555 120594059910510322812483833)
  ·
    refine ⟨90445544932882742109362875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120594059910510322812483833 90445544932882742109362875)
    ·
      refine ⟨135668317399324113164044313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90445544932882742109362875 135668317399324113164044313)
      ·
        refine ⟨101751238049493084873033235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135668317399324113164044313 101751238049493084873033235)
        ·
          refine ⟨152626857074239627309549853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101751238049493084873033235 152626857074239627309549853)
          ·
            refine ⟨57235071402839860241081195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152626857074239627309549853 57235071402839860241081195)
            ·
              refine ⟨85852607104259790361621793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57235071402839860241081195 85852607104259790361621793)
              ·
                refine ⟨64389455328194842771216345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85852607104259790361621793 64389455328194842771216345)
                ·
                  refine ⟨48292091496146132078412259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64389455328194842771216345 48292091496146132078412259)
                  ·
                    refine ⟨72438137244219198117618389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48292091496146132078412259 72438137244219198117618389)
                    ·
                      refine ⟨1697768841661387455881681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72438137244219198117618389 1697768841661387455881681)
                      ·
                        rfl

theorem cell23_3306393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3306393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306393 prefixEnd_3306393 := by exact prefixLift 3306393
  have htrace : WordTrace (prefixWord ++ tailWord_3306393) baseStart_3306393 baseEnd_3306393 := by
    simpa [prefixWord, tailWord_3306393, baseEnd_3306393] using wordTrace_append hprefix tailTrace_3306393
  have hstable : (prefixWord ++ tailWord_3306393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306393).length < 2 ^ (prefixWord ++ tailWord_3306393).sum := by decide
  have hdescent : baseEnd_3306393 < baseStart_3306393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306417 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 3, 5]
def baseStart_3306417 : Nat := 118140960795 + 3306417 * 2 ^ 59
def prefixEnd_3306417 : Nat := 4983230072969 + 3 ^ 40 * 3306417 * 2
def baseEnd_3306417 : Nat := 565927055065698453993857

theorem tailTrace_3306417 : CollatzResearch.WordTrace tailWord_3306417 prefixEnd_3306417 565927055065698453993857 := by
  unfold tailWord_3306417
  simp only [CollatzResearch.WordTrace]
  refine ⟨120594935262423374911357505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80396623508282249940905003 120594935262423374911357505)
  ·
    refine ⟨90446201446817531183518129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120594935262423374911357505 90446201446817531183518129)
    ·
      refine ⟨67834651085113148387638597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90446201446817531183518129 67834651085113148387638597)
      ·
        refine ⟨12718997078458715322682237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67834651085113148387638597 12718997078458715322682237)
        ·
          refine ⟨4769623904422018246005839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12718997078458715322682237 4769623904422018246005839)
          ·
            refine ⟨7154435856633027369008759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769623904422018246005839 7154435856633027369008759)
            ·
              refine ⟨10731653784949541053513139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154435856633027369008759 10731653784949541053513139)
              ·
                refine ⟨16097480677424311580269709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10731653784949541053513139 16097480677424311580269709)
                ·
                  refine ⟨6036555254034116842601141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16097480677424311580269709 6036555254034116842601141)
                  ·
                    refine ⟨565927055065698453993857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6036555254034116842601141 565927055065698453993857)
                    ·
                      rfl

theorem cell23_3306417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_3306417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306417 prefixEnd_3306417 := by exact prefixLift 3306417
  have htrace : WordTrace (prefixWord ++ tailWord_3306417) baseStart_3306417 baseEnd_3306417 := by
    simpa [prefixWord, tailWord_3306417, baseEnd_3306417] using wordTrace_append hprefix tailTrace_3306417
  have hstable : (prefixWord ++ tailWord_3306417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306417).length < 2 ^ (prefixWord ++ tailWord_3306417).sum := by decide
  have hdescent : baseEnd_3306417 < baseStart_3306417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306424 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 2, 3, 2]
def baseStart_3306424 : Nat := 118140960795 + 3306424 * 2 ^ 59
def prefixEnd_3306424 : Nat := 4983230072969 + 3 ^ 40 * 3306424 * 2
def baseEnd_3306424 : Nat := 1697784759561676834594039

theorem tailTrace_3306424 : CollatzResearch.WordTrace tailWord_3306424 prefixEnd_3306424 1697784759561676834594039 := by
  unfold tailWord_3306424
  simp only [CollatzResearch.WordTrace]
  refine ⟨60297595286699007553431163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80396793715598676737908217 60297595286699007553431163)
  ·
    refine ⟨90446392930048511330146745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60297595286699007553431163 90446392930048511330146745)
    ·
      refine ⟨67834794697536383497610059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90446392930048511330146745 67834794697536383497610059)
      ·
        refine ⟨101752192046304575246415089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67834794697536383497610059 101752192046304575246415089)
        ·
          refine ⟨76314144034728431434811317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101752192046304575246415089 76314144034728431434811317)
          ·
            refine ⟨7154451003255790447013561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76314144034728431434811317 7154451003255790447013561)
            ·
              refine ⟨5365838252441842835260171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7154451003255790447013561 5365838252441842835260171)
              ·
                refine ⟨8048757378662764252890257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365838252441842835260171 8048757378662764252890257)
                ·
                  refine ⟨6036568033997073189667693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8048757378662764252890257 6036568033997073189667693)
                  ·
                    refine ⟨2263713012748902446125385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6036568033997073189667693 2263713012748902446125385)
                    ·
                      refine ⟨1697784759561676834594039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263713012748902446125385 1697784759561676834594039)
                      ·
                        rfl

theorem cell23_3306424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_3306424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306424 prefixEnd_3306424 := by exact prefixLift 3306424
  have htrace : WordTrace (prefixWord ++ tailWord_3306424) baseStart_3306424 baseEnd_3306424 := by
    simpa [prefixWord, tailWord_3306424, baseEnd_3306424] using wordTrace_append hprefix tailTrace_3306424
  have hstable : (prefixWord ++ tailWord_3306424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306424).length < 2 ^ (prefixWord ++ tailWord_3306424).sum := by decide
  have hdescent : baseEnd_3306424 < baseStart_3306424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306443 : List Nat := [1, 1, 1, 1, 3, 16]
def baseStart_3306443 : Nat := 118140960795 + 3306443 * 2 ^ 59
def prefixEnd_3306443 : Nat := 4983230072969 + 3 ^ 40 * 3306443 * 2
def baseEnd_3306443 : Nat := 6986808706560132758257

theorem tailTrace_3306443 : CollatzResearch.WordTrace tailWord_3306443 prefixEnd_3306443 6986808706560132758257 := by
  unfold tailWord_3306443
  simp only [CollatzResearch.WordTrace]
  refine ⟨120595883560329181351803983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80397255706886120901202655 120595883560329181351803983)
  ·
    refine ⟨180893825340493772027705975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120595883560329181351803983 180893825340493772027705975)
    ·
      refine ⟨271340738010740658041558963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180893825340493772027705975 271340738010740658041558963)
      ·
        refine ⟨407011107016110987062338445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271340738010740658041558963 407011107016110987062338445)
        ·
          refine ⟨152629165131041620148376917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407011107016110987062338445 152629165131041620148376917)
          ·
            refine ⟨6986808706560132758257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 152629165131041620148376917 6986808706560132758257)
            ·
              rfl

theorem cell23_3306443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 16].length) (baseStart_3306443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306443 prefixEnd_3306443 := by exact prefixLift 3306443
  have htrace : WordTrace (prefixWord ++ tailWord_3306443) baseStart_3306443 baseEnd_3306443 := by
    simpa [prefixWord, tailWord_3306443, baseEnd_3306443] using wordTrace_append hprefix tailTrace_3306443
  have hstable : (prefixWord ++ tailWord_3306443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306443).length < 2 ^ (prefixWord ++ tailWord_3306443).sum := by decide
  have hdescent : baseEnd_3306443 < baseStart_3306443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306447 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 2, 4]
def baseStart_3306447 : Nat := 118140960795 + 3306447 * 2 ^ 59
def prefixEnd_3306447 : Nat := 4983230072969 + 3 ^ 40 * 3306447 * 2
def baseEnd_3306447 : Nat := 565932189872243414868811

theorem tailTrace_3306447 : CollatzResearch.WordTrace tailWord_3306447 prefixEnd_3306447 565932189872243414868811 := by
  unfold tailWord_3306447
  simp only [CollatzResearch.WordTrace]
  refine ⟨120596029452314690034949595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80397352968209793356633063 120596029452314690034949595)
  ·
    refine ⟨180894044178472035052424393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120596029452314690034949595 180894044178472035052424393)
    ·
      refine ⟨135670533133854026289318295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180894044178472035052424393 135670533133854026289318295)
      ·
        refine ⟨203505799700781039433977443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135670533133854026289318295 203505799700781039433977443)
        ·
          refine ⟨305258699551171559150966165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203505799700781039433977443 305258699551171559150966165)
          ·
            refine ⟨14309001541461166835201539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 305258699551171559150966165 14309001541461166835201539)
            ·
              refine ⟨21463502312191750252802309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309001541461166835201539 21463502312191750252802309)
              ·
                refine ⟨4024406683535953172400433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21463502312191750252802309 4024406683535953172400433)
                ·
                  refine ⟨3018305012651964879300325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024406683535953172400433 3018305012651964879300325)
                  ·
                    refine ⟨565932189872243414868811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018305012651964879300325 565932189872243414868811)
                    ·
                      rfl

theorem cell23_3306447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_3306447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306447 prefixEnd_3306447 := by exact prefixLift 3306447
  have htrace : WordTrace (prefixWord ++ tailWord_3306447) baseStart_3306447 baseEnd_3306447 := by
    simpa [prefixWord, tailWord_3306447, baseEnd_3306447] using wordTrace_append hprefix tailTrace_3306447
  have hstable : (prefixWord ++ tailWord_3306447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306447).length < 2 ^ (prefixWord ++ tailWord_3306447).sum := by decide
  have hdescent : baseEnd_3306447 < baseStart_3306447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306454 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3306454 : Nat := 118140960795 + 3306454 * 2 ^ 59
def prefixEnd_3306454 : Nat := 4983230072969 + 3 ^ 40 * 3306454 * 2
def baseEnd_3306454 : Nat := 1697800163981311717218901

theorem tailTrace_3306454 : CollatzResearch.WordTrace tailWord_3306454 prefixEnd_3306454 1697800163981311717218901 := by
  unfold tailWord_3306454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537267797705583139403401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80397523175526220153636277 7537267797705583139403401)
  ·
    refine ⟨5652950848279187354552551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7537267797705583139403401 5652950848279187354552551)
    ·
      refine ⟨8479426272418781031828827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5652950848279187354552551 8479426272418781031828827)
      ·
        refine ⟨12719139408628171547743241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479426272418781031828827 12719139408628171547743241)
        ·
          refine ⟨9539354556471128660807431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719139408628171547743241 9539354556471128660807431)
          ·
            refine ⟨14309031834706692991211147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539354556471128660807431 14309031834706692991211147)
            ·
              refine ⟨21463547752060039486816721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309031834706692991211147 21463547752060039486816721)
              ·
                refine ⟨16097660814045029615112541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21463547752060039486816721 16097660814045029615112541)
                ·
                  refine ⟨6036622805266886105667203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16097660814045029615112541 6036622805266886105667203)
                  ·
                    refine ⟨9054934207900329158500805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6036622805266886105667203 9054934207900329158500805)
                    ·
                      refine ⟨1697800163981311717218901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9054934207900329158500805 1697800163981311717218901)
                      ·
                        rfl

theorem cell23_3306454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3306454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306454 prefixEnd_3306454 := by exact prefixLift 3306454
  have htrace : WordTrace (prefixWord ++ tailWord_3306454) baseStart_3306454 baseEnd_3306454 := by
    simpa [prefixWord, tailWord_3306454, baseEnd_3306454] using wordTrace_append hprefix tailTrace_3306454
  have hstable : (prefixWord ++ tailWord_3306454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306454).length < 2 ^ (prefixWord ++ tailWord_3306454).sum := by decide
  have hdescent : baseEnd_3306454 < baseStart_3306454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306457 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 3]
def baseStart_3306457 : Nat := 118140960795 + 3306457 * 2 ^ 59
def prefixEnd_3306457 : Nat := 4983230072969 + 3 ^ 40 * 3306457 * 2
def baseEnd_3306457 : Nat := 1697801704423275205481387

theorem tailTrace_3306457 : CollatzResearch.WordTrace tailWord_3306457 prefixEnd_3306457 1697801704423275205481387 := by
  unfold tailWord_3306457
  simp only [CollatzResearch.WordTrace]
  refine ⟨120596394182278461742813625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80397596121518974495209083 120596394182278461742813625)
  ·
    refine ⟨90447295636708846307110219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120596394182278461742813625 90447295636708846307110219)
    ·
      refine ⟨135670943455063269460665329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90447295636708846307110219 135670943455063269460665329)
      ·
        refine ⟨101753207591297452095498997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135670943455063269460665329 101753207591297452095498997)
        ·
          refine ⟨9539363211684136133953031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101753207591297452095498997 9539363211684136133953031)
          ·
            refine ⟨14309044817526204200929547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539363211684136133953031 14309044817526204200929547)
            ·
              refine ⟨21463567226289306301394321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309044817526204200929547 21463567226289306301394321)
              ·
                refine ⟨16097675419716979726045741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21463567226289306301394321 16097675419716979726045741)
                ·
                  refine ⟨6036628282393867397267153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16097675419716979726045741 6036628282393867397267153)
                  ·
                    refine ⟨4527471211795400547950365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6036628282393867397267153 4527471211795400547950365)
                    ·
                      refine ⟨1697801704423275205481387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527471211795400547950365 1697801704423275205481387)
                      ·
                        rfl

theorem cell23_3306457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_3306457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306457 prefixEnd_3306457 := by exact prefixLift 3306457
  have htrace : WordTrace (prefixWord ++ tailWord_3306457) baseStart_3306457 baseEnd_3306457 := by
    simpa [prefixWord, tailWord_3306457, baseEnd_3306457] using wordTrace_append hprefix tailTrace_3306457
  have hstable : (prefixWord ++ tailWord_3306457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306457).length < 2 ^ (prefixWord ++ tailWord_3306457).sum := by decide
  have hdescent : baseEnd_3306457 < baseStart_3306457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306467 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3306467 : Nat := 118140960795 + 3306467 * 2 ^ 59
def prefixEnd_3306467 : Nat := 4983230072969 + 3 ^ 40 * 3306467 * 2
def baseEnd_3306467 : Nat := 1697806839229820166356341

theorem tailTrace_3306467 : CollatzResearch.WordTrace tailWord_3306467 prefixEnd_3306467 1697806839229820166356341 := by
  unfold tailWord_3306467
  simp only [CollatzResearch.WordTrace]
  refine ⟨120596758912242233450677655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80397839274828155633785103 120596758912242233450677655)
  ·
    refine ⟨180895138368363350176016483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120596758912242233450677655 180895138368363350176016483)
    ·
      refine ⟨271342707552545025264024725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180895138368363350176016483 271342707552545025264024725)
      ·
        refine ⟨12719189416525548059251159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 271342707552545025264024725 12719189416525548059251159)
        ·
          refine ⟨19078784124788322088876739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12719189416525548059251159 19078784124788322088876739)
          ·
            refine ⟨28618176187182483133315109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19078784124788322088876739 28618176187182483133315109)
            ·
              refine ⟨5365908035096715587496583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28618176187182483133315109 5365908035096715587496583)
              ·
                refine ⟨8048862052645073381244875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365908035096715587496583 8048862052645073381244875)
                ·
                  refine ⟨12073293078967610071867313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048862052645073381244875 12073293078967610071867313)
                  ·
                    refine ⟨9054969809225707553900485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12073293078967610071867313 9054969809225707553900485)
                    ·
                      refine ⟨1697806839229820166356341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9054969809225707553900485 1697806839229820166356341)
                      ·
                        rfl

theorem cell23_3306467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3306467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306467 prefixEnd_3306467 := by exact prefixLift 3306467
  have htrace : WordTrace (prefixWord ++ tailWord_3306467) baseStart_3306467 baseEnd_3306467 := by
    simpa [prefixWord, tailWord_3306467, baseEnd_3306467] using wordTrace_append hprefix tailTrace_3306467
  have hstable : (prefixWord ++ tailWord_3306467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306467).length < 2 ^ (prefixWord ++ tailWord_3306467).sum := by decide
  have hdescent : baseEnd_3306467 < baseStart_3306467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306471 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3306471 : Nat := 118140960795 + 3306471 * 2 ^ 59
def prefixEnd_3306471 : Nat := 4983230072969 + 3 ^ 40 * 3306471 * 2
def baseEnd_3306471 : Nat := 1697808893152438150706323

theorem tailTrace_3306471 : CollatzResearch.WordTrace tailWord_3306471 prefixEnd_3306471 1697808893152438150706323 := by
  unfold tailWord_3306471
  simp only [CollatzResearch.WordTrace]
  refine ⟨120596904804227742133823267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80397936536151828089215511 120596904804227742133823267)
  ·
    refine ⟨180895357206341613200734901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120596904804227742133823267 180895357206341613200734901)
    ·
      refine ⟨16958939738094526237568897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180895357206341613200734901 16958939738094526237568897)
      ·
        refine ⟨12719204803570894678176673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16958939738094526237568897 12719204803570894678176673)
        ·
          refine ⟨9539403602678171008632505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719204803570894678176673 9539403602678171008632505)
          ·
            refine ⟨7154552702008628256474379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9539403602678171008632505 7154552702008628256474379)
            ·
              refine ⟨10731829053012942384711569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154552702008628256474379 10731829053012942384711569)
              ·
                refine ⟨8048871789759706788533677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10731829053012942384711569 8048871789759706788533677)
                ·
                  refine ⟨3018326921159890045700129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8048871789759706788533677 3018326921159890045700129)
                  ·
                    refine ⟨2263745190869917534275097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018326921159890045700129 2263745190869917534275097)
                    ·
                      refine ⟨1697808893152438150706323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263745190869917534275097 1697808893152438150706323)
                      ·
                        rfl

theorem cell23_3306471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3306471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306471 prefixEnd_3306471 := by exact prefixLift 3306471
  have htrace : WordTrace (prefixWord ++ tailWord_3306471) baseStart_3306471 baseEnd_3306471 := by
    simpa [prefixWord, tailWord_3306471, baseEnd_3306471] using wordTrace_append hprefix tailTrace_3306471
  have hstable : (prefixWord ++ tailWord_3306471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306471).length < 2 ^ (prefixWord ++ tailWord_3306471).sum := by decide
  have hdescent : baseEnd_3306471 < baseStart_3306471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306485 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3306485 : Nat := 118140960795 + 3306485 * 2 ^ 59
def prefixEnd_3306485 : Nat := 4983230072969 + 3 ^ 40 * 3306485 * 2
def baseEnd_3306485 : Nat := 565938693960533698643753

theorem tailTrace_3306485 : CollatzResearch.WordTrace tailWord_3306485 prefixEnd_3306485 565938693960533698643753 := by
  unfold tailWord_3306485
  simp only [CollatzResearch.WordTrace]
  refine ⟨120597415426177022524832909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80398276950784681683221939 120597415426177022524832909)
  ·
    refine ⟨45224030784816383446812341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120597415426177022524832909 45224030784816383446812341)
    ·
      refine ⟨4239752886076535948138657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45224030784816383446812341 4239752886076535948138657)
      ·
        refine ⟨3179814664557401961103993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4239752886076535948138657 3179814664557401961103993)
        ·
          refine ⟨2384860998418051470827995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3179814664557401961103993 2384860998418051470827995)
          ·
            refine ⟨3577291497627077206241993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384860998418051470827995 3577291497627077206241993)
            ·
              refine ⟨2682968623220307904681495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577291497627077206241993 2682968623220307904681495)
              ·
                refine ⟨4024452934830461857022243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682968623220307904681495 4024452934830461857022243)
                ·
                  refine ⟨6036679402245692785533365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024452934830461857022243 6036679402245692785533365)
                  ·
                    refine ⟨565938693960533698643753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6036679402245692785533365 565938693960533698643753)
                    ·
                      rfl

theorem cell23_3306485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3306485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306485 prefixEnd_3306485 := by exact prefixLift 3306485
  have htrace : WordTrace (prefixWord ++ tailWord_3306485) baseStart_3306485 baseEnd_3306485 := by
    simpa [prefixWord, tailWord_3306485, baseEnd_3306485] using wordTrace_append hprefix tailTrace_3306485
  have hstable : (prefixWord ++ tailWord_3306485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306485).length < 2 ^ (prefixWord ++ tailWord_3306485).sum := by decide
  have hdescent : baseEnd_3306485 < baseStart_3306485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306504 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3306504 : Nat := 118140960795 + 3306504 * 2 ^ 59
def prefixEnd_3306504 : Nat := 4983230072969 + 3 ^ 40 * 3306504 * 2
def baseEnd_3306504 : Nat := 1697825838014036521593671

theorem tailTrace_3306504 : CollatzResearch.WordTrace tailWord_3306504 prefixEnd_3306504 1697825838014036521593671 := by
  unfold tailWord_3306504
  simp only [CollatzResearch.WordTrace]
  refine ⟨60299054206554094384887283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80398738942072125846516377 60299054206554094384887283)
  ·
    refine ⟨90448581309831141577330925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60299054206554094384887283 90448581309831141577330925)
    ·
      refine ⟨33918217991186678091499097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90448581309831141577330925 33918217991186678091499097)
      ·
        refine ⟨25438663493390008568624323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33918217991186678091499097 25438663493390008568624323)
        ·
          refine ⟨38157995240085012852936485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25438663493390008568624323 38157995240085012852936485)
          ·
            refine ⟨7154624107515939909925591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38157995240085012852936485 7154624107515939909925591)
            ·
              refine ⟨10731936161273909864888387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154624107515939909925591 10731936161273909864888387)
              ·
                refine ⟨16097904241910864797332581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10731936161273909864888387 16097904241910864797332581)
                ·
                  refine ⟨3018357045358287149499859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16097904241910864797332581 3018357045358287149499859)
                  ·
                    refine ⟨4527535568037430724249789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3018357045358287149499859 4527535568037430724249789)
                    ·
                      refine ⟨1697825838014036521593671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527535568037430724249789 1697825838014036521593671)
                      ·
                        rfl

theorem cell23_3306504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3306504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306504 prefixEnd_3306504 := by exact prefixLift 3306504
  have htrace : WordTrace (prefixWord ++ tailWord_3306504) baseStart_3306504 baseEnd_3306504 := by
    simpa [prefixWord, tailWord_3306504, baseEnd_3306504] using wordTrace_append hprefix tailTrace_3306504
  have hstable : (prefixWord ++ tailWord_3306504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306504).length < 2 ^ (prefixWord ++ tailWord_3306504).sum := by decide
  have hdescent : baseEnd_3306504 < baseStart_3306504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306531 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 1, 3, 2]
def baseStart_3306531 : Nat := 118140960795 + 3306531 * 2 ^ 59
def prefixEnd_3306531 : Nat := 4983230072969 + 3 ^ 40 * 3306531 * 2
def baseEnd_3306531 : Nat := 1697839701991707915956047

theorem tailTrace_3306531 : CollatzResearch.WordTrace tailWord_3306531 prefixEnd_3306531 1697839701991707915956047 := by
  unfold tailWord_3306531
  simp only [CollatzResearch.WordTrace]
  refine ⟨120599093184010372381007447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80399395456006914920671631 120599093184010372381007447)
  ·
    refine ⟨180898639776015558571511171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120599093184010372381007447 180898639776015558571511171)
    ·
      refine ⟨271347959664023337857266757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180898639776015558571511171 271347959664023337857266757)
      ·
        refine ⟨50877742437004375848237517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271347959664023337857266757 50877742437004375848237517)
        ·
          refine ⟨19079153413876640943089069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50877742437004375848237517 19079153413876640943089069)
          ·
            refine ⟨7154682530203740353658401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19079153413876640943089069 7154682530203740353658401)
            ·
              refine ⟨5366011897652805265243801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7154682530203740353658401 5366011897652805265243801)
              ·
                refine ⟨4024508923239603948932851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366011897652805265243801 4024508923239603948932851)
                ·
                  refine ⟨6036763384859405923399277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024508923239603948932851 6036763384859405923399277)
                  ·
                    refine ⟨2263786269322277221274729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6036763384859405923399277 2263786269322277221274729)
                    ·
                      refine ⟨1697839701991707915956047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263786269322277221274729 1697839701991707915956047)
                      ·
                        rfl

theorem cell23_3306531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_3306531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306531 prefixEnd_3306531 := by exact prefixLift 3306531
  have htrace : WordTrace (prefixWord ++ tailWord_3306531) baseStart_3306531 baseEnd_3306531 := by
    simpa [prefixWord, tailWord_3306531, baseEnd_3306531] using wordTrace_append hprefix tailTrace_3306531
  have hstable : (prefixWord ++ tailWord_3306531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306531).length < 2 ^ (prefixWord ++ tailWord_3306531).sum := by decide
  have hdescent : baseEnd_3306531 < baseStart_3306531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306544 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 6, 2, 2]
def baseStart_3306544 : Nat := 118140960795 + 3306544 * 2 ^ 59
def prefixEnd_3306544 : Nat := 4983230072969 + 3 ^ 40 * 3306544 * 2
def baseEnd_3306544 : Nat := 1697846377240216365093487

theorem tailTrace_3306544 : CollatzResearch.WordTrace tailWord_3306544 prefixEnd_3306544 1697846377240216365093487 := by
  unfold tailWord_3306544
  simp only [CollatzResearch.WordTrace]
  refine ⟨60299783666481637800615343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80399711555308850400820457 60299783666481637800615343)
  ·
    refine ⟨90449675499722456700923015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60299783666481637800615343 90449675499722456700923015)
    ·
      refine ⟨135674513249583685051384523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90449675499722456700923015 135674513249583685051384523)
      ·
        refine ⟨203511769874375527577076785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135674513249583685051384523 203511769874375527577076785)
        ·
          refine ⟨152633827405781645682807589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203511769874375527577076785 152633827405781645682807589)
          ·
            refine ⟨28618842638584058565526423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152633827405781645682807589 28618842638584058565526423)
            ·
              refine ⟨42928263957876087848289635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28618842638584058565526423 42928263957876087848289635)
              ·
                refine ⟨64392395936814131772434453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42928263957876087848289635 64392395936814131772434453)
                ·
                  refine ⟨3018393559538162426832865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64392395936814131772434453 3018393559538162426832865)
                  ·
                    refine ⟨2263795169653621820124649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018393559538162426832865 2263795169653621820124649)
                    ·
                      refine ⟨1697846377240216365093487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263795169653621820124649 1697846377240216365093487)
                      ·
                        rfl

theorem cell23_3306544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 2, 2].length) (baseStart_3306544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306544 prefixEnd_3306544 := by exact prefixLift 3306544
  have htrace : WordTrace (prefixWord ++ tailWord_3306544) baseStart_3306544 baseEnd_3306544 := by
    simpa [prefixWord, tailWord_3306544, baseEnd_3306544] using wordTrace_append hprefix tailTrace_3306544
  have hstable : (prefixWord ++ tailWord_3306544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306544).length < 2 ^ (prefixWord ++ tailWord_3306544).sum := by decide
  have hdescent : baseEnd_3306544 < baseStart_3306544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306548 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_3306548 : Nat := 118140960795 + 3306548 * 2 ^ 59
def prefixEnd_3306548 : Nat := 4983230072969 + 3 ^ 40 * 3306548 * 2
def baseEnd_3306548 : Nat := 1697848431162834349443469

theorem tailTrace_3306548 : CollatzResearch.WordTrace tailWord_3306548 prefixEnd_3306548 1697848431162834349443469 := by
  unfold tailWord_3306548
  simp only [CollatzResearch.WordTrace]
  refine ⟨60299856612474392142188149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80399808816632522856250865 60299856612474392142188149)
  ·
    refine ⟨5653111557419474263330139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60299856612474392142188149 5653111557419474263330139)
    ·
      refine ⟨8479667336129211394995209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653111557419474263330139 8479667336129211394995209)
      ·
        refine ⟨6359750502096908546246407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8479667336129211394995209 6359750502096908546246407)
        ·
          refine ⟨9539625753145362819369611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359750502096908546246407 9539625753145362819369611)
          ·
            refine ⟨14309438629718044229054417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539625753145362819369611 14309438629718044229054417)
            ·
              refine ⟨10732078972288533171790813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14309438629718044229054417 10732078972288533171790813)
              ·
                refine ⟨4024529614608199939421555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10732078972288533171790813 4024529614608199939421555)
                ·
                  refine ⟨6036794421912299909132333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024529614608199939421555 6036794421912299909132333)
                  ·
                    refine ⟨2263797908217112465924625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6036794421912299909132333 2263797908217112465924625)
                    ·
                      refine ⟨1697848431162834349443469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263797908217112465924625 1697848431162834349443469)
                      ·
                        rfl

theorem cell23_3306548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_3306548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306548 prefixEnd_3306548 := by exact prefixLift 3306548
  have htrace : WordTrace (prefixWord ++ tailWord_3306548) baseStart_3306548 baseEnd_3306548 := by
    simpa [prefixWord, tailWord_3306548, baseEnd_3306548] using wordTrace_append hprefix tailTrace_3306548
  have hstable : (prefixWord ++ tailWord_3306548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306548).length < 2 ^ (prefixWord ++ tailWord_3306548).sum := by decide
  have hdescent : baseEnd_3306548 < baseStart_3306548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306560 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_3306560 : Nat := 118140960795 + 3306560 * 2 ^ 59
def prefixEnd_3306560 : Nat := 4983230072969 + 3 ^ 40 * 3306560 * 2
def baseEnd_3306560 : Nat := 1697854592930688302493413

theorem tailTrace_3306560 : CollatzResearch.WordTrace tailWord_3306560 prefixEnd_3306560 1697854592930688302493413 := by
  unfold tailWord_3306560
  simp only [CollatzResearch.WordTrace]
  refine ⟨60300075450452655166906567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80400100600603540222542089 60300075450452655166906567)
  ·
    refine ⟨90450113175678982750359851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60300075450452655166906567 90450113175678982750359851)
    ·
      refine ⟨135675169763518474125539777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90450113175678982750359851 135675169763518474125539777)
      ·
        refine ⟨101756377322638855594154833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135675169763518474125539777 101756377322638855594154833)
        ·
          refine ⟨76317282991979141695616125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101756377322638855594154833 76317282991979141695616125)
          ·
            refine ⟨28618981121992178135856047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76317282991979141695616125 28618981121992178135856047)
            ·
              refine ⟨42928471682988267203784071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28618981121992178135856047 42928471682988267203784071)
              ·
                refine ⟨64392707524482400805676107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42928471682988267203784071 64392707524482400805676107)
                ·
                  refine ⟨96589061286723601208514161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64392707524482400805676107 96589061286723601208514161)
                  ·
                    refine ⟨72441795965042700906385621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96589061286723601208514161 72441795965042700906385621)
                    ·
                      refine ⟨1697854592930688302493413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72441795965042700906385621 1697854592930688302493413)
                      ·
                        rfl

theorem cell23_3306560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_3306560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306560 prefixEnd_3306560 := by exact prefixLift 3306560
  have htrace : WordTrace (prefixWord ++ tailWord_3306560) baseStart_3306560 baseEnd_3306560 := by
    simpa [prefixWord, tailWord_3306560, baseEnd_3306560] using wordTrace_append hprefix tailTrace_3306560
  have hstable : (prefixWord ++ tailWord_3306560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306560).length < 2 ^ (prefixWord ++ tailWord_3306560).sum := by decide
  have hdescent : baseEnd_3306560 < baseStart_3306560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306567 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 7]
def baseStart_3306567 : Nat := 118140960795 + 3306567 * 2 ^ 59
def prefixEnd_3306567 : Nat := 4983230072969 + 3 ^ 40 * 3306567 * 2
def baseEnd_3306567 : Nat := 188650909699474419456209

theorem tailTrace_3306567 : CollatzResearch.WordTrace tailWord_3306567 prefixEnd_3306567 188650909699474419456209 := by
  unfold tailWord_3306567
  simp only [CollatzResearch.WordTrace]
  refine ⟨120600406211879950529317955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80400270807919967019545303 120600406211879950529317955)
  ·
    refine ⟨180900609317819925793976933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120600406211879950529317955 180900609317819925793976933)
    ·
      refine ⟨33918864247091236086370675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180900609317819925793976933 33918864247091236086370675)
      ·
        refine ⟨50878296370636854129556013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33918864247091236086370675 50878296370636854129556013)
        ·
          refine ⟨19079361138988820298583505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50878296370636854129556013 19079361138988820298583505)
          ·
            refine ⟨14309520854241615223937629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19079361138988820298583505 14309520854241615223937629)
            ·
              refine ⟨5366070320340605708976611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14309520854241615223937629 5366070320340605708976611)
              ·
                refine ⟨8049105480510908563464917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366070320340605708976611 8049105480510908563464917)
                ·
                  refine ⟨188650909699474419456209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8049105480510908563464917 188650909699474419456209)
                  ·
                    rfl

theorem cell23_3306567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 7].length) (baseStart_3306567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306567 prefixEnd_3306567 := by exact prefixLift 3306567
  have htrace : WordTrace (prefixWord ++ tailWord_3306567) baseStart_3306567 baseEnd_3306567 := by
    simpa [prefixWord, tailWord_3306567, baseEnd_3306567] using wordTrace_append hprefix tailTrace_3306567
  have hstable : (prefixWord ++ tailWord_3306567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306567).length < 2 ^ (prefixWord ++ tailWord_3306567).sum := by decide
  have hdescent : baseEnd_3306567 < baseStart_3306567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306577 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_3306577 : Nat := 118140960795 + 3306577 * 2 ^ 59
def prefixEnd_3306577 : Nat := 4983230072969 + 3 ^ 40 * 3306577 * 2
def baseEnd_3306577 : Nat := 1697863322101814735980835

theorem tailTrace_3306577 : CollatzResearch.WordTrace tailWord_3306577 prefixEnd_3306577 1697863322101814735980835 := by
  unfold tailWord_3306577
  simp only [CollatzResearch.WordTrace]
  refine ⟨120600770941843722237181985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80400513961229148158121323 120600770941843722237181985)
  ·
    refine ⟨90450578206382791677886489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120600770941843722237181985 90450578206382791677886489)
    ·
      refine ⟨67837933654787093758414867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90450578206382791677886489 67837933654787093758414867)
      ·
        refine ⟨101756900482180640637622301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67837933654787093758414867 101756900482180640637622301)
        ·
          refine ⟨38158837680817740239108363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101756900482180640637622301 38158837680817740239108363)
          ·
            refine ⟨57238256521226610358662545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38158837680817740239108363 57238256521226610358662545)
            ·
              refine ⟨42928692390919957768996909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57238256521226610358662545 42928692390919957768996909)
              ·
                refine ⟨16098259646594984163373841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42928692390919957768996909 16098259646594984163373841)
                ·
                  refine ⟨12073694734946238122530381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16098259646594984163373841 12073694734946238122530381)
                  ·
                    refine ⟨4527635525604839295948893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12073694734946238122530381 4527635525604839295948893)
                    ·
                      refine ⟨1697863322101814735980835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527635525604839295948893 1697863322101814735980835)
                      ·
                        rfl

theorem cell23_3306577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_3306577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306577 prefixEnd_3306577 := by exact prefixLift 3306577
  have htrace : WordTrace (prefixWord ++ tailWord_3306577) baseStart_3306577 baseEnd_3306577 := by
    simpa [prefixWord, tailWord_3306577, baseEnd_3306577] using wordTrace_append hprefix tailTrace_3306577
  have hstable : (prefixWord ++ tailWord_3306577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306577).length < 2 ^ (prefixWord ++ tailWord_3306577).sum := by decide
  have hdescent : baseEnd_3306577 < baseStart_3306577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306578 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_3306578 : Nat := 118140960795 + 3306578 * 2 ^ 59
def prefixEnd_3306578 : Nat := 4983230072969 + 3 ^ 40 * 3306578 * 2
def baseEnd_3306578 : Nat := 1697863835582469232068331

theorem tailTrace_3306578 : CollatzResearch.WordTrace tailWord_3306578 prefixEnd_3306578 1697863835582469232068331 := by
  unfold tailWord_3306578
  simp only [CollatzResearch.WordTrace]
  refine ⟨30150201853710024851992097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80400538276560066271978925 30150201853710024851992097)
  ·
    refine ⟨22612651390282518638994073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30150201853710024851992097 22612651390282518638994073)
    ·
      refine ⟨16959488542711888979245555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22612651390282518638994073 16959488542711888979245555)
      ·
        refine ⟨25439232814067833468868333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16959488542711888979245555 25439232814067833468868333)
        ·
          refine ⟨9539712305275437550825625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25439232814067833468868333 9539712305275437550825625)
          ·
            refine ⟨7154784228956578163119219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9539712305275437550825625 7154784228956578163119219)
            ·
              refine ⟨10732176343434867244678829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154784228956578163119219 10732176343434867244678829)
              ·
                refine ⟨4024566128788075216754561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10732176343434867244678829 4024566128788075216754561)
                ·
                  refine ⟨3018424596591056412565921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024566128788075216754561 3018424596591056412565921)
                  ·
                    refine ⟨2263818447443292309424441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018424596591056412565921 2263818447443292309424441)
                    ·
                      refine ⟨1697863835582469232068331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263818447443292309424441 1697863835582469232068331)
                      ·
                        rfl

theorem cell23_3306578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_3306578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306578 prefixEnd_3306578 := by exact prefixLift 3306578
  have htrace : WordTrace (prefixWord ++ tailWord_3306578) baseStart_3306578 baseEnd_3306578 := by
    simpa [prefixWord, tailWord_3306578, baseEnd_3306578] using wordTrace_append hprefix tailTrace_3306578
  have hstable : (prefixWord ++ tailWord_3306578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306578).length < 2 ^ (prefixWord ++ tailWord_3306578).sum := by decide
  have hdescent : baseEnd_3306578 < baseStart_3306578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306582 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3306582 : Nat := 118140960795 + 3306582 * 2 ^ 59
def prefixEnd_3306582 : Nat := 4983230072969 + 3 ^ 40 * 3306582 * 2
def baseEnd_3306582 : Nat := 1697865889505087216418313

theorem tailTrace_3306582 : CollatzResearch.WordTrace tailWord_3306582 prefixEnd_3306582 1697865889505087216418313 := by
  unfold tailWord_3306582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537559581676600505694625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80400635537883738727409333 7537559581676600505694625)
  ·
    refine ⟨5653169686257450379270969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7537559581676600505694625 5653169686257450379270969)
    ·
      refine ⟨4239877264693087784453227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5653169686257450379270969 4239877264693087784453227)
      ·
        refine ⟨6359815897039631676679841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239877264693087784453227 6359815897039631676679841)
        ·
          refine ⟨4769861922779723757509881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6359815897039631676679841 4769861922779723757509881)
          ·
            refine ⟨3577396442084792818132411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4769861922779723757509881 3577396442084792818132411)
            ·
              refine ⟨5366094663127189227198617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577396442084792818132411 5366094663127189227198617)
              ·
                refine ⟨4024570997345391920398963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366094663127189227198617 4024570997345391920398963)
                ·
                  refine ⟨6036856496018087880598445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024570997345391920398963 6036856496018087880598445)
                  ·
                    refine ⟨2263821186006782955224417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6036856496018087880598445 2263821186006782955224417)
                    ·
                      refine ⟨1697865889505087216418313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263821186006782955224417 1697865889505087216418313)
                      ·
                        rfl

theorem cell23_3306582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3306582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306582 prefixEnd_3306582 := by exact prefixLift 3306582
  have htrace : WordTrace (prefixWord ++ tailWord_3306582) baseStart_3306582 baseEnd_3306582 := by
    simpa [prefixWord, tailWord_3306582, baseEnd_3306582] using wordTrace_append hprefix tailTrace_3306582
  have hstable : (prefixWord ++ tailWord_3306582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306582).length < 2 ^ (prefixWord ++ tailWord_3306582).sum := by decide
  have hdescent : baseEnd_3306582 < baseStart_3306582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306614 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_3306614 : Nat := 118140960795 + 3306614 * 2 ^ 59
def prefixEnd_3306614 : Nat := 4983230072969 + 3 ^ 40 * 3306614 * 2
def baseEnd_3306614 : Nat := 565960773628677030406055

theorem tailTrace_3306614 : CollatzResearch.WordTrace tailWord_3306614 prefixEnd_3306614 565960773628677030406055 := by
  unfold tailWord_3306614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537632527669354847267431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80401413628473118370852597 7537632527669354847267431)
  ·
    refine ⟨11306448791504032270901147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7537632527669354847267431 11306448791504032270901147)
    ·
      refine ⟨16959673187256048406351721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11306448791504032270901147 16959673187256048406351721)
      ·
        refine ⟨12719754890442036304763791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16959673187256048406351721 12719754890442036304763791)
        ·
          refine ⟨19079632335663054457145687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12719754890442036304763791 19079632335663054457145687)
          ·
            refine ⟨28619448503494581685718531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19079632335663054457145687 28619448503494581685718531)
            ·
              refine ⟨42929172755241872528577797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28619448503494581685718531 42929172755241872528577797)
              ·
                refine ⟨8049219891607851099108337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42929172755241872528577797 8049219891607851099108337)
                ·
                  refine ⟨6036914918705888324331253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8049219891607851099108337 6036914918705888324331253)
                  ·
                    refine ⟨565960773628677030406055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6036914918705888324331253 565960773628677030406055)
                    ·
                      rfl

theorem cell23_3306614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_3306614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306614 prefixEnd_3306614 := by exact prefixLift 3306614
  have htrace : WordTrace (prefixWord ++ tailWord_3306614) baseStart_3306614 baseEnd_3306614 := by
    simpa [prefixWord, tailWord_3306614, baseEnd_3306614] using wordTrace_append hprefix tailTrace_3306614
  have hstable : (prefixWord ++ tailWord_3306614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306614).length < 2 ^ (prefixWord ++ tailWord_3306614).sum := by decide
  have hdescent : baseEnd_3306614 < baseStart_3306614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306657 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 8]
def baseStart_3306657 : Nat := 118140960795 + 3306657 * 2 ^ 59
def prefixEnd_3306657 : Nat := 4983230072969 + 3 ^ 40 * 3306657 * 2
def baseEnd_3306657 : Nat := 188656044506019380331163

theorem tailTrace_3306657 : CollatzResearch.WordTrace tailWord_3306657 prefixEnd_3306657 188656044506019380331163 := by
  unfold tailWord_3306657
  simp only [CollatzResearch.WordTrace]
  refine ⟨120603688781553895900094225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80402459187702597266729483 120603688781553895900094225)
  ·
    refine ⟨90452766586165421925070669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120603688781553895900094225 90452766586165421925070669)
    ·
      refine ⟨33919787469812033221901501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90452766586165421925070669 33919787469812033221901501)
      ·
        refine ⟨12719920301179512458213063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33919787469812033221901501 12719920301179512458213063)
        ·
          refine ⟨19079880451769268687319595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12719920301179512458213063 19079880451769268687319595)
          ·
            refine ⟨28619820677653903030979393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19079880451769268687319595 28619820677653903030979393)
            ·
              refine ⟨21464865508240427273234545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28619820677653903030979393 21464865508240427273234545)
              ·
                refine ⟨16098649131180320454925909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21464865508240427273234545 16098649131180320454925909)
                ·
                  refine ⟨188656044506019380331163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16098649131180320454925909 188656044506019380331163)
                  ·
                    rfl

theorem cell23_3306657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 8].length) (baseStart_3306657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306657 prefixEnd_3306657 := by exact prefixLift 3306657
  have htrace : WordTrace (prefixWord ++ tailWord_3306657) baseStart_3306657 baseEnd_3306657 := by
    simpa [prefixWord, tailWord_3306657, baseEnd_3306657] using wordTrace_append hprefix tailTrace_3306657
  have hstable : (prefixWord ++ tailWord_3306657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306657).length < 2 ^ (prefixWord ++ tailWord_3306657).sum := by decide
  have hdescent : baseEnd_3306657 < baseStart_3306657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306661 : List Nat := [1, 3, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_3306661 : Nat := 118140960795 + 3306661 * 2 ^ 59
def prefixEnd_3306661 : Nat := 4983230072969 + 3 ^ 40 * 3306661 * 2
def baseEnd_3306661 : Nat := 565968818158930802443483

theorem tailTrace_3306661 : CollatzResearch.WordTrace tailWord_3306661 prefixEnd_3306661 565968818158930802443483 := by
  unfold tailWord_3306661
  simp only [CollatzResearch.WordTrace]
  refine ⟨120603834673539404583239837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80402556449026269722159891 120603834673539404583239837)
  ·
    refine ⟨45226438002577276718714939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120603834673539404583239837 45226438002577276718714939)
    ·
      refine ⟨67839657003865915078072409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45226438002577276718714939 67839657003865915078072409)
      ·
        refine ⟨50879742752899436308554307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67839657003865915078072409 50879742752899436308554307)
        ·
          refine ⟨76319614129349154462831461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50879742752899436308554307 76319614129349154462831461)
          ·
            refine ⟨14309927649252966461780899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76319614129349154462831461 14309927649252966461780899)
            ·
              refine ⟨21464891473879449692671349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309927649252966461780899 21464891473879449692671349)
              ·
                refine ⟨2012333575676198408687939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21464891473879449692671349 2012333575676198408687939)
                ·
                  refine ⟨3018500363514297613031909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012333575676198408687939 3018500363514297613031909)
                  ·
                    refine ⟨565968818158930802443483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018500363514297613031909 565968818158930802443483)
                    ·
                      rfl

theorem cell23_3306661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_3306661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306661 prefixEnd_3306661 := by exact prefixLift 3306661
  have htrace : WordTrace (prefixWord ++ tailWord_3306661) baseStart_3306661 baseEnd_3306661 := by
    simpa [prefixWord, tailWord_3306661, baseEnd_3306661] using wordTrace_append hprefix tailTrace_3306661
  have hstable : (prefixWord ++ tailWord_3306661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306661).length < 2 ^ (prefixWord ++ tailWord_3306661).sum := by decide
  have hdescent : baseEnd_3306661 < baseStart_3306661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306674 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 6]
def baseStart_3306674 : Nat := 118140960795 + 3306674 * 2 ^ 59
def prefixEnd_3306674 : Nat := 4983230072969 + 3 ^ 40 * 3306674 * 2
def baseEnd_3306674 : Nat := 188657014413922317385321

theorem tailTrace_3306674 : CollatzResearch.WordTrace tailWord_3306674 prefixEnd_3306674 188657014413922317385321 := by
  unfold tailWord_3306674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30151077205623076950865769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80402872548328205202308717 30151077205623076950865769)
  ·
    refine ⟨22613307904217307713149327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30151077205623076950865769 22613307904217307713149327)
    ·
      refine ⟨33919961856325961569723991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22613307904217307713149327 33919961856325961569723991)
      ·
        refine ⟨50879942784488942354585987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33919961856325961569723991 50879942784488942354585987)
        ·
          refine ⟨76319914176733413531878981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50879942784488942354585987 76319914176733413531878981)
          ·
            refine ⟨14309983908137515037227309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76319914176733413531878981 14309983908137515037227309)
            ·
              refine ⟨5366243965551568138960241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14309983908137515037227309 5366243965551568138960241)
              ·
                refine ⟨4024682974163676104220181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366243965551568138960241 4024682974163676104220181)
                ·
                  refine ⟨188657014413922317385321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4024682974163676104220181 188657014413922317385321)
                  ·
                    rfl

theorem cell23_3306674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_3306674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306674 prefixEnd_3306674 := by exact prefixLift 3306674
  have htrace : WordTrace (prefixWord ++ tailWord_3306674) baseStart_3306674 baseEnd_3306674 := by
    simpa [prefixWord, tailWord_3306674, baseEnd_3306674] using wordTrace_append hprefix tailTrace_3306674
  have hstable : (prefixWord ++ tailWord_3306674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306674).length < 2 ^ (prefixWord ++ tailWord_3306674).sum := by decide
  have hdescent : baseEnd_3306674 < baseStart_3306674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306687 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 5, 5]
def baseStart_3306687 : Nat := 118140960795 + 3306687 * 2 ^ 59
def prefixEnd_3306687 : Nat := 4983230072969 + 3 ^ 40 * 3306687 * 2
def baseEnd_3306687 : Nat := 565973268324603101868443

theorem tailTrace_3306687 : CollatzResearch.WordTrace tailWord_3306687 prefixEnd_3306687 565973268324603101868443 := by
  unfold tailWord_3306687
  simp only [CollatzResearch.WordTrace]
  refine ⟨120604782971445211023686315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80403188647630140682457543 120604782971445211023686315)
  ·
    refine ⟨180907174457167816535529473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120604782971445211023686315 180907174457167816535529473)
    ·
      refine ⟨135680380842875862401647105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180907174457167816535529473 135680380842875862401647105)
      ·
        refine ⟨101760285632156896801235329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135680380842875862401647105 101760285632156896801235329)
        ·
          refine ⟨76320214224117672600926497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101760285632156896801235329 76320214224117672600926497)
          ·
            refine ⟨57240160668088254450694873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76320214224117672600926497 57240160668088254450694873)
            ·
              refine ⟨42930120501066190838021155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57240160668088254450694873 42930120501066190838021155)
              ·
                refine ⟨64395180751599286257031733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42930120501066190838021155 64395180751599286257031733)
                ·
                  refine ⟨6037048195462433086596725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64395180751599286257031733 6037048195462433086596725)
                  ·
                    refine ⟨565973268324603101868443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6037048195462433086596725 565973268324603101868443)
                    ·
                      rfl

theorem cell23_3306687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_3306687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306687 prefixEnd_3306687 := by exact prefixLift 3306687
  have htrace : WordTrace (prefixWord ++ tailWord_3306687) baseStart_3306687 baseEnd_3306687 := by
    simpa [prefixWord, tailWord_3306687, baseEnd_3306687] using wordTrace_append hprefix tailTrace_3306687
  have hstable : (prefixWord ++ tailWord_3306687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306687).length < 2 ^ (prefixWord ++ tailWord_3306687).sum := by decide
  have hdescent : baseEnd_3306687 < baseStart_3306687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306735 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 3, 1, 3]
def baseStart_3306735 : Nat := 118140960795 + 3306735 * 2 ^ 59
def prefixEnd_3306735 : Nat := 4983230072969 + 3 ^ 40 * 3306735 * 2
def baseEnd_3306735 : Nat := 1697944452045225117805109

theorem tailTrace_3306735 : CollatzResearch.WordTrace tailWord_3306735 prefixEnd_3306735 1697944452045225117805109 := by
  unfold tailWord_3306735
  simp only [CollatzResearch.WordTrace]
  refine ⟨120606533675271315221433659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80404355783514210147622439 120606533675271315221433659)
  ·
    refine ⟨180909800512906972832150489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120606533675271315221433659 180909800512906972832150489)
    ·
      refine ⟨135682350384680229624112867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180909800512906972832150489 135682350384680229624112867)
      ·
        refine ⟨203523525577020344436169301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135682350384680229624112867 203523525577020344436169301)
        ·
          refine ⟨2385041315355707161361359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 203523525577020344436169301 2385041315355707161361359)
          ·
            refine ⟨3577561973033560742042039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385041315355707161361359 3577561973033560742042039)
            ·
              refine ⟨5366342959550341113063059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577561973033560742042039 5366342959550341113063059)
              ·
                refine ⟨8049514439325511669594589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366342959550341113063059 8049514439325511669594589)
                ·
                  refine ⟨3018567914747066876097971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8049514439325511669594589 3018567914747066876097971)
                  ·
                    refine ⟨4527851872120600314146957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3018567914747066876097971 4527851872120600314146957)
                    ·
                      refine ⟨1697944452045225117805109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527851872120600314146957 1697944452045225117805109)
                      ·
                        rfl

theorem cell23_3306735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 1, 3].length) (baseStart_3306735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306735 prefixEnd_3306735 := by exact prefixLift 3306735
  have htrace : WordTrace (prefixWord ++ tailWord_3306735) baseStart_3306735 baseEnd_3306735 := by
    simpa [prefixWord, tailWord_3306735, baseEnd_3306735] using wordTrace_append hprefix tailTrace_3306735
  have hstable : (prefixWord ++ tailWord_3306735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306735).length < 2 ^ (prefixWord ++ tailWord_3306735).sum := by decide
  have hdescent : baseEnd_3306735 < baseStart_3306735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306751 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 2, 4]
def baseStart_3306751 : Nat := 118140960795 + 3306751 * 2 ^ 59
def prefixEnd_3306751 : Nat := 4983230072969 + 3 ^ 40 * 3306751 * 2
def baseEnd_3306751 : Nat := 565984222578565685068345

theorem tailTrace_3306751 : CollatzResearch.WordTrace tailWord_3306751 prefixEnd_3306751 565984222578565685068345 := by
  unfold tailWord_3306751
  simp only [CollatzResearch.WordTrace]
  refine ⟨120607117243213349954016107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80404744828808899969344071 120607117243213349954016107)
  ·
    refine ⟨180910675864820024931024161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120607117243213349954016107 180910675864820024931024161)
    ·
      refine ⟨135683006898615018698268121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180910675864820024931024161 135683006898615018698268121)
      ·
        refine ⟨101762255173961264023701091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135683006898615018698268121 101762255173961264023701091)
        ·
          refine ⟨152643382760941896035551637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101762255173961264023701091 152643382760941896035551637)
          ·
            refine ⟨7155158566919151376666483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152643382760941896035551637 7155158566919151376666483)
            ·
              refine ⟨10732737850378727064999725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155158566919151376666483 10732737850378727064999725)
              ·
                refine ⟨4024776693892022649374897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10732737850378727064999725 4024776693892022649374897)
                ·
                  refine ⟨3018582520419016987031173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024776693892022649374897 3018582520419016987031173)
                  ·
                    refine ⟨565984222578565685068345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018582520419016987031173 565984222578565685068345)
                    ·
                      rfl

theorem cell23_3306751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_3306751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306751 prefixEnd_3306751 := by exact prefixLift 3306751
  have htrace : WordTrace (prefixWord ++ tailWord_3306751) baseStart_3306751 baseEnd_3306751 := by
    simpa [prefixWord, tailWord_3306751, baseEnd_3306751] using wordTrace_append hprefix tailTrace_3306751
  have hstable : (prefixWord ++ tailWord_3306751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306751).length < 2 ^ (prefixWord ++ tailWord_3306751).sum := by decide
  have hdescent : baseEnd_3306751 < baseStart_3306751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306775 : List Nat := [1, 1, 3, 4, 1, 1, 2, 5, 1, 2, 2]
def baseStart_3306775 : Nat := 118140960795 + 3306775 * 2 ^ 59
def prefixEnd_3306775 : Nat := 4983230072969 + 3 ^ 40 * 3306775 * 2
def baseEnd_3306775 : Nat := 1697964991271404961304925

theorem tailTrace_3306775 : CollatzResearch.WordTrace tailWord_3306775 prefixEnd_3306775 1697964991271404961304925 := by
  unfold tailWord_3306775
  simp only [CollatzResearch.WordTrace]
  refine ⟨120607992595126402052889779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80405328396750934701926519 120607992595126402052889779)
  ·
    refine ⟨180911988892689603079334669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120607992595126402052889779 180911988892689603079334669)
    ·
      refine ⟨67841995834758601154750501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180911988892689603079334669 67841995834758601154750501)
      ·
        refine ⟨12720374219017237716515719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67841995834758601154750501 12720374219017237716515719)
        ·
          refine ⟨19080561328525856574773579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12720374219017237716515719 19080561328525856574773579)
          ·
            refine ⟨28620841992788784862160369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19080561328525856574773579 28620841992788784862160369)
            ·
              refine ⟨21465631494591588646620277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28620841992788784862160369 21465631494591588646620277)
              ·
                refine ⟨2012402952617961435620651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21465631494591588646620277 2012402952617961435620651)
                ·
                  refine ⟨3018604428926942153430977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012402952617961435620651 3018604428926942153430977)
                  ·
                    refine ⟨2263953321695206615073233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018604428926942153430977 2263953321695206615073233)
                    ·
                      refine ⟨1697964991271404961304925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263953321695206615073233 1697964991271404961304925)
                      ·
                        rfl

theorem cell23_3306775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_3306775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306775 prefixEnd_3306775 := by exact prefixLift 3306775
  have htrace : WordTrace (prefixWord ++ tailWord_3306775) baseStart_3306775 baseEnd_3306775 := by
    simpa [prefixWord, tailWord_3306775, baseEnd_3306775] using wordTrace_append hprefix tailTrace_3306775
  have hstable : (prefixWord ++ tailWord_3306775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306775).length < 2 ^ (prefixWord ++ tailWord_3306775).sum := by decide
  have hdescent : baseEnd_3306775 < baseStart_3306775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306777 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 6, 7]
def baseStart_3306777 : Nat := 118140960795 + 3306777 * 2 ^ 59
def prefixEnd_3306777 : Nat := 4983230072969 + 3 ^ 40 * 3306777 * 2
def baseEnd_3306777 : Nat := 565988672744237984493305

theorem tailTrace_3306777 : CollatzResearch.WordTrace tailWord_3306777 prefixEnd_3306777 565988672744237984493305 := by
  unfold tailWord_3306777
  simp only [CollatzResearch.WordTrace]
  refine ⟨120608065541119156394462585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80405377027412770929641723 120608065541119156394462585)
  ·
    refine ⟨90456049155839367295846939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120608065541119156394462585 90456049155839367295846939)
    ·
      refine ⟨135684073733759050943770409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90456049155839367295846939 135684073733759050943770409)
      ·
        refine ⟨101763055300319288207827807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135684073733759050943770409 101763055300319288207827807)
        ·
          refine ⟨152644582950478932311741711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101763055300319288207827807 152644582950478932311741711)
          ·
            refine ⟨228966874425718398467612567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152644582950478932311741711 228966874425718398467612567)
            ·
              refine ⟨343450311638577597701418851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228966874425718398467612567 343450311638577597701418851)
              ·
                refine ⟨515175467457866396552128277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343450311638577597701418851 515175467457866396552128277)
                ·
                  refine ⟨24148850037087487338381013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 515175467457866396552128277 24148850037087487338381013)
                  ·
                    refine ⟨565988672744237984493305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24148850037087487338381013 565988672744237984493305)
                    ·
                      rfl

theorem cell23_3306777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_3306777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306777 prefixEnd_3306777 := by exact prefixLift 3306777
  have htrace : WordTrace (prefixWord ++ tailWord_3306777) baseStart_3306777 baseEnd_3306777 := by
    simpa [prefixWord, tailWord_3306777, baseEnd_3306777] using wordTrace_append hprefix tailTrace_3306777
  have hstable : (prefixWord ++ tailWord_3306777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306777).length < 2 ^ (prefixWord ++ tailWord_3306777).sum := by decide
  have hdescent : baseEnd_3306777 < baseStart_3306777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306792 : List Nat := [2, 1, 5, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_3306792 : Nat := 118140960795 + 3306792 * 2 ^ 59
def prefixEnd_3306792 : Nat := 4983230072969 + 3 ^ 40 * 3306792 * 2
def baseEnd_3306792 : Nat := 1697973720442531394792347

theorem tailTrace_3306792 : CollatzResearch.WordTrace tailWord_3306792 prefixEnd_3306792 1697973720442531394792347 := by
  unfold tailWord_3306792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60304306318032406978129315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80405741757376542637505753 60304306318032406978129315)
  ·
    refine ⟨90456459477048610467193973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60304306318032406978129315 90456459477048610467193973)
    ·
      refine ⟨8480293075973307231299435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90456459477048610467193973 8480293075973307231299435)
      ·
        refine ⟨12720439613959960846949153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480293075973307231299435 12720439613959960846949153)
        ·
          refine ⟨9540329710469970635211865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12720439613959960846949153 9540329710469970635211865)
          ·
            refine ⟨7155247282852477976408899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9540329710469970635211865 7155247282852477976408899)
            ·
              refine ⟨10732870924278716964613349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155247282852477976408899 10732870924278716964613349)
              ·
                refine ⟨2012413298302259430865003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10732870924278716964613349 2012413298302259430865003)
                ·
                  refine ⟨3018619947453389146297505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012413298302259430865003 3018619947453389146297505)
                  ·
                    refine ⟨2263964960590041859723129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018619947453389146297505 2263964960590041859723129)
                    ·
                      refine ⟨1697973720442531394792347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2263964960590041859723129 1697973720442531394792347)
                      ·
                        rfl

theorem cell23_3306792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_3306792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306792 prefixEnd_3306792 := by exact prefixLift 3306792
  have htrace : WordTrace (prefixWord ++ tailWord_3306792) baseStart_3306792 baseEnd_3306792 := by
    simpa [prefixWord, tailWord_3306792, baseEnd_3306792] using wordTrace_append hprefix tailTrace_3306792
  have hstable : (prefixWord ++ tailWord_3306792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306792).length < 2 ^ (prefixWord ++ tailWord_3306792).sum := by decide
  have hdescent : baseEnd_3306792 < baseStart_3306792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306829 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3306829 : Nat := 118140960795 + 3306829 * 2 ^ 59
def prefixEnd_3306829 : Nat := 4983230072969 + 3 ^ 40 * 3306829 * 2
def baseEnd_3306829 : Nat := 1697992719226747750029677

theorem tailTrace_3306829 : CollatzResearch.WordTrace tailWord_3306829 prefixEnd_3306829 1697992719226747750029677 := by
  unfold tailWord_3306829
  simp only [CollatzResearch.WordTrace]
  refine ⟨120609962136930769275355541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80406641424620512850237027 120609962136930769275355541)
  ·
    refine ⟨5653591975168629809782291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120609962136930769275355541 5653591975168629809782291)
    ·
      refine ⟨8480387962752944714673437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653591975168629809782291 8480387962752944714673437)
      ·
        refine ⟨3180145486032354268002539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8480387962752944714673437 3180145486032354268002539)
        ·
          refine ⟨4770218229048531402003809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180145486032354268002539 4770218229048531402003809)
          ·
            refine ⟨3577663671786398551502857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4770218229048531402003809 3577663671786398551502857)
            ·
              refine ⟨2683247753839798913627143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577663671786398551502857 2683247753839798913627143)
              ·
                refine ⟨4024871630759698370440715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683247753839798913627143 4024871630759698370440715)
                ·
                  refine ⟨6037307446139547555661073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024871630759698370440715 6037307446139547555661073)
                  ·
                    refine ⟨4527980584604660666745805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6037307446139547555661073 4527980584604660666745805)
                    ·
                      refine ⟨1697992719226747750029677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4527980584604660666745805 1697992719226747750029677)
                      ·
                        rfl

theorem cell23_3306829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3306829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306829 prefixEnd_3306829 := by exact prefixLift 3306829
  have htrace : WordTrace (prefixWord ++ tailWord_3306829) baseStart_3306829 baseEnd_3306829 := by
    simpa [prefixWord, tailWord_3306829, baseEnd_3306829] using wordTrace_append hprefix tailTrace_3306829
  have hstable : (prefixWord ++ tailWord_3306829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306829).length < 2 ^ (prefixWord ++ tailWord_3306829).sum := by decide
  have hdescent : baseEnd_3306829 < baseStart_3306829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306834 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3306834 : Nat := 118140960795 + 3306834 * 2 ^ 59
def prefixEnd_3306834 : Nat := 4983230072969 + 3 ^ 40 * 3306834 * 2
def baseEnd_3306834 : Nat := 1697995286630020230467153

theorem tailTrace_3306834 : CollatzResearch.WordTrace tailWord_3306834 prefixEnd_3306834 1697995286630020230467153 := by
  unfold tailWord_3306834
  simp only [CollatzResearch.WordTrace]
  refine ⟨30152536125478163782321889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80406763001275103419525037 30152536125478163782321889)
  ·
    refine ⟨22614402094108622836741417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30152536125478163782321889 22614402094108622836741417)
    ·
      refine ⟨16960801570581467127556063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22614402094108622836741417 16960801570581467127556063)
      ·
        refine ⟨25441202355872200691334095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16960801570581467127556063 25441202355872200691334095)
        ·
          refine ⟨38161803533808301037001143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25441202355872200691334095 38161803533808301037001143)
          ·
            refine ⟨57242705300712451555501715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38161803533808301037001143 57242705300712451555501715)
            ·
              refine ⟨85864057951068677333252573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57242705300712451555501715 85864057951068677333252573)
              ·
                refine ⟨32199021731650753999969715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85864057951068677333252573 32199021731650753999969715)
                ·
                  refine ⟨48298532597476130999954573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32199021731650753999969715 48298532597476130999954573)
                  ·
                    refine ⟨18111949724053549124982965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48298532597476130999954573 18111949724053549124982965)
                    ·
                      refine ⟨1697995286630020230467153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18111949724053549124982965 1697995286630020230467153)
                      ·
                        rfl

theorem cell23_3306834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3306834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306834 prefixEnd_3306834 := by exact prefixLift 3306834
  have htrace : WordTrace (prefixWord ++ tailWord_3306834) baseStart_3306834 baseEnd_3306834 := by
    simpa [prefixWord, tailWord_3306834, baseEnd_3306834] using wordTrace_append hprefix tailTrace_3306834
  have hstable : (prefixWord ++ tailWord_3306834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306834).length < 2 ^ (prefixWord ++ tailWord_3306834).sum := by decide
  have hdescent : baseEnd_3306834 < baseStart_3306834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306861 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3306861 : Nat := 118140960795 + 3306861 * 2 ^ 59
def prefixEnd_3306861 : Nat := 4983230072969 + 3 ^ 40 * 3306861 * 2
def baseEnd_3306861 : Nat := 1698009150607691624829529

theorem tailTrace_3306861 : CollatzResearch.WordTrace tailWord_3306861 prefixEnd_3306861 1698009150607691624829529 := by
  unfold tailWord_3306861
  simp only [CollatzResearch.WordTrace]
  refine ⟨120611129272814838740520437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80407419515209892493680291 120611129272814838740520437)
  ·
    refine ⟨11307293369326391131923791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120611129272814838740520437 11307293369326391131923791)
    ·
      refine ⟨16960940053989586697885687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11307293369326391131923791 16960940053989586697885687)
      ·
        refine ⟨25441410080984380046828531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16960940053989586697885687 25441410080984380046828531)
        ·
          refine ⟨38162115121476570070242797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25441410080984380046828531 38162115121476570070242797)
          ·
            refine ⟨14310793170553713776341049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38162115121476570070242797 14310793170553713776341049)
            ·
              refine ⟨10733094877915285332255787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14310793170553713776341049 10733094877915285332255787)
              ·
                refine ⟨16099642316872927998383681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733094877915285332255787 16099642316872927998383681)
                ·
                  refine ⟨12074731737654695998787761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16099642316872927998383681 12074731737654695998787761)
                  ·
                    refine ⟨9056048803241021999090821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12074731737654695998787761 9056048803241021999090821)
                    ·
                      refine ⟨1698009150607691624829529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9056048803241021999090821 1698009150607691624829529)
                      ·
                        rfl

theorem cell23_3306861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3306861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306861 prefixEnd_3306861 := by exact prefixLift 3306861
  have htrace : WordTrace (prefixWord ++ tailWord_3306861) baseStart_3306861 baseEnd_3306861 := by
    simpa [prefixWord, tailWord_3306861, baseEnd_3306861] using wordTrace_append hprefix tailTrace_3306861
  have hstable : (prefixWord ++ tailWord_3306861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306861).length < 2 ^ (prefixWord ++ tailWord_3306861).sum := by decide
  have hdescent : baseEnd_3306861 < baseStart_3306861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306882 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_3306882 : Nat := 118140960795 + 3306882 * 2 ^ 59
def prefixEnd_3306882 : Nat := 4983230072969 + 3 ^ 40 * 3306882 * 2
def baseEnd_3306882 : Nat := 1698019933701436042666933

theorem tailTrace_3306882 : CollatzResearch.WordTrace tailWord_3306882 prefixEnd_3306882 1698019933701436042666933 := by
  unfold tailWord_3306882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30152973801434689831758725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80407930137159172884689933 30152973801434689831758725)
  ·
    refine ⟨5653682587769004343454761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30152973801434689831758725 5653682587769004343454761)
    ·
      refine ⟨4240261940826753257591071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5653682587769004343454761 4240261940826753257591071)
      ·
        refine ⟨6360392911240129886386607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240261940826753257591071 6360392911240129886386607)
        ·
          refine ⟨9540589366860194829579911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360392911240129886386607 9540589366860194829579911)
          ·
            refine ⟨14310884050290292244369867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540589366860194829579911 14310884050290292244369867)
            ·
              refine ⟨21466326075435438366554801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14310884050290292244369867 21466326075435438366554801)
              ·
                refine ⟨16099744556576578774916101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21466326075435438366554801 16099744556576578774916101)
                ·
                  refine ⟨3018702104358108520296769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16099744556576578774916101 3018702104358108520296769)
                  ·
                    refine ⟨2264026578268581390222577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018702104358108520296769 2264026578268581390222577)
                    ·
                      refine ⟨1698019933701436042666933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264026578268581390222577 1698019933701436042666933)
                      ·
                        rfl

theorem cell23_3306882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_3306882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306882 prefixEnd_3306882 := by exact prefixLift 3306882
  have htrace : WordTrace (prefixWord ++ tailWord_3306882) baseStart_3306882 baseEnd_3306882 := by
    simpa [prefixWord, tailWord_3306882, baseEnd_3306882] using wordTrace_append hprefix tailTrace_3306882
  have hstable : (prefixWord ++ tailWord_3306882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306882).length < 2 ^ (prefixWord ++ tailWord_3306882).sum := by decide
  have hdescent : baseEnd_3306882 < baseStart_3306882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306888 : List Nat := [2, 1, 3, 3, 1, 2, 3, 3, 5]
def baseStart_3306888 : Nat := 118140960795 + 3306888 * 2 ^ 59
def prefixEnd_3306888 : Nat := 4983230072969 + 3 ^ 40 * 3306888 * 2
def baseEnd_3306888 : Nat := 188669223842818113243545

theorem tailTrace_3306888 : CollatzResearch.WordTrace tailWord_3306888 prefixEnd_3306888 188669223842818113243545 := by
  unfold tailWord_3306888
  simp only [CollatzResearch.WordTrace]
  refine ⟨60306057021858511175876659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80408076029144681567835545 60306057021858511175876659)
  ·
    refine ⟨90459085532787766763814989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60306057021858511175876659 90459085532787766763814989)
    ·
      refine ⟨33922157074795412536430621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90459085532787766763814989 33922157074795412536430621)
      ·
        refine ⟨12720808903048279701161483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33922157074795412536430621 12720808903048279701161483)
        ·
          refine ⟨19081213354572419551742225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12720808903048279701161483 19081213354572419551742225)
          ·
            refine ⟨14310910015929314663806669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19081213354572419551742225 14310910015929314663806669)
            ·
              refine ⟨5366591255973492998927501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14310910015929314663806669 5366591255973492998927501)
              ·
                refine ⟨2012471720990059874597813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5366591255973492998927501 2012471720990059874597813)
                ·
                  refine ⟨188669223842818113243545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2012471720990059874597813 188669223842818113243545)
                  ·
                    rfl

theorem cell23_3306888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 5].length) (baseStart_3306888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306888 prefixEnd_3306888 := by exact prefixLift 3306888
  have htrace : WordTrace (prefixWord ++ tailWord_3306888) baseStart_3306888 baseEnd_3306888 := by
    simpa [prefixWord, tailWord_3306888, baseEnd_3306888] using wordTrace_append hprefix tailTrace_3306888
  have hstable : (prefixWord ++ tailWord_3306888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306888).length < 2 ^ (prefixWord ++ tailWord_3306888).sum := by decide
  have hdescent : baseEnd_3306888 < baseStart_3306888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306911 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3306911 : Nat := 118140960795 + 3306911 * 2 ^ 59
def prefixEnd_3306911 : Nat := 4983230072969 + 3 ^ 40 * 3306911 * 2
def baseEnd_3306911 : Nat := 1698034824640416429204299

theorem tailTrace_3306911 : CollatzResearch.WordTrace tailWord_3306911 prefixEnd_3306911 1698034824640416429204299 := by
  unfold tailWord_3306911
  simp only [CollatzResearch.WordTrace]
  refine ⟨120612952922633697279840587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80408635281755798186560391 120612952922633697279840587)
  ·
    refine ⟨180919429383950545919760881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120612952922633697279840587 180919429383950545919760881)
    ·
      refine ⟨135689572037962909439820661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180919429383950545919760881 135689572037962909439820661)
      ·
        refine ⟨12720897378559022759983187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135689572037962909439820661 12720897378559022759983187)
        ·
          refine ⟨19081346067838534139974781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12720897378559022759983187 19081346067838534139974781)
          ·
            refine ⟨7155504775439450302490543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19081346067838534139974781 7155504775439450302490543)
            ·
              refine ⟨10733257163159175453735815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155504775439450302490543 10733257163159175453735815)
              ·
                refine ⟨16099885744738763180603723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733257163159175453735815 16099885744738763180603723)
                ·
                  refine ⟨24149828617108144770905585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16099885744738763180603723 24149828617108144770905585)
                  ·
                    refine ⟨18112371462831108578179189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24149828617108144770905585 18112371462831108578179189)
                    ·
                      refine ⟨1698034824640416429204299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18112371462831108578179189 1698034824640416429204299)
                      ·
                        rfl

theorem cell23_3306911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3306911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306911 prefixEnd_3306911 := by exact prefixLift 3306911
  have htrace : WordTrace (prefixWord ++ tailWord_3306911) baseStart_3306911 baseEnd_3306911 := by
    simpa [prefixWord, tailWord_3306911, baseEnd_3306911] using wordTrace_append hprefix tailTrace_3306911
  have hstable : (prefixWord ++ tailWord_3306911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306911).length < 2 ^ (prefixWord ++ tailWord_3306911).sum := by decide
  have hdescent : baseEnd_3306911 < baseStart_3306911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306931 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 3, 4]
def baseStart_3306931 : Nat := 118140960795 + 3306931 * 2 ^ 59
def prefixEnd_3306931 : Nat := 4983230072969 + 3 ^ 40 * 3306931 * 2
def baseEnd_3306931 : Nat := 566015031417835450318069

theorem tailTrace_3306931 : CollatzResearch.WordTrace tailWord_3306931 prefixEnd_3306931 566015031417835450318069 := by
  unfold tailWord_3306931
  simp only [CollatzResearch.WordTrace]
  refine ⟨120613682382561240695568647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80409121588374160463712431 120613682382561240695568647)
  ·
    refine ⟨180920523573841861043352971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120613682382561240695568647 180920523573841861043352971)
    ·
      refine ⟨271380785360762791565029457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180920523573841861043352971 271380785360762791565029457)
      ·
        refine ⟨203535589020572093673772093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271380785360762791565029457 203535589020572093673772093)
        ·
          refine ⟨76325845882714535127664535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203535589020572093673772093 76325845882714535127664535)
          ·
            refine ⟨114488768824071802691496803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76325845882714535127664535 114488768824071802691496803)
            ·
              refine ⟨171733153236107704037245205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114488768824071802691496803 171733153236107704037245205)
              ·
                refine ⟨8049991557942548626745869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171733153236107704037245205 8049991557942548626745869)
                ·
                  refine ⟨3018746834228455735029701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8049991557942548626745869 3018746834228455735029701)
                  ·
                    refine ⟨566015031417835450318069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018746834228455735029701 566015031417835450318069)
                    ·
                      rfl

theorem cell23_3306931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 4].length) (baseStart_3306931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306931 prefixEnd_3306931 := by exact prefixLift 3306931
  have htrace : WordTrace (prefixWord ++ tailWord_3306931) baseStart_3306931 baseEnd_3306931 := by
    simpa [prefixWord, tailWord_3306931, baseEnd_3306931] using wordTrace_append hprefix tailTrace_3306931
  have hstable : (prefixWord ++ tailWord_3306931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306931).length < 2 ^ (prefixWord ++ tailWord_3306931).sum := by decide
  have hdescent : baseEnd_3306931 < baseStart_3306931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306944 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 10]
def baseStart_3306944 : Nat := 118140960795 + 3306944 * 2 ^ 59
def prefixEnd_3306944 : Nat := 4983230072969 + 3 ^ 40 * 3306944 * 2
def baseEnd_3306944 : Nat := 188672418833557200010183

theorem tailTrace_3306944 : CollatzResearch.WordTrace tailWord_3306944 prefixEnd_3306944 188672418833557200010183 := by
  unfold tailWord_3306944
  simp only [CollatzResearch.WordTrace]
  refine ⟨60307078265757071957895943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80409437687676095943861257 60307078265757071957895943)
  ·
    refine ⟨90460617398635607936843915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60307078265757071957895943 90460617398635607936843915)
    ·
      refine ⟨135690926097953411905265873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90460617398635607936843915 135690926097953411905265873)
      ·
        refine ⟨101768194573465058928949405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135690926097953411905265873 101768194573465058928949405)
        ·
          refine ⟨38163072965049397098356027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101768194573465058928949405 38163072965049397098356027)
          ·
            refine ⟨57244609447574095647534041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38163072965049397098356027 57244609447574095647534041)
            ·
              refine ⟨42933457085680571735650531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57244609447574095647534041 42933457085680571735650531)
              ·
                refine ⟨64400185628520857603475797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42933457085680571735650531 64400185628520857603475797)
                ·
                  refine ⟨188672418833557200010183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 64400185628520857603475797 188672418833557200010183)
                  ·
                    rfl

theorem cell23_3306944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_3306944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306944 prefixEnd_3306944 := by exact prefixLift 3306944
  have htrace : WordTrace (prefixWord ++ tailWord_3306944) baseStart_3306944 baseEnd_3306944 := by
    simpa [prefixWord, tailWord_3306944, baseEnd_3306944] using wordTrace_append hprefix tailTrace_3306944
  have hstable : (prefixWord ++ tailWord_3306944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306944).length < 2 ^ (prefixWord ++ tailWord_3306944).sum := by decide
  have hdescent : baseEnd_3306944 < baseStart_3306944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306958 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3306958 : Nat := 118140960795 + 3306958 * 2 ^ 59
def prefixEnd_3306958 : Nat := 4983230072969 + 3 ^ 40 * 3306958 * 2
def baseEnd_3306958 : Nat := 1698058958231177745316583

theorem tailTrace_3306958 : CollatzResearch.WordTrace tailWord_3306958 prefixEnd_3306958 1698058958231177745316583 := by
  unfold tailWord_3306958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15076833394182928038350191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80409778102308949537867685 15076833394182928038350191)
  ·
    refine ⟨22615250091274392057525287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15076833394182928038350191 22615250091274392057525287)
    ·
      refine ⟨33922875136911588086287931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22615250091274392057525287 33922875136911588086287931)
      ·
        refine ⟨50884312705367382129431897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33922875136911588086287931 50884312705367382129431897)
        ·
          refine ⟨38163234529025536597073923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50884312705367382129431897 38163234529025536597073923)
          ·
            refine ⟨57244851793538304895610885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38163234529025536597073923 57244851793538304895610885)
            ·
              refine ⟨10733409711288432167927041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57244851793538304895610885 10733409711288432167927041)
              ·
                refine ⟨8050057283466324125945281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10733409711288432167927041 8050057283466324125945281)
                ·
                  refine ⟨6037542962599743094458961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8050057283466324125945281 6037542962599743094458961)
                  ·
                    refine ⟨4528157221949807320844221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6037542962599743094458961 4528157221949807320844221)
                    ·
                      refine ⟨1698058958231177745316583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4528157221949807320844221 1698058958231177745316583)
                      ·
                        rfl

theorem cell23_3306958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3306958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306958 prefixEnd_3306958 := by exact prefixLift 3306958
  have htrace : WordTrace (prefixWord ++ tailWord_3306958) baseStart_3306958 baseEnd_3306958 := by
    simpa [prefixWord, tailWord_3306958, baseEnd_3306958] using wordTrace_append hprefix tailTrace_3306958
  have hstable : (prefixWord ++ tailWord_3306958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306958).length < 2 ^ (prefixWord ++ tailWord_3306958).sum := by decide
  have hdescent : baseEnd_3306958 < baseStart_3306958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306965 : List Nat := [1, 3, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_3306965 : Nat := 118140960795 + 3306965 * 2 ^ 59
def prefixEnd_3306965 : Nat := 4983230072969 + 3 ^ 40 * 3306965 * 2
def baseEnd_3306965 : Nat := 566020850865253072643017

theorem tailTrace_3306965 : CollatzResearch.WordTrace tailWord_3306965 prefixEnd_3306965 566020850865253072643017 := by
  unfold tailWord_3306965
  simp only [CollatzResearch.WordTrace]
  refine ⟨120614922464438064502306349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80409948309625376334870899 120614922464438064502306349)
  ·
    refine ⟨45230595924164274188364881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120614922464438064502306349 45230595924164274188364881)
    ·
      refine ⟨33922946943123205641273661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45230595924164274188364881 33922946943123205641273661)
      ·
        refine ⟨12721105103671202115477623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33922946943123205641273661 12721105103671202115477623)
        ·
          refine ⟨19081657655506803173216435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721105103671202115477623 19081657655506803173216435)
          ·
            refine ⟨28622486483260204759824653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19081657655506803173216435 28622486483260204759824653)
            ·
              refine ⟨10733432431222576784934245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28622486483260204759824653 10733432431222576784934245)
              ·
                refine ⟨2012518580854233147175171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10733432431222576784934245 2012518580854233147175171)
                ·
                  refine ⟨3018777871281349720762757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012518580854233147175171 3018777871281349720762757)
                  ·
                    refine ⟨566020850865253072643017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018777871281349720762757 566020850865253072643017)
                    ·
                      rfl

theorem cell23_3306965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_3306965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306965 prefixEnd_3306965 := by exact prefixLift 3306965
  have htrace : WordTrace (prefixWord ++ tailWord_3306965) baseStart_3306965 baseEnd_3306965 := by
    simpa [prefixWord, tailWord_3306965, baseEnd_3306965] using wordTrace_append hprefix tailTrace_3306965
  have hstable : (prefixWord ++ tailWord_3306965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306965).length < 2 ^ (prefixWord ++ tailWord_3306965).sum := by decide
  have hdescent : baseEnd_3306965 < baseStart_3306965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3306991 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 3, 5]
def baseStart_3306991 : Nat := 118140960795 + 3306991 * 2 ^ 59
def prefixEnd_3306991 : Nat := 4983230072969 + 3 ^ 40 * 3306991 * 2
def baseEnd_3306991 : Nat := 566025301030925372067977

theorem tailTrace_3306991 : CollatzResearch.WordTrace tailWord_3306991 prefixEnd_3306991 566025301030925372067977 := by
  unfold tailWord_3306991
  simp only [CollatzResearch.WordTrace]
  refine ⟨120615870762343870942752827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80410580508229247295168551 120615870762343870942752827)
  ·
    refine ⟨180923806143515806414129241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120615870762343870942752827 180923806143515806414129241)
    ·
      refine ⟨135692854607636854810596931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180923806143515806414129241 135692854607636854810596931)
      ·
        refine ⟨203539281911455282215895397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135692854607636854810596931 203539281911455282215895397)
        ·
          refine ⟨38163615358397865415480387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203539281911455282215895397 38163615358397865415480387)
          ·
            refine ⟨57245423037596798123220581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38163615358397865415480387 57245423037596798123220581)
            ·
              refine ⟨10733516819549399648103859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57245423037596798123220581 10733516819549399648103859)
              ·
                refine ⟨16100275229324099472155789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733516819549399648103859 16100275229324099472155789)
                ·
                  refine ⟨6037603210996537302058421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16100275229324099472155789 6037603210996537302058421)
                  ·
                    refine ⟨566025301030925372067977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6037603210996537302058421 566025301030925372067977)
                    ·
                      rfl

theorem cell23_3306991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_3306991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3306991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3306991 prefixEnd_3306991 := by exact prefixLift 3306991
  have htrace : WordTrace (prefixWord ++ tailWord_3306991) baseStart_3306991 baseEnd_3306991 := by
    simpa [prefixWord, tailWord_3306991, baseEnd_3306991] using wordTrace_append hprefix tailTrace_3306991
  have hstable : (prefixWord ++ tailWord_3306991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3306991).length < 2 ^ (prefixWord ++ tailWord_3306991).sum := by decide
  have hdescent : baseEnd_3306991 < baseStart_3306991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3306991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307011 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 4]
def baseStart_3307011 : Nat := 118140960795 + 3307011 * 2 ^ 59
def prefixEnd_3307011 : Nat := 4983230072969 + 3 ^ 40 * 3307011 * 2
def baseEnd_3307011 : Nat := 1698086172705866037953839

theorem tailTrace_3307011 : CollatzResearch.WordTrace tailWord_3307011 prefixEnd_3307011 1698086172705866037953839 := by
  unfold tailWord_3307011
  simp only [CollatzResearch.WordTrace]
  refine ⟨120616600222271414358480887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80411066814847609572320591 120616600222271414358480887)
  ·
    refine ⟨180924900333407121537721331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120616600222271414358480887 180924900333407121537721331)
    ·
      refine ⟨271387350500110682306581997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180924900333407121537721331 271387350500110682306581997)
      ·
        refine ⟨101770256437541505864968249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271387350500110682306581997 101770256437541505864968249)
        ·
          refine ⟨76327692328156129398726187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101770256437541505864968249 76327692328156129398726187)
          ·
            refine ⟨114491538492234194098089281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76327692328156129398726187 114491538492234194098089281)
            ·
              refine ⟨85868653869175645573566961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114491538492234194098089281 85868653869175645573566961)
              ·
                refine ⟨64401490401881734180175221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85868653869175645573566961 64401490401881734180175221)
                ·
                  refine ⟨6037639725176412579391427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64401490401881734180175221 6037639725176412579391427)
                  ·
                    refine ⟨9056459587764618869087141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6037639725176412579391427 9056459587764618869087141)
                    ·
                      refine ⟨1698086172705866037953839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9056459587764618869087141 1698086172705866037953839)
                      ·
                        rfl

theorem cell23_3307011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_3307011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307011 prefixEnd_3307011 := by exact prefixLift 3307011
  have htrace : WordTrace (prefixWord ++ tailWord_3307011) baseStart_3307011 baseEnd_3307011 := by
    simpa [prefixWord, tailWord_3307011, baseEnd_3307011] using wordTrace_append hprefix tailTrace_3307011
  have hstable : (prefixWord ++ tailWord_3307011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307011).length < 2 ^ (prefixWord ++ tailWord_3307011).sum := by decide
  have hdescent : baseEnd_3307011 < baseStart_3307011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307012 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 6]
def baseStart_3307012 : Nat := 118140960795 + 3307012 * 2 ^ 59
def prefixEnd_3307012 : Nat := 4983230072969 + 3 ^ 40 * 3307012 * 2
def baseEnd_3307012 : Nat := 188676298465168948226815

theorem tailTrace_3307012 : CollatzResearch.WordTrace tailWord_3307012 prefixEnd_3307012 188676298465168948226815 := by
  unfold tailWord_3307012
  simp only [CollatzResearch.WordTrace]
  refine ⟨60308318347633895764633645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80411091130178527686178193 60308318347633895764633645)
  ·
    refine ⟨22615619380362710911737617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60308318347633895764633645 22615619380362710911737617)
    ·
      refine ⟨16961714535272033183803213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22615619380362710911737617 16961714535272033183803213)
      ·
        refine ⟨6360642950727012443926205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16961714535272033183803213 6360642950727012443926205)
        ·
          refine ⟨2385241106522629666472327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6360642950727012443926205 2385241106522629666472327)
          ·
            refine ⟨3577861659783944499708491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385241106522629666472327 3577861659783944499708491)
            ·
              refine ⟨5366792489675916749562737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577861659783944499708491 5366792489675916749562737)
              ·
                refine ⟨4025094367256937562172053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366792489675916749562737 4025094367256937562172053)
                ·
                  refine ⟨188676298465168948226815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4025094367256937562172053 188676298465168948226815)
                  ·
                    rfl

theorem cell23_3307012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_3307012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307012 prefixEnd_3307012 := by exact prefixLift 3307012
  have htrace : WordTrace (prefixWord ++ tailWord_3307012) baseStart_3307012 baseEnd_3307012 := by
    simpa [prefixWord, tailWord_3307012, baseEnd_3307012] using wordTrace_append hprefix tailTrace_3307012
  have hstable : (prefixWord ++ tailWord_3307012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307012).length < 2 ^ (prefixWord ++ tailWord_3307012).sum := by decide
  have hdescent : baseEnd_3307012 < baseStart_3307012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307022 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3307022 : Nat := 118140960795 + 3307022 * 2 ^ 59
def prefixEnd_3307022 : Nat := 4983230072969 + 3 ^ 40 * 3307022 * 2
def baseEnd_3307022 : Nat := 1698091820993065494916289

theorem tailTrace_3307022 : CollatzResearch.WordTrace tailWord_3307022 prefixEnd_3307022 1698091820993065494916289 := by
  unfold tailWord_3307022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15077125178153945404641415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80411334283487708824754213 15077125178153945404641415)
  ·
    refine ⟨22615687767230918106962123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15077125178153945404641415 22615687767230918106962123)
    ·
      refine ⟨33923531650846377160443185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22615687767230918106962123 33923531650846377160443185)
      ·
        refine ⟨25442648738134782870332389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33923531650846377160443185 25442648738134782870332389)
        ·
          refine ⟨4770496638400271788187323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25442648738134782870332389 4770496638400271788187323)
          ·
            refine ⟨7155744957600407682280985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4770496638400271788187323 7155744957600407682280985)
            ·
              refine ⟨5366808718200305761710739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7155744957600407682280985 5366808718200305761710739)
              ·
                refine ⟨8050213077300458642566109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366808718200305761710739 8050213077300458642566109)
                ·
                  refine ⟨3018829903987671990962291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8050213077300458642566109 3018829903987671990962291)
                  ·
                    refine ⟨4528244855981507986443437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3018829903987671990962291 4528244855981507986443437)
                    ·
                      refine ⟨1698091820993065494916289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4528244855981507986443437 1698091820993065494916289)
                      ·
                        rfl

theorem cell23_3307022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3307022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307022 prefixEnd_3307022 := by exact prefixLift 3307022
  have htrace : WordTrace (prefixWord ++ tailWord_3307022) baseStart_3307022 baseEnd_3307022 := by
    simpa [prefixWord, tailWord_3307022, baseEnd_3307022] using wordTrace_append hprefix tailTrace_3307022
  have hstable : (prefixWord ++ tailWord_3307022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307022).length < 2 ^ (prefixWord ++ tailWord_3307022).sum := by decide
  have hdescent : baseEnd_3307022 < baseStart_3307022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307065 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3307065 : Nat := 118140960795 + 3307065 * 2 ^ 59
def prefixEnd_3307065 : Nat := 4983230072969 + 3 ^ 40 * 3307065 * 2
def baseEnd_3307065 : Nat := 1698113900661208826678591

theorem tailTrace_3307065 : CollatzResearch.WordTrace tailWord_3307065 prefixEnd_3307065 1698113900661208826678591 := by
  unfold tailWord_3307065
  simp only [CollatzResearch.WordTrace]
  refine ⟨120618569764075781580946649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80412379842717187720631099 120618569764075781580946649)
  ·
    refine ⟨90463927323056836185709987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120618569764075781580946649 90463927323056836185709987)
    ·
      refine ⟨135695890984585254278564981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90463927323056836185709987 135695890984585254278564981)
      ·
        refine ⟨12721489779804867588615467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135695890984585254278564981 12721489779804867588615467)
        ·
          refine ⟨19082234669707301382923201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721489779804867588615467 19082234669707301382923201)
          ·
            refine ⟨14311676002280476037192401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19082234669707301382923201 14311676002280476037192401)
            ·
              refine ⟨10733757001710357027894301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14311676002280476037192401 10733757001710357027894301)
              ·
                refine ⟨4025158875641383885460363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10733757001710357027894301 4025158875641383885460363)
                ·
                  refine ⟨6037738313462075828190545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025158875641383885460363 6037738313462075828190545)
                  ·
                    refine ⟨4528303735096556871142909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6037738313462075828190545 4528303735096556871142909)
                    ·
                      refine ⟨1698113900661208826678591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4528303735096556871142909 1698113900661208826678591)
                      ·
                        rfl

theorem cell23_3307065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3307065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307065 prefixEnd_3307065 := by exact prefixLift 3307065
  have htrace : WordTrace (prefixWord ++ tailWord_3307065) baseStart_3307065 baseEnd_3307065 := by
    simpa [prefixWord, tailWord_3307065, baseEnd_3307065] using wordTrace_append hprefix tailTrace_3307065
  have hstable : (prefixWord ++ tailWord_3307065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307065).length < 2 ^ (prefixWord ++ tailWord_3307065).sum := by decide
  have hdescent : baseEnd_3307065 < baseStart_3307065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307068 : List Nat := [2, 2, 2, 2, 4, 2, 9]
def baseStart_3307068 : Nat := 118140960795 + 3307068 * 2 ^ 59
def prefixEnd_3307068 : Nat := 4983230072969 + 3 ^ 40 * 3307068 * 2
def baseEnd_3307068 : Nat := 20964388161767559443717

theorem tailTrace_3307068 : CollatzResearch.WordTrace tailWord_3307068 prefixEnd_3307068 20964388161767559443717 := by
  unfold tailWord_3307068
  simp only [CollatzResearch.WordTrace]
  refine ⟨60309339591532456546652929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80412452788709942062203905 60309339591532456546652929)
  ·
    refine ⟨45232004693649342409989697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60309339591532456546652929 45232004693649342409989697)
    ·
      refine ⟨33924003520237006807492273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45232004693649342409989697 33924003520237006807492273)
      ·
        refine ⟨25443002640177755105619205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33924003520237006807492273 25443002640177755105619205)
        ·
          refine ⟨4770562995033329082303601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25443002640177755105619205 4770562995033329082303601)
          ·
            refine ⟨3577922246274996811727701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4770562995033329082303601 3577922246274996811727701)
            ·
              refine ⟨20964388161767559443717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3577922246274996811727701 20964388161767559443717)
              ·
                rfl

theorem cell23_3307068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 9].length) (baseStart_3307068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307068 prefixEnd_3307068 := by exact prefixLift 3307068
  have htrace : WordTrace (prefixWord ++ tailWord_3307068) baseStart_3307068 baseEnd_3307068 := by
    simpa [prefixWord, tailWord_3307068, baseEnd_3307068] using wordTrace_append hprefix tailTrace_3307068
  have hstable : (prefixWord ++ tailWord_3307068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307068).length < 2 ^ (prefixWord ++ tailWord_3307068).sum := by decide
  have hdescent : baseEnd_3307068 < baseStart_3307068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307079 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_3307079 : Nat := 118140960795 + 3307079 * 2 ^ 59
def prefixEnd_3307079 : Nat := 4983230072969 + 3 ^ 40 * 3307079 * 2
def baseEnd_3307079 : Nat := 1698121089390371771903527

theorem tailTrace_3307079 : CollatzResearch.WordTrace tailWord_3307079 prefixEnd_3307079 1698121089390371771903527 := by
  unfold tailWord_3307079
  simp only [CollatzResearch.WordTrace]
  refine ⟨120619080386025061971956291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80412720257350041314637527 120619080386025061971956291)
  ·
    refine ⟨180928620579037592957934437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120619080386025061971956291 180928620579037592957934437)
    ·
      refine ⟨33924116358569548679612707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180928620579037592957934437 33924116358569548679612707)
      ·
        refine ⟨50886174537854323019419061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33924116358569548679612707 50886174537854323019419061)
        ·
          refine ⟨4770578862923842783070537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50886174537854323019419061 4770578862923842783070537)
          ·
            refine ⟨3577934147192882087302903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4770578862923842783070537 3577934147192882087302903)
            ·
              refine ⟨5366901220789323130954355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577934147192882087302903 5366901220789323130954355)
              ·
                refine ⟨8050351831183984696431533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366901220789323130954355 8050351831183984696431533)
                ·
                  refine ⟨3018881936693994261161825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8050351831183984696431533 3018881936693994261161825)
                  ·
                    refine ⟨2264161452520495695871369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018881936693994261161825 2264161452520495695871369)
                    ·
                      refine ⟨1698121089390371771903527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264161452520495695871369 1698121089390371771903527)
                      ·
                        rfl

theorem cell23_3307079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_3307079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307079 prefixEnd_3307079 := by exact prefixLift 3307079
  have htrace : WordTrace (prefixWord ++ tailWord_3307079) baseStart_3307079 baseEnd_3307079 := by
    simpa [prefixWord, tailWord_3307079, baseEnd_3307079] using wordTrace_append hprefix tailTrace_3307079
  have hstable : (prefixWord ++ tailWord_3307079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307079).length < 2 ^ (prefixWord ++ tailWord_3307079).sum := by decide
  have hdescent : baseEnd_3307079 < baseStart_3307079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307085 : List Nat := [1, 6, 1, 1, 3, 1, 2, 8]
def baseStart_3307085 : Nat := 118140960795 + 3307085 * 2 ^ 59
def prefixEnd_3307085 : Nat := 4983230072969 + 3 ^ 40 * 3307085 * 2
def baseEnd_3307085 : Nat := 62893487787936990682537

theorem tailTrace_3307085 : CollatzResearch.WordTrace tailWord_3307085 prefixEnd_3307085 62893487787936990682537 := by
  unfold tailWord_3307085
  simp only [CollatzResearch.WordTrace]
  refine ⟨120619299224003324996674709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80412866149335549997783139 120619299224003324996674709)
  ·
    refine ⟨5654029651125155859219127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120619299224003324996674709 5654029651125155859219127)
    ·
      refine ⟨8481044476687733788828691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654029651125155859219127 8481044476687733788828691)
      ·
        refine ⟨12721566715031600683243037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8481044476687733788828691 12721566715031600683243037)
        ·
          refine ⟨4770587518136850256216139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12721566715031600683243037 4770587518136850256216139)
          ·
            refine ⟨7155881277205275384324209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4770587518136850256216139 7155881277205275384324209)
            ·
              refine ⟨5366910957903956538243157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7155881277205275384324209 5366910957903956538243157)
              ·
                refine ⟨62893487787936990682537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5366910957903956538243157 62893487787936990682537)
                ·
                  rfl

theorem cell23_3307085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 8].length) (baseStart_3307085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307085 prefixEnd_3307085 := by exact prefixLift 3307085
  have htrace : WordTrace (prefixWord ++ tailWord_3307085) baseStart_3307085 baseEnd_3307085 := by
    simpa [prefixWord, tailWord_3307085, baseEnd_3307085] using wordTrace_append hprefix tailTrace_3307085
  have hstable : (prefixWord ++ tailWord_3307085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307085).length < 2 ^ (prefixWord ++ tailWord_3307085).sum := by decide
  have hdescent : baseEnd_3307085 < baseStart_3307085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307105 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_3307105 : Nat := 118140960795 + 3307105 * 2 ^ 59
def prefixEnd_3307105 : Nat := 4983230072969 + 3 ^ 40 * 3307105 * 2
def baseEnd_3307105 : Nat := 1698134439887388670178407

theorem tailTrace_3307105 : CollatzResearch.WordTrace tailWord_3307105 prefixEnd_3307105 1698134439887388670178407 := by
  unfold tailWord_3307105
  simp only [CollatzResearch.WordTrace]
  refine ⟨120620028683930868412402769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80413352455953912274935179 120620028683930868412402769)
  ·
    refine ⟨90465021512948151309302077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120620028683930868412402769 90465021512948151309302077)
    ·
      refine ⟨33924383067355556740988279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90465021512948151309302077 33924383067355556740988279)
      ·
        refine ⟨50886574601033335111482419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33924383067355556740988279 50886574601033335111482419)
        ·
          refine ⟨76329861901550002667223629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50886574601033335111482419 76329861901550002667223629)
          ·
            refine ⟨28623698213081251000208861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76329861901550002667223629 28623698213081251000208861)
            ·
              refine ⟨10733886829905469125078323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28623698213081251000208861 10733886829905469125078323)
              ·
                refine ⟨16100830244858203687617485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733886829905469125078323 16100830244858203687617485)
                ·
                  refine ⟨6037811341821826382856557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16100830244858203687617485 6037811341821826382856557)
                  ·
                    refine ⟨2264179253183184893571209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6037811341821826382856557 2264179253183184893571209)
                    ·
                      refine ⟨1698134439887388670178407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264179253183184893571209 1698134439887388670178407)
                      ·
                        rfl

theorem cell23_3307105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_3307105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307105 prefixEnd_3307105 := by exact prefixLift 3307105
  have htrace : WordTrace (prefixWord ++ tailWord_3307105) baseStart_3307105 baseEnd_3307105 := by
    simpa [prefixWord, tailWord_3307105, baseEnd_3307105] using wordTrace_append hprefix tailTrace_3307105
  have hstable : (prefixWord ++ tailWord_3307105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307105).length < 2 ^ (prefixWord ++ tailWord_3307105).sum := by decide
  have hdescent : baseEnd_3307105 < baseStart_3307105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307135 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 8, 2, 2]
def baseStart_3307135 : Nat := 118140960795 + 3307135 * 2 ^ 59
def prefixEnd_3307135 : Nat := 4983230072969 + 3 ^ 40 * 3307135 * 2
def baseEnd_3307135 : Nat := 1698149844307023552803269

theorem tailTrace_3307135 : CollatzResearch.WordTrace tailWord_3307135 prefixEnd_3307135 1698149844307023552803269 := by
  unfold tailWord_3307135
  simp only [CollatzResearch.WordTrace]
  refine ⟨120621122873822183535994859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80414081915881455690663239 120621122873822183535994859)
  ·
    refine ⟨180931684310733275303992289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120621122873822183535994859 180931684310733275303992289)
    ·
      refine ⟨135698763233049956477994217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180931684310733275303992289 135698763233049956477994217)
      ·
        refine ⟨101774072424787467358495663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135698763233049956477994217 101774072424787467358495663)
        ·
          refine ⟨152661108637181201037743495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101774072424787467358495663 152661108637181201037743495)
          ·
            refine ⟨228991662955771801556615243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152661108637181201037743495 228991662955771801556615243)
            ·
              refine ⟨343487494433657702334922865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228991662955771801556615243 343487494433657702334922865)
              ·
                refine ⟨257615620825243276751192149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343487494433657702334922865 257615620825243276751192149)
                ·
                  refine ⟨3018933056545819649428033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 257615620825243276751192149 3018933056545819649428033)
                  ·
                    refine ⟨2264199792409364737071025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018933056545819649428033 2264199792409364737071025)
                    ·
                      refine ⟨1698149844307023552803269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264199792409364737071025 1698149844307023552803269)
                      ·
                        rfl

theorem cell23_3307135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_3307135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307135 prefixEnd_3307135 := by exact prefixLift 3307135
  have htrace : WordTrace (prefixWord ++ tailWord_3307135) baseStart_3307135 baseEnd_3307135 := by
    simpa [prefixWord, tailWord_3307135, baseEnd_3307135] using wordTrace_append hprefix tailTrace_3307135
  have hstable : (prefixWord ++ tailWord_3307135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307135).length < 2 ^ (prefixWord ++ tailWord_3307135).sum := by decide
  have hdescent : baseEnd_3307135 < baseStart_3307135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307148 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3307148 : Nat := 118140960795 + 3307148 * 2 ^ 59
def prefixEnd_3307148 : Nat := 4983230072969 + 3 ^ 40 * 3307148 * 2
def baseEnd_3307148 : Nat := 1698156519555532001940709

theorem tailTrace_3307148 : CollatzResearch.WordTrace tailWord_3307148 prefixEnd_3307148 1698156519555532001940709 := by
  unfold tailWord_3307148
  simp only [CollatzResearch.WordTrace]
  refine ⟨60310798511387543378109049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80414398015183391170812065 60310798511387543378109049)
  ·
    refine ⟨45233098883540657533581787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60310798511387543378109049 45233098883540657533581787)
    ·
      refine ⟨67849648325310986300372681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45233098883540657533581787 67849648325310986300372681)
      ·
        refine ⟨50887236243983239725279511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67849648325310986300372681 50887236243983239725279511)
        ·
          refine ⟨76330854365974859587919267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50887236243983239725279511 76330854365974859587919267)
          ·
            refine ⟨114496281548962289381878901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76330854365974859587919267 114496281548962289381878901)
            ·
              refine ⟨10734026395215214629551147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114496281548962289381878901 10734026395215214629551147)
              ·
                refine ⟨16101039592822821944326721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10734026395215214629551147 16101039592822821944326721)
                ·
                  refine ⟨12075779694617116458245041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16101039592822821944326721 12075779694617116458245041)
                  ·
                    refine ⟨9056834770962837343683781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12075779694617116458245041 9056834770962837343683781)
                    ·
                      refine ⟨1698156519555532001940709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9056834770962837343683781 1698156519555532001940709)
                      ·
                        rfl

theorem cell23_3307148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3307148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307148 prefixEnd_3307148 := by exact prefixLift 3307148
  have htrace : WordTrace (prefixWord ++ tailWord_3307148) baseStart_3307148 baseEnd_3307148 := by
    simpa [prefixWord, tailWord_3307148, baseEnd_3307148] using wordTrace_append hprefix tailTrace_3307148
  have hstable : (prefixWord ++ tailWord_3307148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307148).length < 2 ^ (prefixWord ++ tailWord_3307148).sum := by decide
  have hdescent : baseEnd_3307148 < baseStart_3307148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307208 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3307208 : Nat := 118140960795 + 3307208 * 2 ^ 59
def prefixEnd_3307208 : Nat := 4983230072969 + 3 ^ 40 * 3307208 * 2
def baseEnd_3307208 : Nat := 1698187328394801767190433

theorem tailTrace_3307208 : CollatzResearch.WordTrace tailWord_3307208 prefixEnd_3307208 1698187328394801767190433 := by
  unfold tailWord_3307208
  simp only [CollatzResearch.WordTrace]
  refine ⟨60311892701278858501701139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80415856935038478002268185 60311892701278858501701139)
  ·
    refine ⟨90467839051918287752551709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60311892701278858501701139 90467839051918287752551709)
    ·
      refine ⟨33925439644469357907206891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90467839051918287752551709 33925439644469357907206891)
      ·
        refine ⟨50888159466704036860810337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33925439644469357907206891 50888159466704036860810337)
        ·
          refine ⟨38166119600028027645607753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50888159466704036860810337 38166119600028027645607753)
          ·
            refine ⟨28624589700021020734205815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38166119600028027645607753 28624589700021020734205815)
            ·
              refine ⟨42936884550031531101308723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28624589700021020734205815 42936884550031531101308723)
              ·
                refine ⟨64405326825047296651963085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42936884550031531101308723 64405326825047296651963085)
                ·
                  refine ⟨24151997559392736244486157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64405326825047296651963085 24151997559392736244486157)
                  ·
                    refine ⟨9056999084772276091682309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24151997559392736244486157 9056999084772276091682309)
                    ·
                      refine ⟨1698187328394801767190433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9056999084772276091682309 1698187328394801767190433)
                      ·
                        rfl

theorem cell23_3307208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3307208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307208 prefixEnd_3307208 := by exact prefixLift 3307208
  have htrace : WordTrace (prefixWord ++ tailWord_3307208) baseStart_3307208 baseEnd_3307208 := by
    simpa [prefixWord, tailWord_3307208, baseEnd_3307208] using wordTrace_append hprefix tailTrace_3307208
  have hstable : (prefixWord ++ tailWord_3307208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307208).length < 2 ^ (prefixWord ++ tailWord_3307208).sum := by decide
  have hdescent : baseEnd_3307208 < baseStart_3307208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307349 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_3307349 : Nat := 118140960795 + 3307349 * 2 ^ 59
def prefixEnd_3307349 : Nat := 4983230072969 + 3 ^ 40 * 3307349 * 2
def baseEnd_3307349 : Nat := 1698259729167085715527285

theorem tailTrace_3307349 : CollatzResearch.WordTrace tailWord_3307349 prefixEnd_3307349 1698259729167085715527285 := by
  unfold tailWord_3307349
  simp only [CollatzResearch.WordTrace]
  refine ⟨120628928095046898084285101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80419285396697932056190067 120628928095046898084285101)
  ·
    refine ⟨45235848035642586781606913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120628928095046898084285101 45235848035642586781606913)
    ·
      refine ⟨33926886026731940086205185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45235848035642586781606913 33926886026731940086205185)
      ·
        refine ⟨25445164520048955064653889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33926886026731940086205185 25445164520048955064653889)
        ·
          refine ⟨19083873390036716298490417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25445164520048955064653889 19083873390036716298490417)
          ·
            refine ⟨14312905042527537223867813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19083873390036716298490417 14312905042527537223867813)
            ·
              refine ⟨2683669695473913229475215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14312905042527537223867813 2683669695473913229475215)
              ·
                refine ⟨4025504543210869844212823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683669695473913229475215 4025504543210869844212823)
                ·
                  refine ⟨6038256814816304766319235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025504543210869844212823 6038256814816304766319235)
                  ·
                    refine ⟨9057385222224457149478853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6038256814816304766319235 9057385222224457149478853)
                    ·
                      refine ⟨1698259729167085715527285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9057385222224457149478853 1698259729167085715527285)
                      ·
                        rfl

theorem cell23_3307349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_3307349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307349 prefixEnd_3307349 := by exact prefixLift 3307349
  have htrace : WordTrace (prefixWord ++ tailWord_3307349) baseStart_3307349 baseEnd_3307349 := by
    simpa [prefixWord, tailWord_3307349, baseEnd_3307349] using wordTrace_append hprefix tailTrace_3307349
  have hstable : (prefixWord ++ tailWord_3307349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307349).length < 2 ^ (prefixWord ++ tailWord_3307349).sum := by decide
  have hdescent : baseEnd_3307349 < baseStart_3307349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307359 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 2, 4]
def baseStart_3307359 : Nat := 118140960795 + 3307359 * 2 ^ 59
def prefixEnd_3307359 : Nat := 4983230072969 + 3 ^ 40 * 3307359 * 2
def baseEnd_3307359 : Nat := 566088287991210225467413

theorem tailTrace_3307359 : CollatzResearch.WordTrace tailWord_3307359 prefixEnd_3307359 566088287991210225467413 := by
  unfold tailWord_3307359
  simp only [CollatzResearch.WordTrace]
  refine ⟨120629292825010669792149131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80419528550007113194766087 120629292825010669792149131)
  ·
    refine ⟨180943939237516004688223697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120629292825010669792149131 180943939237516004688223697)
    ·
      refine ⟨135707954428137003516167773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180943939237516004688223697 135707954428137003516167773)
      ·
        refine ⟨50890482910551376318562915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135707954428137003516167773 50890482910551376318562915)
        ·
          refine ⟨76335724365827064477844373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50890482910551376318562915 76335724365827064477844373)
          ·
            refine ⟨3578237079648143647398955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76335724365827064477844373 3578237079648143647398955)
            ·
              refine ⟨5367355619472215471098433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578237079648143647398955 5367355619472215471098433)
              ·
                refine ⟨4025516714604161603323825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367355619472215471098433 4025516714604161603323825)
                ·
                  refine ⟨3019137535953121202492869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4025516714604161603323825 3019137535953121202492869)
                  ·
                    refine ⟨566088287991210225467413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019137535953121202492869 566088287991210225467413)
                    ·
                      rfl

theorem cell23_3307359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_3307359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307359 prefixEnd_3307359 := by exact prefixLift 3307359
  have htrace : WordTrace (prefixWord ++ tailWord_3307359) baseStart_3307359 baseEnd_3307359 := by
    simpa [prefixWord, tailWord_3307359, baseEnd_3307359] using wordTrace_append hprefix tailTrace_3307359
  have hstable : (prefixWord ++ tailWord_3307359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307359).length < 2 ^ (prefixWord ++ tailWord_3307359).sum := by decide
  have hdescent : baseEnd_3307359 < baseStart_3307359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307395 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5]
def baseStart_3307395 : Nat := 118140960795 + 3307395 * 2 ^ 59
def prefixEnd_3307395 : Nat := 4983230072969 + 3 ^ 40 * 3307395 * 2
def baseEnd_3307395 : Nat := 1698283349277192535552073

theorem tailTrace_3307395 : CollatzResearch.WordTrace tailWord_3307395 prefixEnd_3307395 1698283349277192535552073 := by
  unfold tailWord_3307395
  simp only [CollatzResearch.WordTrace]
  refine ⟨120630605852880247940459639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80420403901920165293639759 120630605852880247940459639)
  ·
    refine ⟨180945908779320371910689459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120630605852880247940459639 180945908779320371910689459)
    ·
      refine ⟨271418863168980557866034189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180945908779320371910689459 271418863168980557866034189)
      ·
        refine ⟨101782073688367709199762821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271418863168980557866034189 101782073688367709199762821)
        ·
          refine ⟨19084138816568945474955529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101782073688367709199762821 19084138816568945474955529)
          ·
            refine ⟨14313104112426709106216647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19084138816568945474955529 14313104112426709106216647)
            ·
              refine ⟨21469656168640063659324971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14313104112426709106216647 21469656168640063659324971)
              ·
                refine ⟨32204484252960095488987457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21469656168640063659324971 32204484252960095488987457)
                ·
                  refine ⟨24153363189720071616740593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32204484252960095488987457 24153363189720071616740593)
                  ·
                    refine ⟨18115022392290053712555445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24153363189720071616740593 18115022392290053712555445)
                    ·
                      refine ⟨1698283349277192535552073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18115022392290053712555445 1698283349277192535552073)
                      ·
                        rfl

theorem cell23_3307395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_3307395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307395 prefixEnd_3307395 := by exact prefixLift 3307395
  have htrace : WordTrace (prefixWord ++ tailWord_3307395) baseStart_3307395 baseEnd_3307395 := by
    simpa [prefixWord, tailWord_3307395, baseEnd_3307395] using wordTrace_append hprefix tailTrace_3307395
  have hstable : (prefixWord ++ tailWord_3307395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307395).length < 2 ^ (prefixWord ++ tailWord_3307395).sum := by decide
  have hdescent : baseEnd_3307395 < baseStart_3307395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307400 : List Nat := [2, 1, 3, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_3307400 : Nat := 118140960795 + 3307400 * 2 ^ 59
def prefixEnd_3307400 : Nat := 4983230072969 + 3 ^ 40 * 3307400 * 2
def baseEnd_3307400 : Nat := 1698285916680465015989551

theorem tailTrace_3307400 : CollatzResearch.WordTrace tailWord_3307400 prefixEnd_3307400 1698285916680465015989551 := by
  unfold tailWord_3307400
  simp only [CollatzResearch.WordTrace]
  refine ⟨60315394108931066897195827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80420525478574755862927769 60315394108931066897195827)
  ·
    refine ⟨90473091163396600345793741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60315394108931066897195827 90473091163396600345793741)
    ·
      refine ⟨33927409186273725129672653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90473091163396600345793741 33927409186273725129672653)
      ·
        refine ⟨12722778444852646923627245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33927409186273725129672653 12722778444852646923627245)
        ·
          refine ⟨4771041916819742596360217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12722778444852646923627245 4771041916819742596360217)
          ·
            refine ⟨3578281437614806947270163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771041916819742596360217 3578281437614806947270163)
            ·
              refine ⟨5367422156422210420905245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578281437614806947270163 5367422156422210420905245)
              ·
                refine ⟨2012783308658328907839467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5367422156422210420905245 2012783308658328907839467)
                ·
                  refine ⟨3019174962987493361759201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012783308658328907839467 3019174962987493361759201)
                  ·
                    refine ⟨2264381222240620021319401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3019174962987493361759201 2264381222240620021319401)
                    ·
                      refine ⟨1698285916680465015989551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264381222240620021319401 1698285916680465015989551)
                      ·
                        rfl

theorem cell23_3307400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_3307400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307400 prefixEnd_3307400 := by exact prefixLift 3307400
  have htrace : WordTrace (prefixWord ++ tailWord_3307400) baseStart_3307400 baseEnd_3307400 := by
    simpa [prefixWord, tailWord_3307400, baseEnd_3307400] using wordTrace_append hprefix tailTrace_3307400
  have hstable : (prefixWord ++ tailWord_3307400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307400).length < 2 ^ (prefixWord ++ tailWord_3307400).sum := by decide
  have hdescent : baseEnd_3307400 < baseStart_3307400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307409 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 1, 3, 2]
def baseStart_3307409 : Nat := 118140960795 + 3307409 * 2 ^ 59
def prefixEnd_3307409 : Nat := 4983230072969 + 3 ^ 40 * 3307409 * 2
def baseEnd_3307409 : Nat := 1698290538006355480777009

theorem tailTrace_3307409 : CollatzResearch.WordTrace tailWord_3307409 prefixEnd_3307409 1698290538006355480777009 := by
  unfold tailWord_3307409
  simp only [CollatzResearch.WordTrace]
  refine ⟨120631116474829528331469281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80420744316553018887646187 120631116474829528331469281)
  ·
    refine ⟨90473337356122146248601961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120631116474829528331469281 90473337356122146248601961)
    ·
      refine ⟨67855003017091609686451471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90473337356122146248601961 67855003017091609686451471)
      ·
        refine ⟨101782504525637414529677207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67855003017091609686451471 101782504525637414529677207)
        ·
          refine ⟨152673756788456121794515811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101782504525637414529677207 152673756788456121794515811)
          ·
            refine ⟨229010635182684182691773717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152673756788456121794515811 229010635182684182691773717)
            ·
              refine ⟨10734873524188321063676893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229010635182684182691773717 10734873524188321063676893)
              ·
                refine ⟨4025577571570620398878835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10734873524188321063676893 4025577571570620398878835)
                ·
                  refine ⟨6038366357355930598318253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025577571570620398878835 6038366357355930598318253)
                  ·
                    refine ⟨2264387384008473974369345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6038366357355930598318253 2264387384008473974369345)
                    ·
                      refine ⟨1698290538006355480777009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264387384008473974369345 1698290538006355480777009)
                      ·
                        rfl

theorem cell23_3307409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_3307409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307409 prefixEnd_3307409 := by exact prefixLift 3307409
  have htrace : WordTrace (prefixWord ++ tailWord_3307409) baseStart_3307409 baseEnd_3307409 := by
    simpa [prefixWord, tailWord_3307409, baseEnd_3307409] using wordTrace_append hprefix tailTrace_3307409
  have hstable : (prefixWord ++ tailWord_3307409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307409).length < 2 ^ (prefixWord ++ tailWord_3307409).sum := by decide
  have hdescent : baseEnd_3307409 < baseStart_3307409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307549 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3307549 : Nat := 118140960795 + 3307549 * 2 ^ 59
def prefixEnd_3307549 : Nat := 4983230072969 + 3 ^ 40 * 3307549 * 2
def baseEnd_3307549 : Nat := 1698362425297984933026365

theorem tailTrace_3307549 : CollatzResearch.WordTrace tailWord_3307549 prefixEnd_3307549 1698362425297984933026365 := by
  unfold tailWord_3307549
  simp only [CollatzResearch.WordTrace]
  refine ⟨120636222694322332241565701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80424148462881554827710467 120636222694322332241565701)
  ·
    refine ⟨22619291755185437295293569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120636222694322332241565701 22619291755185437295293569)
    ·
      refine ⟨16964468816389077971470177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22619291755185437295293569 16964468816389077971470177)
      ·
        refine ⟨12723351612291808478602633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16964468816389077971470177 12723351612291808478602633)
        ·
          refine ⟨9542513709218856358951975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12723351612291808478602633 9542513709218856358951975)
          ·
            refine ⟨14313770563828284538427963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542513709218856358951975 14313770563828284538427963)
            ·
              refine ⟨21470655845742426807641945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14313770563828284538427963 21470655845742426807641945)
              ·
                refine ⟨16102991884306820105731459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21470655845742426807641945 16102991884306820105731459)
                ·
                  refine ⟨24154487826460230158597189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16102991884306820105731459 24154487826460230158597189)
                  ·
                    refine ⟨4528966467461293154736973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24154487826460230158597189 4528966467461293154736973)
                    ·
                      refine ⟨1698362425297984933026365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4528966467461293154736973 1698362425297984933026365)
                      ·
                        rfl

theorem cell23_3307549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3307549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307549 prefixEnd_3307549 := by exact prefixLift 3307549
  have htrace : WordTrace (prefixWord ++ tailWord_3307549) baseStart_3307549 baseEnd_3307549 := by
    simpa [prefixWord, tailWord_3307549, baseEnd_3307549] using wordTrace_append hprefix tailTrace_3307549
  have hstable : (prefixWord ++ tailWord_3307549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307549).length < 2 ^ (prefixWord ++ tailWord_3307549).sum := by decide
  have hdescent : baseEnd_3307549 < baseStart_3307549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307596 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3307596 : Nat := 118140960795 + 3307596 * 2 ^ 59
def prefixEnd_3307596 : Nat := 4983230072969 + 3 ^ 40 * 3307596 * 2
def baseEnd_3307596 : Nat := 1698386558888746249138649

theorem tailTrace_3307596 : CollatzResearch.WordTrace tailWord_3307596 prefixEnd_3307596 1698386558888746249138649 := by
  unfold tailWord_3307596
  simp only [CollatzResearch.WordTrace]
  refine ⟨60318968462576029634263321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80425291283434706179017761 60318968462576029634263321)
  ·
    refine ⟨45239226346932022225697491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60318968462576029634263321 45239226346932022225697491)
    ·
      refine ⟨67858839520398033338546237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45239226346932022225697491 67858839520398033338546237)
      ·
        refine ⟨25447064820149262501954839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67858839520398033338546237 25447064820149262501954839)
        ·
          refine ⟨38170597230223893752932259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25447064820149262501954839 38170597230223893752932259)
          ·
            refine ⟨57255895845335840629398389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38170597230223893752932259 57255895845335840629398389)
            ·
              refine ⟨5367740235500235059006099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57255895845335840629398389 5367740235500235059006099)
              ·
                refine ⟨8051610353250352588509149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367740235500235059006099 8051610353250352588509149)
                ·
                  refine ⟨3019353882468882220690931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8051610353250352588509149 3019353882468882220690931)
                  ·
                    refine ⟨4529030823703323331036397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3019353882468882220690931 4529030823703323331036397)
                    ·
                      refine ⟨1698386558888746249138649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529030823703323331036397 1698386558888746249138649)
                      ·
                        rfl

theorem cell23_3307596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3307596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307596 prefixEnd_3307596 := by exact prefixLift 3307596
  have htrace : WordTrace (prefixWord ++ tailWord_3307596) baseStart_3307596 baseEnd_3307596 := by
    simpa [prefixWord, tailWord_3307596, baseEnd_3307596] using wordTrace_append hprefix tailTrace_3307596
  have hstable : (prefixWord ++ tailWord_3307596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307596).length < 2 ^ (prefixWord ++ tailWord_3307596).sum := by decide
  have hdescent : baseEnd_3307596 < baseStart_3307596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307616 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 1, 5]
def baseStart_3307616 : Nat := 118140960795 + 3307616 * 2 ^ 59
def prefixEnd_3307616 : Nat := 4983230072969 + 3 ^ 40 * 3307616 * 2
def baseEnd_3307616 : Nat := 566132276167278723629519

theorem tailTrace_3307616 : CollatzResearch.WordTrace tailWord_3307616 prefixEnd_3307616 566132276167278723629519 := by
  unfold tailWord_3307616
  simp only [CollatzResearch.WordTrace]
  refine ⟨60319333192539801342127351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80425777590053068456169801 60319333192539801342127351)
  ·
    refine ⟨90478999788809702013191027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60319333192539801342127351 90478999788809702013191027)
    ·
      refine ⟨135718499683214553019786541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90478999788809702013191027 135718499683214553019786541)
      ·
        refine ⟨50894437381205457382419953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135718499683214553019786541 50894437381205457382419953)
        ·
          refine ⟨38170828035904093036814965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50894437381205457382419953 38170828035904093036814965)
          ·
            refine ⟨3578515128366008722201403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38170828035904093036814965 3578515128366008722201403)
            ·
              refine ⟨5367772692549013083302105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578515128366008722201403 5367772692549013083302105)
              ·
                refine ⟨4025829519411759812476579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367772692549013083302105 4025829519411759812476579)
                ·
                  refine ⟨6038744279117639718714869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025829519411759812476579 6038744279117639718714869)
                  ·
                    refine ⟨566132276167278723629519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6038744279117639718714869 566132276167278723629519)
                    ·
                      rfl

theorem cell23_3307616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_3307616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307616 prefixEnd_3307616 := by exact prefixLift 3307616
  have htrace : WordTrace (prefixWord ++ tailWord_3307616) baseStart_3307616 baseEnd_3307616 := by
    simpa [prefixWord, tailWord_3307616, baseEnd_3307616] using wordTrace_append hprefix tailTrace_3307616
  have hstable : (prefixWord ++ tailWord_3307616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307616).length < 2 ^ (prefixWord ++ tailWord_3307616).sum := by decide
  have hdescent : baseEnd_3307616 < baseStart_3307616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307619 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 2, 6, 2]
def baseStart_3307619 : Nat := 118140960795 + 3307619 * 2 ^ 59
def prefixEnd_3307619 : Nat := 4983230072969 + 3 ^ 40 * 3307619 * 2
def baseEnd_3307619 : Nat := 1698398368943799659151043

theorem tailTrace_3307619 : CollatzResearch.WordTrace tailWord_3307619 prefixEnd_3307619 1698398368943799659151043 := by
  unfold tailWord_3307619
  simp only [CollatzResearch.WordTrace]
  refine ⟨120638775804068734196613911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80425850536045822797742607 120638775804068734196613911)
  ·
    refine ⟨180958163706103101294920867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120638775804068734196613911 180958163706103101294920867)
    ·
      refine ⟨271437245559154651942381301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180958163706103101294920867 271437245559154651942381301)
      ·
        refine ⟨25447241771170748619598247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271437245559154651942381301 25447241771170748619598247)
        ·
          refine ⟨38170862656756122929397371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25447241771170748619598247 38170862656756122929397371)
          ·
            refine ⟨57256293985134184394096057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38170862656756122929397371 57256293985134184394096057)
            ·
              refine ⟨42942220488850638295572043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57256293985134184394096057 42942220488850638295572043)
              ·
                refine ⟨64413330733275957443358065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42942220488850638295572043 64413330733275957443358065)
                ·
                  refine ⟨48309998049956968082518549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64413330733275957443358065 48309998049956968082518549)
                  ·
                    refine ⟨2264531158591732878868057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48309998049956968082518549 2264531158591732878868057)
                    ·
                      refine ⟨1698398368943799659151043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264531158591732878868057 1698398368943799659151043)
                      ·
                        rfl

theorem cell23_3307619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_3307619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307619 prefixEnd_3307619 := by exact prefixLift 3307619
  have htrace : WordTrace (prefixWord ++ tailWord_3307619) baseStart_3307619 baseEnd_3307619 := by
    simpa [prefixWord, tailWord_3307619, baseEnd_3307619] using wordTrace_append hprefix tailTrace_3307619
  have hstable : (prefixWord ++ tailWord_3307619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307619).length < 2 ^ (prefixWord ++ tailWord_3307619).sum := by decide
  have hdescent : baseEnd_3307619 < baseStart_3307619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307629 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_3307629 : Nat := 118140960795 + 3307629 * 2 ^ 59
def prefixEnd_3307629 : Nat := 4983230072969 + 3 ^ 40 * 3307629 * 2
def baseEnd_3307629 : Nat := 566134501250114873341999

theorem tailTrace_3307629 : CollatzResearch.WordTrace tailWord_3307629 prefixEnd_3307629 566134501250114873341999 := by
  unfold tailWord_3307629
  simp only [CollatzResearch.WordTrace]
  refine ⟨120639140534032505904477941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80426093689355003936318627 120639140534032505904477941)
  ·
    refine ⟨11309919425065547428544807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120639140534032505904477941 11309919425065547428544807)
    ·
      refine ⟨16964879137598321142817211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11309919425065547428544807 16964879137598321142817211)
      ·
        refine ⟨25447318706397481714225817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16964879137598321142817211 25447318706397481714225817)
        ·
          refine ⟨19085489029798111285669363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25447318706397481714225817 19085489029798111285669363)
          ·
            refine ⟨28628233544697166928504045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19085489029798111285669363 28628233544697166928504045)
            ·
              refine ⟨10735587579261437598189017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28628233544697166928504045 10735587579261437598189017)
              ·
                refine ⟨8051690684446078198641763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10735587579261437598189017 8051690684446078198641763)
                ·
                  refine ⟨12077536026669117297962645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8051690684446078198641763 12077536026669117297962645)
                  ·
                    refine ⟨566134501250114873341999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12077536026669117297962645 566134501250114873341999)
                    ·
                      rfl

theorem cell23_3307629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_3307629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307629 prefixEnd_3307629 := by exact prefixLift 3307629
  have htrace : WordTrace (prefixWord ++ tailWord_3307629) baseStart_3307629 baseEnd_3307629 := by
    simpa [prefixWord, tailWord_3307629, baseEnd_3307629] using wordTrace_append hprefix tailTrace_3307629
  have hstable : (prefixWord ++ tailWord_3307629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307629).length < 2 ^ (prefixWord ++ tailWord_3307629).sum := by decide
  have hdescent : baseEnd_3307629 < baseStart_3307629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307639 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_3307639 : Nat := 118140960795 + 3307639 * 2 ^ 59
def prefixEnd_3307639 : Nat := 4983230072969 + 3 ^ 40 * 3307639 * 2
def baseEnd_3307639 : Nat := 1698408638556889580900951

theorem tailTrace_3307639 : CollatzResearch.WordTrace tailWord_3307639 prefixEnd_3307639 1698408638556889580900951 := by
  unfold tailWord_3307639
  simp only [CollatzResearch.WordTrace]
  refine ⟨120639505263996277612341971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80426336842664185074894647 120639505263996277612341971)
  ·
    refine ⟨180959257895994416418512957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120639505263996277612341971 180959257895994416418512957)
    ·
      refine ⟨67859721710997906156942359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180959257895994416418512957 67859721710997906156942359)
      ·
        refine ⟨101789582566496859235413539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67859721710997906156942359 101789582566496859235413539)
        ·
          refine ⟨152684373849745288853120309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101789582566496859235413539 152684373849745288853120309)
          ·
            refine ⟨14314160048413620829980029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152684373849745288853120309 14314160048413620829980029)
            ·
              refine ⟨5367810018155107811242511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14314160048413620829980029 5367810018155107811242511)
              ·
                refine ⟨8051715027232661716863767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367810018155107811242511 8051715027232661716863767)
                ·
                  refine ⟨12077572540848992575295651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8051715027232661716863767 12077572540848992575295651)
                  ·
                    refine ⟨18116358811273488862943477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12077572540848992575295651 18116358811273488862943477)
                    ·
                      refine ⟨1698408638556889580900951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18116358811273488862943477 1698408638556889580900951)
                      ·
                        rfl

theorem cell23_3307639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_3307639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307639 prefixEnd_3307639 := by exact prefixLift 3307639
  have htrace : WordTrace (prefixWord ++ tailWord_3307639) baseStart_3307639 baseEnd_3307639 := by
    simpa [prefixWord, tailWord_3307639, baseEnd_3307639] using wordTrace_append hprefix tailTrace_3307639
  have hstable : (prefixWord ++ tailWord_3307639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307639).length < 2 ^ (prefixWord ++ tailWord_3307639).sum := by decide
  have hdescent : baseEnd_3307639 < baseStart_3307639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307656 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3307656 : Nat := 118140960795 + 3307656 * 2 ^ 59
def prefixEnd_3307656 : Nat := 4983230072969 + 3 ^ 40 * 3307656 * 2
def baseEnd_3307656 : Nat := 1698417367728016014388373

theorem tailTrace_3307656 : CollatzResearch.WordTrace tailWord_3307656 prefixEnd_3307656 1698417367728016014388373 := by
  unfold tailWord_3307656
  simp only [CollatzResearch.WordTrace]
  refine ⟨60320062652467344757855411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80426750203289793010473881 60320062652467344757855411)
  ·
    refine ⟨90480093978701017136783117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60320062652467344757855411 90480093978701017136783117)
    ·
      refine ⟨33930035242012881426293669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90480093978701017136783117 33930035242012881426293669)
      ·
        refine ⟨6361881607877415267430063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33930035242012881426293669 6361881607877415267430063)
        ·
          refine ⟨9542822411816122901145095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361881607877415267430063 9542822411816122901145095)
          ·
            refine ⟨14314233617724184351717643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542822411816122901145095 14314233617724184351717643)
            ·
              refine ⟨21471350426586276527576465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314233617724184351717643 21471350426586276527576465)
              ·
                refine ⟨16103512819939707395682349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21471350426586276527576465 16103512819939707395682349)
                ·
                  refine ⟨6038817307477390273380881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16103512819939707395682349 6038817307477390273380881)
                  ·
                    refine ⟨4529112980608042705035661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6038817307477390273380881 4529112980608042705035661)
                    ·
                      refine ⟨1698417367728016014388373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529112980608042705035661 1698417367728016014388373)
                      ·
                        rfl

theorem cell23_3307656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3307656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307656 prefixEnd_3307656 := by exact prefixLift 3307656
  have htrace : WordTrace (prefixWord ++ tailWord_3307656) baseStart_3307656 baseEnd_3307656 := by
    simpa [prefixWord, tailWord_3307656, baseEnd_3307656] using wordTrace_append hprefix tailTrace_3307656
  have hstable : (prefixWord ++ tailWord_3307656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307656).length < 2 ^ (prefixWord ++ tailWord_3307656).sum := by decide
  have hdescent : baseEnd_3307656 < baseStart_3307656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307666 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3307666 : Nat := 118140960795 + 3307666 * 2 ^ 59
def prefixEnd_3307666 : Nat := 4983230072969 + 3 ^ 40 * 3307666 * 2
def baseEnd_3307666 : Nat := 1698422502534560975263327

theorem tailTrace_3307666 : CollatzResearch.WordTrace tailWord_3307666 prefixEnd_3307666 1698422502534560975263327 := by
  unfold tailWord_3307666
  simp only [CollatzResearch.WordTrace]
  refine ⟨30160122508724615305893713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80426993356598974149049901 30160122508724615305893713)
  ·
    refine ⟨22620091881543461479420285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30160122508724615305893713 22620091881543461479420285)
    ·
      refine ⟨8482534455578798054782607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22620091881543461479420285 8482534455578798054782607)
      ·
        refine ⟨12723801683368197082173911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8482534455578798054782607 12723801683368197082173911)
        ·
          refine ⟨19085702525052295623260867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12723801683368197082173911 19085702525052295623260867)
          ·
            refine ⟨28628553787578443434891301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19085702525052295623260867 28628553787578443434891301)
            ·
              refine ⟨5367853835170958144042119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28628553787578443434891301 5367853835170958144042119)
              ·
                refine ⟨8051780752756437216063179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367853835170958144042119 8051780752756437216063179)
                ·
                  refine ⟨12077671129134655824094769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8051780752756437216063179 12077671129134655824094769)
                  ·
                    refine ⟨9058253346850991868071077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12077671129134655824094769 9058253346850991868071077)
                    ·
                      refine ⟨1698422502534560975263327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9058253346850991868071077 1698422502534560975263327)
                      ·
                        rfl

theorem cell23_3307666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3307666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307666 prefixEnd_3307666 := by exact prefixLift 3307666
  have htrace : WordTrace (prefixWord ++ tailWord_3307666) baseStart_3307666 baseEnd_3307666 := by
    simpa [prefixWord, tailWord_3307666, baseEnd_3307666] using wordTrace_append hprefix tailTrace_3307666
  have hstable : (prefixWord ++ tailWord_3307666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307666).length < 2 ^ (prefixWord ++ tailWord_3307666).sum := by decide
  have hdescent : baseEnd_3307666 < baseStart_3307666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307687 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_3307687 : Nat := 118140960795 + 3307687 * 2 ^ 59
def prefixEnd_3307687 : Nat := 4983230072969 + 3 ^ 40 * 3307687 * 2
def baseEnd_3307687 : Nat := 1698433285628305393100731

theorem tailTrace_3307687 : CollatzResearch.WordTrace tailWord_3307687 prefixEnd_3307687 1698433285628305393100731 := by
  unfold tailWord_3307687
  simp only [CollatzResearch.WordTrace]
  refine ⟨120641255967822381810089315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80427503978548254540059543 120641255967822381810089315)
  ·
    refine ⟨180961883951733572715133973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120641255967822381810089315 180961883951733572715133973)
    ·
      refine ⟨8482588310237511221021905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180961883951733572715133973 8482588310237511221021905)
      ·
        refine ⟨6361941232678133415766429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8482588310237511221021905 6361941232678133415766429)
        ·
          refine ⟨2385727962254300030912411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6361941232678133415766429 2385727962254300030912411)
          ·
            refine ⟨3578591943381450046368617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385727962254300030912411 3578591943381450046368617)
            ·
              refine ⟨2683943957536087534776463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3578591943381450046368617 2683943957536087534776463)
              ·
                refine ⟨4025915936304131302164695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683943957536087534776463 4025915936304131302164695)
                ·
                  refine ⟨6038873904456196953247043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025915936304131302164695 6038873904456196953247043)
                  ·
                    refine ⟨9058310856684295429870565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6038873904456196953247043 9058310856684295429870565)
                    ·
                      refine ⟨1698433285628305393100731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9058310856684295429870565 1698433285628305393100731)
                      ·
                        rfl

theorem cell23_3307687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_3307687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307687 prefixEnd_3307687 := by exact prefixLift 3307687
  have htrace : WordTrace (prefixWord ++ tailWord_3307687) baseStart_3307687 baseEnd_3307687 := by
    simpa [prefixWord, tailWord_3307687, baseEnd_3307687] using wordTrace_append hprefix tailTrace_3307687
  have hstable : (prefixWord ++ tailWord_3307687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307687).length < 2 ^ (prefixWord ++ tailWord_3307687).sum := by decide
  have hdescent : baseEnd_3307687 < baseStart_3307687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307690 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3307690 : Nat := 118140960795 + 3307690 * 2 ^ 59
def prefixEnd_3307690 : Nat := 4983230072969 + 3 ^ 40 * 3307690 * 2
def baseEnd_3307690 : Nat := 1698434826070268881363217

theorem tailTrace_3307690 : CollatzResearch.WordTrace tailWord_3307690 prefixEnd_3307690 1698434826070268881363217 := by
  unfold tailWord_3307690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30160341346702878330612131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80427576924541008881632349 30160341346702878330612131)
  ·
    refine ⟨45240512020054317495918197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30160341346702878330612131 45240512020054317495918197)
    ·
      refine ⟨4241298001880092265242331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45240512020054317495918197 4241298001880092265242331)
      ·
        refine ⟨6361947002820138397863497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241298001880092265242331 6361947002820138397863497)
        ·
          refine ⟨4771460252115103798397623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6361947002820138397863497 4771460252115103798397623)
          ·
            refine ⟨7157190378172655697596435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771460252115103798397623 7157190378172655697596435)
            ·
              refine ⟨10735785567258983546394653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157190378172655697596435 10735785567258983546394653)
              ·
                refine ⟨4025919587722118829897995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10735785567258983546394653 4025919587722118829897995)
                ·
                  refine ⟨6038879381583178244846993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025919587722118829897995 6038879381583178244846993)
                  ·
                    refine ⟨4529159536187383683635245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6038879381583178244846993 4529159536187383683635245)
                    ·
                      refine ⟨1698434826070268881363217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529159536187383683635245 1698434826070268881363217)
                      ·
                        rfl

theorem cell23_3307690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3307690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307690 prefixEnd_3307690 := by exact prefixLift 3307690
  have htrace : WordTrace (prefixWord ++ tailWord_3307690) baseStart_3307690 baseEnd_3307690 := by
    simpa [prefixWord, tailWord_3307690, baseEnd_3307690] using wordTrace_append hprefix tailTrace_3307690
  have hstable : (prefixWord ++ tailWord_3307690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307690).length < 2 ^ (prefixWord ++ tailWord_3307690).sum := by decide
  have hdescent : baseEnd_3307690 < baseStart_3307690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307703 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_3307703 : Nat := 118140960795 + 3307703 * 2 ^ 59
def prefixEnd_3307703 : Nat := 4983230072969 + 3 ^ 40 * 3307703 * 2
def baseEnd_3307703 : Nat := 1698441501318777330500657

theorem tailTrace_3307703 : CollatzResearch.WordTrace tailWord_3307703 prefixEnd_3307703 1698441501318777330500657 := by
  unfold tailWord_3307703
  simp only [CollatzResearch.WordTrace]
  refine ⟨120641839535764416542671763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80427893023842944361781175 120641839535764416542671763)
  ·
    refine ⟨180962759303646624814007645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120641839535764416542671763 180962759303646624814007645)
    ·
      refine ⟨67861034738867484305252867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180962759303646624814007645 67861034738867484305252867)
      ·
        refine ⟨101791552108301226457879301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67861034738867484305252867 101791552108301226457879301)
        ·
          refine ⟨19085916020306479960852369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101791552108301226457879301 19085916020306479960852369)
          ·
            refine ⟨14314437015229859970639277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19085916020306479960852369 14314437015229859970639277)
            ·
              refine ⟨5367913880711197488989729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14314437015229859970639277 5367913880711197488989729)
              ·
                refine ⟨4025935410533398116742297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367913880711197488989729 4025935410533398116742297)
                ·
                  refine ⟨3019451557900048587556723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4025935410533398116742297 3019451557900048587556723)
                  ·
                    refine ⟨4529177336850072881335085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3019451557900048587556723 4529177336850072881335085)
                    ·
                      refine ⟨1698441501318777330500657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529177336850072881335085 1698441501318777330500657)
                      ·
                        rfl

theorem cell23_3307703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_3307703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307703 prefixEnd_3307703 := by exact prefixLift 3307703
  have htrace : WordTrace (prefixWord ++ tailWord_3307703) baseStart_3307703 baseEnd_3307703 := by
    simpa [prefixWord, tailWord_3307703, baseEnd_3307703] using wordTrace_append hprefix tailTrace_3307703
  have hstable : (prefixWord ++ tailWord_3307703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307703).length < 2 ^ (prefixWord ++ tailWord_3307703).sum := by decide
  have hdescent : baseEnd_3307703 < baseStart_3307703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307729 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_3307729 : Nat := 118140960795 + 3307729 * 2 ^ 59
def prefixEnd_3307729 : Nat := 4983230072969 + 3 ^ 40 * 3307729 * 2
def baseEnd_3307729 : Nat := 1698454851815794228775537

theorem tailTrace_3307729 : CollatzResearch.WordTrace tailWord_3307729 prefixEnd_3307729 1698454851815794228775537 := by
  unfold tailWord_3307729
  simp only [CollatzResearch.WordTrace]
  refine ⟨120642787833670222983118241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80428525222446815322078827 120642787833670222983118241)
  ·
    refine ⟨90482090875252667237338681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120642787833670222983118241 90482090875252667237338681)
    ·
      refine ⟨67861568156439500428004011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90482090875252667237338681 67861568156439500428004011)
      ·
        refine ⟨101792352234659250642006017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67861568156439500428004011 101792352234659250642006017)
        ·
          refine ⟨76344264175994437981504513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101792352234659250642006017 76344264175994437981504513)
          ·
            refine ⟨57258198131995828486128385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76344264175994437981504513 57258198131995828486128385)
            ·
              refine ⟨42943648598996871364596289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57258198131995828486128385 42943648598996871364596289)
              ·
                refine ⟨32207736449247653523447217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42943648598996871364596289 32207736449247653523447217)
                ·
                  refine ⟨24155802336935740142585413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32207736449247653523447217 24155802336935740142585413)
                  ·
                    refine ⟨4529212938175451276734765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24155802336935740142585413 4529212938175451276734765)
                    ·
                      refine ⟨1698454851815794228775537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529212938175451276734765 1698454851815794228775537)
                      ·
                        rfl

theorem cell23_3307729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_3307729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307729 prefixEnd_3307729 := by exact prefixLift 3307729
  have htrace : WordTrace (prefixWord ++ tailWord_3307729) baseStart_3307729 baseEnd_3307729 := by
    simpa [prefixWord, tailWord_3307729, baseEnd_3307729] using wordTrace_append hprefix tailTrace_3307729
  have hstable : (prefixWord ++ tailWord_3307729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307729).length < 2 ^ (prefixWord ++ tailWord_3307729).sum := by decide
  have hdescent : baseEnd_3307729 < baseStart_3307729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307730 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_3307730 : Nat := 118140960795 + 3307730 * 2 ^ 59
def prefixEnd_3307730 : Nat := 4983230072969 + 3 ^ 40 * 3307730 * 2
def baseEnd_3307730 : Nat := 1698455365296448724863033

theorem tailTrace_3307730 : CollatzResearch.WordTrace tailWord_3307730 prefixEnd_3307730 1698455365296448724863033 := by
  unfold tailWord_3307730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30160706076666650038476161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80428549537777733435936429 30160706076666650038476161)
  ·
    refine ⟨22620529557499987528857121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30160706076666650038476161 22620529557499987528857121)
    ·
      refine ⟨16965397168124990646642841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22620529557499987528857121 16965397168124990646642841)
      ·
        refine ⟨12724047876093742984982131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16965397168124990646642841 12724047876093742984982131)
        ·
          refine ⟨19086071814140614477473197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12724047876093742984982131 19086071814140614477473197)
          ·
            refine ⟨7157276930302730429052449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19086071814140614477473197 7157276930302730429052449)
            ·
              refine ⟨5367957697727047821789337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7157276930302730429052449 5367957697727047821789337)
              ·
                refine ⟨4025968273295285866342003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367957697727047821789337 4025968273295285866342003)
                ·
                  refine ⟨6038952409942928799513005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025968273295285866342003 6038952409942928799513005)
                  ·
                    refine ⟨2264607153728598299817377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6038952409942928799513005 2264607153728598299817377)
                    ·
                      refine ⟨1698455365296448724863033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264607153728598299817377 1698455365296448724863033)
                      ·
                        rfl

theorem cell23_3307730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_3307730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307730 prefixEnd_3307730 := by exact prefixLift 3307730
  have htrace : WordTrace (prefixWord ++ tailWord_3307730) baseStart_3307730 baseEnd_3307730 := by
    simpa [prefixWord, tailWord_3307730, baseEnd_3307730] using wordTrace_append hprefix tailTrace_3307730
  have hstable : (prefixWord ++ tailWord_3307730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307730).length < 2 ^ (prefixWord ++ tailWord_3307730).sum := by decide
  have hdescent : baseEnd_3307730 < baseStart_3307730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307766 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_3307766 : Nat := 118140960795 + 3307766 * 2 ^ 59
def prefixEnd_3307766 : Nat := 4983230072969 + 3 ^ 40 * 3307766 * 2
def baseEnd_3307766 : Nat := 188719316733334509334763

theorem tailTrace_3307766 : CollatzResearch.WordTrace tailWord_3307766 prefixEnd_3307766 188719316733334509334763 := by
  unfold tailWord_3307766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540258583408511143888447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80429424889690785534810101 7540258583408511143888447)
  ·
    refine ⟨11310387875112766715832671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7540258583408511143888447 11310387875112766715832671)
    ·
      refine ⟨16965581812669150073749007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11310387875112766715832671 16965581812669150073749007)
      ·
        refine ⟨25448372719003725110623511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16965581812669150073749007 25448372719003725110623511)
        ·
          refine ⟨38172559078505587665935267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25448372719003725110623511 38172559078505587665935267)
          ·
            refine ⟨57258838617758381498902901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38172559078505587665935267 57258838617758381498902901)
            ·
              refine ⟨5368016120414848265522147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57258838617758381498902901 5368016120414848265522147)
              ·
                refine ⟨8052024180622272398283221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368016120414848265522147 8052024180622272398283221)
                ·
                  refine ⟨188719316733334509334763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8052024180622272398283221 188719316733334509334763)
                  ·
                    rfl

theorem cell23_3307766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_3307766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307766 prefixEnd_3307766 := by exact prefixLift 3307766
  have htrace : WordTrace (prefixWord ++ tailWord_3307766) baseStart_3307766 baseEnd_3307766 := by
    simpa [prefixWord, tailWord_3307766, baseEnd_3307766] using wordTrace_append hprefix tailTrace_3307766
  have hstable : (prefixWord ++ tailWord_3307766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307766).length < 2 ^ (prefixWord ++ tailWord_3307766).sum := by decide
  have hdescent : baseEnd_3307766 < baseStart_3307766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307779 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 4, 5]
def baseStart_3307779 : Nat := 118140960795 + 3307779 * 2 ^ 59
def prefixEnd_3307779 : Nat := 4983230072969 + 3 ^ 40 * 3307779 * 2
def baseEnd_3307779 : Nat := 566160175282839677716769

theorem tailTrace_3307779 : CollatzResearch.WordTrace tailWord_3307779 prefixEnd_3307779 566160175282839677716769 := by
  unfold tailWord_3307779
  simp only [CollatzResearch.WordTrace]
  refine ⟨120644611483489081522438391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80429740988992721014958927 120644611483489081522438391)
  ·
    refine ⟨180966917225233622283657587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120644611483489081522438391 180966917225233622283657587)
    ·
      refine ⟨271450375837850433425486381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180966917225233622283657587 271450375837850433425486381)
      ·
        refine ⟨101793890939193912534557393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271450375837850433425486381 101793890939193912534557393)
        ·
          refine ⟨76345418204395434400918045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101793890939193912534557393 76345418204395434400918045)
          ·
            refine ⟨28629531826648287900344267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76345418204395434400918045 28629531826648287900344267)
            ·
              refine ⟨42944297739972431850516401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28629531826648287900344267 42944297739972431850516401)
              ·
                refine ⟨32208223304979323887887301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42944297739972431850516401 32208223304979323887887301)
                ·
                  refine ⟨6039041869683623228978869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32208223304979323887887301 6039041869683623228978869)
                  ·
                    refine ⟨566160175282839677716769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6039041869683623228978869 566160175282839677716769)
                    ·
                      rfl

theorem cell23_3307779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 5].length) (baseStart_3307779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307779 prefixEnd_3307779 := by exact prefixLift 3307779
  have htrace : WordTrace (prefixWord ++ tailWord_3307779) baseStart_3307779 baseEnd_3307779 := by
    simpa [prefixWord, tailWord_3307779, baseEnd_3307779] using wordTrace_append hprefix tailTrace_3307779
  have hstable : (prefixWord ++ tailWord_3307779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307779).length < 2 ^ (prefixWord ++ tailWord_3307779).sum := by decide
  have hdescent : baseEnd_3307779 < baseStart_3307779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307833 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3307833 : Nat := 118140960795 + 3307833 * 2 ^ 59
def prefixEnd_3307833 : Nat := 4983230072969 + 3 ^ 40 * 3307833 * 2
def baseEnd_3307833 : Nat := 1698508253803861821875059

theorem tailTrace_3307833 : CollatzResearch.WordTrace tailWord_3307833 prefixEnd_3307833 1698508253803861821875059 := by
  unfold tailWord_3307833
  simp only [CollatzResearch.WordTrace]
  refine ⟨120646581025293448744904153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80431054016862299163269435 120646581025293448744904153)
  ·
    refine ⟨90484935768970086558678115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120646581025293448744904153 90484935768970086558678115)
    ·
      refine ⟨135727403653455129838017173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90484935768970086558678115 135727403653455129838017173)
      ·
        refine ⟨6362222046255709211157055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135727403653455129838017173 6362222046255709211157055)
        ·
          refine ⟨9543333069383563816735583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6362222046255709211157055 9543333069383563816735583)
          ·
            refine ⟨14314999604075345725103375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9543333069383563816735583 14314999604075345725103375)
            ·
              refine ⟨21472499406113018587655063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314999604075345725103375 21472499406113018587655063)
              ·
                refine ⟨32208749109169527881482595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21472499406113018587655063 32208749109169527881482595)
                ·
                  refine ⟨48313123663754291822223893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32208749109169527881482595 48313123663754291822223893)
                  ·
                    refine ⟨2264677671738482429166745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48313123663754291822223893 2264677671738482429166745)
                    ·
                      refine ⟨1698508253803861821875059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264677671738482429166745 1698508253803861821875059)
                      ·
                        rfl

theorem cell23_3307833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3307833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307833 prefixEnd_3307833 := by exact prefixLift 3307833
  have htrace : WordTrace (prefixWord ++ tailWord_3307833) baseStart_3307833 baseEnd_3307833 := by
    simpa [prefixWord, tailWord_3307833, baseEnd_3307833] using wordTrace_append hprefix tailTrace_3307833
  have hstable : (prefixWord ++ tailWord_3307833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307833).length < 2 ^ (prefixWord ++ tailWord_3307833).sum := by decide
  have hdescent : baseEnd_3307833 < baseStart_3307833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307836 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3307836 : Nat := 118140960795 + 3307836 * 2 ^ 59
def prefixEnd_3307836 : Nat := 4983230072969 + 3 ^ 40 * 3307836 * 2
def baseEnd_3307836 : Nat := 1698509794245825310137545

theorem tailTrace_3307836 : CollatzResearch.WordTrace tailWord_3307836 prefixEnd_3307836 1698509794245825310137545 := by
  unfold tailWord_3307836
  simp only [CollatzResearch.WordTrace]
  refine ⟨60323345222141290128631681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80431126962855053504842241 60323345222141290128631681)
  ·
    refine ⟨45242508916605967596473761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60323345222141290128631681 45242508916605967596473761)
    ·
      refine ⟨33931881687454475697355321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45242508916605967596473761 33931881687454475697355321)
      ·
        refine ⟨25448911265590856773016491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33931881687454475697355321 25448911265590856773016491)
        ·
          refine ⟨38173366898386285159524737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25448911265590856773016491 38173366898386285159524737)
          ·
            refine ⟨28630025173789713869643553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38173366898386285159524737 28630025173789713869643553)
            ·
              refine ⟨21472518880342285402232665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28630025173789713869643553 21472518880342285402232665)
              ·
                refine ⟨16104389160256714051674499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21472518880342285402232665 16104389160256714051674499)
                ·
                  refine ⟨24156583740385071077511749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16104389160256714051674499 24156583740385071077511749)
                  ·
                    refine ⟨4529359451322200827033453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24156583740385071077511749 4529359451322200827033453)
                    ·
                      refine ⟨1698509794245825310137545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529359451322200827033453 1698509794245825310137545)
                      ·
                        rfl

theorem cell23_3307836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3307836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307836 prefixEnd_3307836 := by exact prefixLift 3307836
  have htrace : WordTrace (prefixWord ++ tailWord_3307836) baseStart_3307836 baseEnd_3307836 := by
    simpa [prefixWord, tailWord_3307836, baseEnd_3307836] using wordTrace_append hprefix tailTrace_3307836
  have hstable : (prefixWord ++ tailWord_3307836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307836).length < 2 ^ (prefixWord ++ tailWord_3307836).sum := by decide
  have hdescent : baseEnd_3307836 < baseStart_3307836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307860 : List Nat := [2, 4, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_3307860 : Nat := 118140960795 + 3307860 * 2 ^ 59
def prefixEnd_3307860 : Nat := 4983230072969 + 3 ^ 40 * 3307860 * 2
def baseEnd_3307860 : Nat := 566174039260511072079145

theorem tailTrace_3307860 : CollatzResearch.WordTrace tailWord_3307860 prefixEnd_3307860 566174039260511072079145 := by
  unfold tailWord_3307860
  simp only [CollatzResearch.WordTrace]
  refine ⟨60323782898097816178068517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80431710530797088237424689 60323782898097816178068517)
  ·
    refine ⟨11310709293393340533387847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60323782898097816178068517 11310709293393340533387847)
    ·
      refine ⟨16966063940090010800081771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11310709293393340533387847 16966063940090010800081771)
      ·
        refine ⟨25449095910135016200122657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16966063940090010800081771 25449095910135016200122657)
        ·
          refine ⟨19086821932601262150091993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25449095910135016200122657 19086821932601262150091993)
          ·
            refine ⟨14315116449450946612568995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19086821932601262150091993 14315116449450946612568995)
            ·
              refine ⟨21472674674176419918853493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14315116449450946612568995 21472674674176419918853493)
              ·
                refine ⟨2013063250704039367392515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21472674674176419918853493 2013063250704039367392515)
                ·
                  refine ⟨3019594876056059051088773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013063250704039367392515 3019594876056059051088773)
                  ·
                    refine ⟨566174039260511072079145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019594876056059051088773 566174039260511072079145)
                    ·
                      rfl

theorem cell23_3307860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_3307860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307860 prefixEnd_3307860 := by exact prefixLift 3307860
  have htrace : WordTrace (prefixWord ++ tailWord_3307860) baseStart_3307860 baseEnd_3307860 := by
    simpa [prefixWord, tailWord_3307860, baseEnd_3307860] using wordTrace_append hprefix tailTrace_3307860
  have hstable : (prefixWord ++ tailWord_3307860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307860).length < 2 ^ (prefixWord ++ tailWord_3307860).sum := by decide
  have hdescent : baseEnd_3307860 < baseStart_3307860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307934 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3307934 : Nat := 118140960795 + 3307934 * 2 ^ 59
def prefixEnd_3307934 : Nat := 4983230072969 + 3 ^ 40 * 3307934 * 2
def baseEnd_3307934 : Nat := 1698560115349965926712095

theorem tailTrace_3307934 : CollatzResearch.WordTrace tailWord_3307934 prefixEnd_3307934 1698560115349965926712095 := by
  unfold tailWord_3307934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15081283099740942874291357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80433509865285028662887237 15081283099740942874291357)
  ·
    refine ⟨5655481162402853577859259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15081283099740942874291357 5655481162402853577859259)
    ·
      refine ⟨8483221743604280366788889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5655481162402853577859259 8483221743604280366788889)
      ·
        refine ⟨6362416307703210275091667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8483221743604280366788889 6362416307703210275091667)
        ·
          refine ⟨9543624461554815412637501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6362416307703210275091667 9543624461554815412637501)
          ·
            refine ⟨3578859173083055779739063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9543624461554815412637501 3578859173083055779739063)
            ·
              refine ⟨5368288759624583669608595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578859173083055779739063 5368288759624583669608595)
              ·
                refine ⟨8052433139436875504412893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368288759624583669608595 8052433139436875504412893)
                ·
                  refine ⟨3019662427288828314154835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8052433139436875504412893 3019662427288828314154835)
                  ·
                    refine ⟨4529493640933242471232253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3019662427288828314154835 4529493640933242471232253)
                    ·
                      refine ⟨1698560115349965926712095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529493640933242471232253 1698560115349965926712095)
                      ·
                        rfl

theorem cell23_3307934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3307934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307934 prefixEnd_3307934 := by exact prefixLift 3307934
  have htrace : WordTrace (prefixWord ++ tailWord_3307934) baseStart_3307934 baseEnd_3307934 := by
    simpa [prefixWord, tailWord_3307934, baseEnd_3307934] using wordTrace_append hprefix tailTrace_3307934
  have hstable : (prefixWord ++ tailWord_3307934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307934).length < 2 ^ (prefixWord ++ tailWord_3307934).sum := by decide
  have hdescent : baseEnd_3307934 < baseStart_3307934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307936 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3307936 : Nat := 118140960795 + 3307936 * 2 ^ 59
def prefixEnd_3307936 : Nat := 4983230072969 + 3 ^ 40 * 3307936 * 2
def baseEnd_3307936 : Nat := 1698561142311274918887085

theorem tailTrace_3307936 : CollatzResearch.WordTrace tailWord_3307936 prefixEnd_3307936 1698561142311274918887085 := by
  unfold tailWord_3307936
  simp only [CollatzResearch.WordTrace]
  refine ⟨60325168871960148667951831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80433558495946864890602441 60325168871960148667951831)
  ·
    refine ⟨90487753307940223001927747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60325168871960148667951831 90487753307940223001927747)
    ·
      refine ⟨135731629961910334502891621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90487753307940223001927747 135731629961910334502891621)
      ·
        refine ⟨25449680617858187719292179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135731629961910334502891621 25449680617858187719292179)
        ·
          refine ⟨38174520926787281578938269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25449680617858187719292179 38174520926787281578938269)
          ·
            refine ⟨14315445347545230592101851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38174520926787281578938269 14315445347545230592101851)
            ·
              refine ⟨21473168021317845888152777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14315445347545230592101851 21473168021317845888152777)
              ·
                refine ⟨16104876015988384416114583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21473168021317845888152777 16104876015988384416114583)
                ·
                  refine ⟨24157314023982576624171875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16104876015988384416114583 24157314023982576624171875)
                  ·
                    refine ⟨36235971035973864936257813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24157314023982576624171875 36235971035973864936257813)
                    ·
                      refine ⟨1698561142311274918887085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36235971035973864936257813 1698561142311274918887085)
                      ·
                        rfl

theorem cell23_3307936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3307936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307936 prefixEnd_3307936 := by exact prefixLift 3307936
  have htrace : WordTrace (prefixWord ++ tailWord_3307936) baseStart_3307936 baseEnd_3307936 := by
    simpa [prefixWord, tailWord_3307936, baseEnd_3307936] using wordTrace_append hprefix tailTrace_3307936
  have hstable : (prefixWord ++ tailWord_3307936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307936).length < 2 ^ (prefixWord ++ tailWord_3307936).sum := by decide
  have hdescent : baseEnd_3307936 < baseStart_3307936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307943 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3307943 : Nat := 118140960795 + 3307943 * 2 ^ 59
def prefixEnd_3307943 : Nat := 4983230072969 + 3 ^ 40 * 3307943 * 2
def baseEnd_3307943 : Nat := 1698564736675856391499553

theorem tailTrace_3307943 : CollatzResearch.WordTrace tailWord_3307943 prefixEnd_3307943 1698564736675856391499553 := by
  unfold tailWord_3307943
  simp only [CollatzResearch.WordTrace]
  refine ⟨120650593054894937531408483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80433728703263291687605655 120650593054894937531408483)
  ·
    refine ⟨180975889582342406297112725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120650593054894937531408483 180975889582342406297112725)
    ·
      refine ⟨8483244824172300295177159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180975889582342406297112725 8483244824172300295177159)
      ·
        refine ⟨12724867236258450442765739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8483244824172300295177159 12724867236258450442765739)
        ·
          refine ⟨19087300854387675664148609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12724867236258450442765739 19087300854387675664148609)
          ·
            refine ⟨14315475640790756748111457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19087300854387675664148609 14315475640790756748111457)
            ·
              refine ⟨10736606730593067561083593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14315475640790756748111457 10736606730593067561083593)
              ·
                refine ⟨8052455047944800670812695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10736606730593067561083593 8052455047944800670812695)
                ·
                  refine ⟨12078682571917201006219043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052455047944800670812695 12078682571917201006219043)
                  ·
                    refine ⟨18118023857875801509328565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12078682571917201006219043 18118023857875801509328565)
                    ·
                      refine ⟨1698564736675856391499553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18118023857875801509328565 1698564736675856391499553)
                      ·
                        rfl

theorem cell23_3307943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3307943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307943 prefixEnd_3307943 := by exact prefixLift 3307943
  have htrace : WordTrace (prefixWord ++ tailWord_3307943) baseStart_3307943 baseEnd_3307943 := by
    simpa [prefixWord, tailWord_3307943, baseEnd_3307943] using wordTrace_append hprefix tailTrace_3307943
  have hstable : (prefixWord ++ tailWord_3307943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307943).length < 2 ^ (prefixWord ++ tailWord_3307943).sum := by decide
  have hdescent : baseEnd_3307943 < baseStart_3307943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307957 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3307957 : Nat := 118140960795 + 3307957 * 2 ^ 59
def prefixEnd_3307957 : Nat := 4983230072969 + 3 ^ 40 * 3307957 * 2
def baseEnd_3307957 : Nat := 1698571925405019336724489

theorem tailTrace_3307957 : CollatzResearch.WordTrace tailWord_3307957 prefixEnd_3307957 1698571925405019336724489 := by
  unfold tailWord_3307957
  simp only [CollatzResearch.WordTrace]
  refine ⟨120651103676844217922418125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80434069117896145281612083 120651103676844217922418125)
  ·
    refine ⟨45244163878816581720906797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120651103676844217922418125 45244163878816581720906797)
    ·
      refine ⟨16966561454556218145340049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45244163878816581720906797 16966561454556218145340049)
      ·
        refine ⟨12724921090917163609005037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16966561454556218145340049 12724921090917163609005037)
        ·
          refine ⟨4771845409093936353376889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12724921090917163609005037 4771845409093936353376889)
          ·
            refine ⟨3578884056820452265032667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771845409093936353376889 3578884056820452265032667)
            ·
              refine ⟨5368326085230678397549001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578884056820452265032667 5368326085230678397549001)
              ·
                refine ⟨4026244563923008798161751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5368326085230678397549001 4026244563923008798161751)
                ·
                  refine ⟨6039366845884513197242627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026244563923008798161751 6039366845884513197242627)
                  ·
                    refine ⟨9059050268826769795863941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039366845884513197242627 9059050268826769795863941)
                    ·
                      refine ⟨1698571925405019336724489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9059050268826769795863941 1698571925405019336724489)
                      ·
                        rfl

theorem cell23_3307957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3307957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307957 prefixEnd_3307957 := by exact prefixLift 3307957
  have htrace : WordTrace (prefixWord ++ tailWord_3307957) baseStart_3307957 baseEnd_3307957 := by
    simpa [prefixWord, tailWord_3307957, baseEnd_3307957] using wordTrace_append hprefix tailTrace_3307957
  have hstable : (prefixWord ++ tailWord_3307957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307957).length < 2 ^ (prefixWord ++ tailWord_3307957).sum := by decide
  have hdescent : baseEnd_3307957 < baseStart_3307957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3307990 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3307990 : Nat := 118140960795 + 3307990 * 2 ^ 59
def prefixEnd_3307990 : Nat := 4983230072969 + 3 ^ 40 * 3307990 * 2
def baseEnd_3307990 : Nat := 1698588870266617707611837

theorem tailTrace_3307990 : CollatzResearch.WordTrace tailWord_3307990 prefixEnd_3307990 1698588870266617707611837 := by
  unfold tailWord_3307990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540769205357791534898089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80434871523816443038912949 7540769205357791534898089)
  ·
    refine ⟨5655576904018343651173567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7540769205357791534898089 5655576904018343651173567)
    ·
      refine ⟨8483365356027515476760351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5655576904018343651173567 8483365356027515476760351)
      ·
        refine ⟨12725048034041273215140527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8483365356027515476760351 12725048034041273215140527)
        ·
          refine ⟨19087572051061909822710791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12725048034041273215140527 19087572051061909822710791)
          ·
            refine ⟨28631358076592864734066187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19087572051061909822710791 28631358076592864734066187)
            ·
              refine ⟨42947037114889297101099281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28631358076592864734066187 42947037114889297101099281)
              ·
                refine ⟨32210277836166972825824461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42947037114889297101099281 32210277836166972825824461)
                ·
                  refine ⟨12078854188562614809684173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32210277836166972825824461 12078854188562614809684173)
                  ·
                    refine ⟨4529570320710980553631565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12078854188562614809684173 4529570320710980553631565)
                    ·
                      refine ⟨1698588870266617707611837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529570320710980553631565 1698588870266617707611837)
                      ·
                        rfl

theorem cell23_3307990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3307990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3307990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3307990 prefixEnd_3307990 := by exact prefixLift 3307990
  have htrace : WordTrace (prefixWord ++ tailWord_3307990) baseStart_3307990 baseEnd_3307990 := by
    simpa [prefixWord, tailWord_3307990, baseEnd_3307990] using wordTrace_append hprefix tailTrace_3307990
  have hstable : (prefixWord ++ tailWord_3307990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3307990).length < 2 ^ (prefixWord ++ tailWord_3307990).sum := by decide
  have hdescent : baseEnd_3307990 < baseStart_3307990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3307990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308043 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4]
def baseStart_3308043 : Nat := 118140960795 + 3308043 * 2 ^ 59
def prefixEnd_3308043 : Nat := 4983230072969 + 3 ^ 40 * 3308043 * 2
def baseEnd_3308043 : Nat := 1698616084741306000249093

theorem tailTrace_3308043 : CollatzResearch.WordTrace tailWord_3308043 prefixEnd_3308043 1698616084741306000249093 := by
  unfold tailWord_3308043
  simp only [CollatzResearch.WordTrace]
  refine ⟨120654240354532654610048783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80436160236355103073365855 120654240354532654610048783)
  ·
    refine ⟨180981360531798981915073175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120654240354532654610048783 180981360531798981915073175)
    ·
      refine ⟨271472040797698472872609763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180981360531798981915073175 271472040797698472872609763)
      ·
        refine ⟨407208061196547709308914645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271472040797698472872609763 407208061196547709308914645)
        ·
          refine ⟨9543938934294086936927687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 407208061196547709308914645 9543938934294086936927687)
          ·
            refine ⟨14315908401441130405391531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9543938934294086936927687 14315908401441130405391531)
            ·
              refine ⟨21473862602161695608087297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14315908401441130405391531 21473862602161695608087297)
              ·
                refine ⟨16105396951621271706065473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21473862602161695608087297 16105396951621271706065473)
                ·
                  refine ⟨12079047713715953779549105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16105396951621271706065473 12079047713715953779549105)
                  ·
                    refine ⟨9059285785286965334661829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12079047713715953779549105 9059285785286965334661829)
                    ·
                      refine ⟨1698616084741306000249093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9059285785286965334661829 1698616084741306000249093)
                      ·
                        rfl

theorem cell23_3308043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_3308043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308043 prefixEnd_3308043 := by exact prefixLift 3308043
  have htrace : WordTrace (prefixWord ++ tailWord_3308043) baseStart_3308043 baseEnd_3308043 := by
    simpa [prefixWord, tailWord_3308043, baseEnd_3308043] using wordTrace_append hprefix tailTrace_3308043
  have hstable : (prefixWord ++ tailWord_3308043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308043).length < 2 ^ (prefixWord ++ tailWord_3308043).sum := by decide
  have hdescent : baseEnd_3308043 < baseStart_3308043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308053 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 7]
def baseStart_3308053 : Nat := 118140960795 + 3308053 * 2 ^ 59
def prefixEnd_3308053 : Nat := 4983230072969 + 3 ^ 40 * 3308053 * 2
def baseEnd_3308053 : Nat := 188735691060872329013783

theorem tailTrace_3308053 : CollatzResearch.WordTrace tailWord_3308053 prefixEnd_3308053 188735691060872329013783 := by
  unfold tailWord_3308053
  simp only [CollatzResearch.WordTrace]
  refine ⟨120654605084496426317912813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80436403389664284211941875 120654605084496426317912813)
  ·
    refine ⟨45245476906686159869217305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120654605084496426317912813 45245476906686159869217305)
    ·
      refine ⟨33934107680014619901912979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45245476906686159869217305 33934107680014619901912979)
      ·
        refine ⟨50901161520021929852869469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33934107680014619901912979 50901161520021929852869469)
        ·
          refine ⟨19087935570008223694826051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50901161520021929852869469 19087935570008223694826051)
          ·
            refine ⟨28631903355012335542239077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19087935570008223694826051 28631903355012335542239077)
            ·
              refine ⟨5368481879064812914169827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28631903355012335542239077 5368481879064812914169827)
              ·
                refine ⟨8052722818597219371254741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368481879064812914169827 8052722818597219371254741)
                ·
                  refine ⟨188735691060872329013783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8052722818597219371254741 188735691060872329013783)
                  ·
                    rfl

theorem cell23_3308053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_3308053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308053 prefixEnd_3308053 := by exact prefixLift 3308053
  have htrace : WordTrace (prefixWord ++ tailWord_3308053) baseStart_3308053 baseEnd_3308053 := by
    simpa [prefixWord, tailWord_3308053, baseEnd_3308053] using wordTrace_append hprefix tailTrace_3308053
  have hstable : (prefixWord ++ tailWord_3308053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308053).length < 2 ^ (prefixWord ++ tailWord_3308053).sum := by decide
  have hdescent : baseEnd_3308053 < baseStart_3308053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308064 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3308064 : Nat := 118140960795 + 3308064 * 2 ^ 59
def prefixEnd_3308064 : Nat := 4983230072969 + 3 ^ 40 * 3308064 * 2
def baseEnd_3308064 : Nat := 1698626867835050418086497

theorem tailTrace_3308064 : CollatzResearch.WordTrace tailWord_3308064 prefixEnd_3308064 1698626867835050418086497 := by
  unfold tailWord_3308064
  simp only [CollatzResearch.WordTrace]
  refine ⟨60327503143728287598281623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80436670858304383464375497 60327503143728287598281623)
  ·
    refine ⟨90491254715592431397422435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60327503143728287598281623 90491254715592431397422435)
    ·
      refine ⟨135736882073388647096133653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90491254715592431397422435 135736882073388647096133653)
      ·
        refine ⟨6362666347190092832631265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135736882073388647096133653 6362666347190092832631265)
        ·
          refine ⟨4771999760392569624473449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6362666347190092832631265 4771999760392569624473449)
          ·
            refine ⟨3578999820294427218355087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771999760392569624473449 3578999820294427218355087)
            ·
              refine ⟨5368499730441640827532631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578999820294427218355087 5368499730441640827532631)
              ·
                refine ⟨8052749595662461241298947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368499730441640827532631 8052749595662461241298947)
                ·
                  refine ⟨12079124393493691861948421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052749595662461241298947 12079124393493691861948421)
                  ·
                    refine ⟨2264835823780067224115329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12079124393493691861948421 2264835823780067224115329)
                    ·
                      refine ⟨1698626867835050418086497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264835823780067224115329 1698626867835050418086497)
                      ·
                        rfl

theorem cell23_3308064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3308064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308064 prefixEnd_3308064 := by exact prefixLift 3308064
  have htrace : WordTrace (prefixWord ++ tailWord_3308064) baseStart_3308064 baseEnd_3308064 := by
    simpa [prefixWord, tailWord_3308064, baseEnd_3308064] using wordTrace_append hprefix tailTrace_3308064
  have hstable : (prefixWord ++ tailWord_3308064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308064).length < 2 ^ (prefixWord ++ tailWord_3308064).sum := by decide
  have hdescent : baseEnd_3308064 < baseStart_3308064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308083 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 2, 5]
def baseStart_3308083 : Nat := 118140960795 + 3308083 * 2 ^ 59
def prefixEnd_3308083 : Nat := 4983230072969 + 3 ^ 40 * 3308083 * 2
def baseEnd_3308083 : Nat := 566212207989161947916303

theorem tailTrace_3308083 : CollatzResearch.WordTrace tailWord_3308083 prefixEnd_3308083 566212207989161947916303 := by
  unfold tailWord_3308083
  simp only [CollatzResearch.WordTrace]
  refine ⟨120655699274387741441504903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80437132849591827627669935 120655699274387741441504903)
  ·
    refine ⟨180983548911581612162257355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120655699274387741441504903 180983548911581612162257355)
    ·
      refine ⟨271475323367372418243386033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180983548911581612162257355 271475323367372418243386033)
      ·
        refine ⟨203606492525529313682539525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271475323367372418243386033 203606492525529313682539525)
        ·
          refine ⟨38176217348536746315476161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203606492525529313682539525 38176217348536746315476161)
          ·
            refine ⟨28632163011402559736607121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38176217348536746315476161 28632163011402559736607121)
            ·
              refine ⟨21474122258551919802455341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28632163011402559736607121 21474122258551919802455341)
              ·
                refine ⟨8052795846956969925920753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21474122258551919802455341 8052795846956969925920753)
                ·
                  refine ⟨6039596885217727444440565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8052795846956969925920753 6039596885217727444440565)
                  ·
                    refine ⟨566212207989161947916303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6039596885217727444440565 566212207989161947916303)
                    ·
                      rfl

theorem cell23_3308083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 5].length) (baseStart_3308083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308083 prefixEnd_3308083 := by exact prefixLift 3308083
  have htrace : WordTrace (prefixWord ++ tailWord_3308083) baseStart_3308083 baseEnd_3308083 := by
    simpa [prefixWord, tailWord_3308083, baseEnd_3308083] using wordTrace_append hprefix tailTrace_3308083
  have hstable : (prefixWord ++ tailWord_3308083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308083).length < 2 ^ (prefixWord ++ tailWord_3308083).sum := by decide
  have hdescent : baseEnd_3308083 < baseStart_3308083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308120 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 2, 4, 2]
def baseStart_3308120 : Nat := 118140960795 + 3308120 * 2 ^ 59
def prefixEnd_3308120 : Nat := 4983230072969 + 3 ^ 40 * 3308120 * 2
def baseEnd_3308120 : Nat := 1698655622751702198986239

theorem tailTrace_3308120 : CollatzResearch.WordTrace tailWord_3308120 prefixEnd_3308120 1698655622751702198986239 := by
  unfold tailWord_3308120
  simp only [CollatzResearch.WordTrace]
  refine ⟨60328524387626848380300907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80438032516835797840401209 60328524387626848380300907)
  ·
    refine ⟨90492786581440272570451361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60328524387626848380300907 90492786581440272570451361)
    ·
      refine ⟨67869589936080204427838521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90492786581440272570451361 67869589936080204427838521)
      ·
        refine ⟨50902192452060153320878891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67869589936080204427838521 50902192452060153320878891)
        ·
          refine ⟨76353288678090229981318337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50902192452060153320878891 76353288678090229981318337)
          ·
            refine ⟨57264966508567672485988753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76353288678090229981318337 57264966508567672485988753)
            ·
              refine ⟨42948724881425754364491565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57264966508567672485988753 42948724881425754364491565)
              ·
                refine ⟨16105771830534657886684337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42948724881425754364491565 16105771830534657886684337)
                ·
                  refine ⟨12079328872900993415013253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16105771830534657886684337 12079328872900993415013253)
                  ·
                    refine ⟨2264874163668936265314985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12079328872900993415013253 2264874163668936265314985)
                    ·
                      refine ⟨1698655622751702198986239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264874163668936265314985 1698655622751702198986239)
                      ·
                        rfl

theorem cell23_3308120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_3308120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308120 prefixEnd_3308120 := by exact prefixLift 3308120
  have htrace : WordTrace (prefixWord ++ tailWord_3308120) baseStart_3308120 baseEnd_3308120 := by
    simpa [prefixWord, tailWord_3308120, baseEnd_3308120] using wordTrace_append hprefix tailTrace_3308120
  have hstable : (prefixWord ++ tailWord_3308120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308120).length < 2 ^ (prefixWord ++ tailWord_3308120).sum := by decide
  have hdescent : baseEnd_3308120 < baseStart_3308120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308140 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_3308140 : Nat := 118140960795 + 3308140 * 2 ^ 59
def prefixEnd_3308140 : Nat := 4983230072969 + 3 ^ 40 * 3308140 * 2
def baseEnd_3308140 : Nat := 1698665892364792120736147

theorem tailTrace_3308140 : CollatzResearch.WordTrace tailWord_3308140 prefixEnd_3308140 1698665892364792120736147 := by
  unfold tailWord_3308140
  simp only [CollatzResearch.WordTrace]
  refine ⟨60328889117590620088164937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80438518823454160117553249 60328889117590620088164937)
  ·
    refine ⟨45246666838192965066123703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60328889117590620088164937 45246666838192965066123703)
    ·
      refine ⟨67870000257289447599185555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45246666838192965066123703 67870000257289447599185555)
      ·
        refine ⟨101805000385934171398778333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67870000257289447599185555 101805000385934171398778333)
        ·
          refine ⟨38176875144725314274541875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101805000385934171398778333 38176875144725314274541875)
          ·
            refine ⟨57265312717087971411812813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38176875144725314274541875 57265312717087971411812813)
            ·
              refine ⟨21474492268907989279429805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57265312717087971411812813 21474492268907989279429805)
              ·
                refine ⟨8052934600840495979786177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21474492268907989279429805 8052934600840495979786177)
                ·
                  refine ⟨6039700950630371984839633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8052934600840495979786177 6039700950630371984839633)
                  ·
                    refine ⟨4529775712972778988629725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6039700950630371984839633 4529775712972778988629725)
                    ·
                      refine ⟨1698665892364792120736147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529775712972778988629725 1698665892364792120736147)
                      ·
                        rfl

theorem cell23_3308140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_3308140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308140 prefixEnd_3308140 := by exact prefixLift 3308140
  have htrace : WordTrace (prefixWord ++ tailWord_3308140) baseStart_3308140 baseEnd_3308140 := by
    simpa [prefixWord, tailWord_3308140, baseEnd_3308140] using wordTrace_append hprefix tailTrace_3308140
  have hstable : (prefixWord ++ tailWord_3308140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308140).length < 2 ^ (prefixWord ++ tailWord_3308140).sum := by decide
  have hdescent : baseEnd_3308140 < baseStart_3308140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308160 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 6]
def baseStart_3308160 : Nat := 118140960795 + 3308160 * 2 ^ 59
def prefixEnd_3308160 : Nat := 4983230072969 + 3 ^ 40 * 3308160 * 2
def baseEnd_3308160 : Nat := 188741795775320226942895

theorem tailTrace_3308160 : CollatzResearch.WordTrace tailWord_3308160 prefixEnd_3308160 188741795775320226942895 := by
  unfold tailWord_3308160
  simp only [CollatzResearch.WordTrace]
  refine ⟨60329253847554391796028967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80439005130072522394705289 60329253847554391796028967)
  ·
    refine ⟨90493880771331587694043451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60329253847554391796028967 90493880771331587694043451)
    ·
      refine ⟨135740821156997381541065177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90493880771331587694043451 135740821156997381541065177)
      ·
        refine ⟨101805615867748036155798883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135740821156997381541065177 101805615867748036155798883)
        ·
          refine ⟨152708423801622054233698325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101805615867748036155798883 152708423801622054233698325)
          ·
            refine ⟨7158207365701033792204609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152708423801622054233698325 7158207365701033792204609)
            ·
              refine ⟨5368655524275775344153457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7158207365701033792204609 5368655524275775344153457)
              ·
                refine ⟨4026491643206831508115093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5368655524275775344153457 4026491643206831508115093)
                ·
                  refine ⟨188741795775320226942895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4026491643206831508115093 188741795775320226942895)
                  ·
                    rfl

theorem cell23_3308160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 6].length) (baseStart_3308160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308160 prefixEnd_3308160 := by exact prefixLift 3308160
  have htrace : WordTrace (prefixWord ++ tailWord_3308160) baseStart_3308160 baseEnd_3308160 := by
    simpa [prefixWord, tailWord_3308160, baseEnd_3308160] using wordTrace_append hprefix tailTrace_3308160
  have hstable : (prefixWord ++ tailWord_3308160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308160).length < 2 ^ (prefixWord ++ tailWord_3308160).sum := by decide
  have hdescent : baseEnd_3308160 < baseStart_3308160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308164 : List Nat := [2, 3, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_3308164 : Nat := 118140960795 + 3308164 * 2 ^ 59
def prefixEnd_3308164 : Nat := 4983230072969 + 3 ^ 40 * 3308164 * 2
def baseEnd_3308164 : Nat := 566226071966833342278679

theorem tailTrace_3308164 : CollatzResearch.WordTrace tailWord_3308164 prefixEnd_3308164 566226071966833342278679 := by
  unfold tailWord_3308164
  simp only [CollatzResearch.WordTrace]
  refine ⟨60329326793547146137601773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80439102391396194850135697 60329326793547146137601773)
  ·
    refine ⟨22623497547580179801600665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60329326793547146137601773 22623497547580179801600665)
    ·
      refine ⟨16967623160685134851200499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22623497547580179801600665 16967623160685134851200499)
      ·
        refine ⟨25451434741027702276800749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16967623160685134851200499 25451434741027702276800749)
        ·
          refine ⟨9544288027885388353800281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25451434741027702276800749 9544288027885388353800281)
          ·
            refine ⟨7158216020914041265350211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9544288027885388353800281 7158216020914041265350211)
            ·
              refine ⟨10737324031371061898025317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158216020914041265350211 10737324031371061898025317)
              ·
                refine ⟨2013248255882074105879747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10737324031371061898025317 2013248255882074105879747)
                ·
                  refine ⟨3019872383823111158819621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013248255882074105879747 3019872383823111158819621)
                  ·
                    refine ⟨566226071966833342278679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019872383823111158819621 566226071966833342278679)
                    ·
                      rfl

theorem cell23_3308164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_3308164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308164 prefixEnd_3308164 := by exact prefixLift 3308164
  have htrace : WordTrace (prefixWord ++ tailWord_3308164) baseStart_3308164 baseEnd_3308164 := by
    simpa [prefixWord, tailWord_3308164, baseEnd_3308164] using wordTrace_append hprefix tailTrace_3308164
  have hstable : (prefixWord ++ tailWord_3308164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308164).length < 2 ^ (prefixWord ++ tailWord_3308164).sum := by decide
  have hdescent : baseEnd_3308164 < baseStart_3308164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308183 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3308183 : Nat := 118140960795 + 3308183 * 2 ^ 59
def prefixEnd_3308183 : Nat := 4983230072969 + 3 ^ 40 * 3308183 * 2
def baseEnd_3308183 : Nat := 1698687972032935452498449

theorem tailTrace_3308183 : CollatzResearch.WordTrace tailWord_3308183 prefixEnd_3308183 1698687972032935452498449 := by
  unfold tailWord_3308183
  simp only [CollatzResearch.WordTrace]
  refine ⟨120659346574025458520145203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80439564382683639013430135 120659346574025458520145203)
  ·
    refine ⟨180989019861038187780217805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120659346574025458520145203 180989019861038187780217805)
    ·
      refine ⟨67870882447889320417581677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180989019861038187780217805 67870882447889320417581677)
      ·
        refine ⟨25451580917958495156593129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67870882447889320417581677 25451580917958495156593129)
        ·
          refine ⟨19088685688468871367444847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25451580917958495156593129 19088685688468871367444847)
          ·
            refine ⟨28633028532703307051167271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19088685688468871367444847 28633028532703307051167271)
            ·
              refine ⟨42949542799054960576750907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28633028532703307051167271 42949542799054960576750907)
              ·
                refine ⟨64424314198582440865126361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42949542799054960576750907 64424314198582440865126361)
                ·
                  refine ⟨48318235648936830648844771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64424314198582440865126361 48318235648936830648844771)
                  ·
                    refine ⟨72477353473405245973267157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48318235648936830648844771 72477353473405245973267157)
                    ·
                      refine ⟨1698687972032935452498449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72477353473405245973267157 1698687972032935452498449)
                      ·
                        rfl

theorem cell23_3308183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3308183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308183 prefixEnd_3308183 := by exact prefixLift 3308183
  have htrace : WordTrace (prefixWord ++ tailWord_3308183) baseStart_3308183 baseEnd_3308183 := by
    simpa [prefixWord, tailWord_3308183, baseEnd_3308183] using wordTrace_append hprefix tailTrace_3308183
  have hstable : (prefixWord ++ tailWord_3308183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308183).length < 2 ^ (prefixWord ++ tailWord_3308183).sum := by decide
  have hdescent : baseEnd_3308183 < baseStart_3308183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308207 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 1, 5]
def baseStart_3308207 : Nat := 118140960795 + 3308207 * 2 ^ 59
def prefixEnd_3308207 : Nat := 4983230072969 + 3 ^ 40 * 3308207 * 2
def baseEnd_3308207 : Nat := 566233431856214452866113

theorem tailTrace_3308207 : CollatzResearch.WordTrace tailWord_3308207 prefixEnd_3308207 566233431856214452866113 := by
  unfold tailWord_3308207
  simp only [CollatzResearch.WordTrace]
  refine ⟨120660221925938510619018875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80440147950625673746012583 120660221925938510619018875)
  ·
    refine ⟨180990332888907765928528313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120660221925938510619018875 180990332888907765928528313)
    ·
      refine ⟨135742749666680824446396235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180990332888907765928528313 135742749666680824446396235)
      ·
        refine ⟨203614124500021236669594353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135742749666680824446396235 203614124500021236669594353)
        ·
          refine ⟨152710593375015927502195765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203614124500021236669594353 152710593375015927502195765)
          ·
            refine ⟨14316618128907743203330853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152710593375015927502195765 14316618128907743203330853)
            ·
              refine ⟨2684365899170201850624535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14316618128907743203330853 2684365899170201850624535)
              ·
                refine ⟨4026548848755302775936803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684365899170201850624535 4026548848755302775936803)
                ·
                  refine ⟨6039823273132954163905205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026548848755302775936803 6039823273132954163905205)
                  ·
                    refine ⟨566233431856214452866113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6039823273132954163905205 566233431856214452866113)
                    ·
                      rfl

theorem cell23_3308207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 5].length) (baseStart_3308207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308207 prefixEnd_3308207 := by exact prefixLift 3308207
  have htrace : WordTrace (prefixWord ++ tailWord_3308207) baseStart_3308207 baseEnd_3308207 := by
    simpa [prefixWord, tailWord_3308207, baseEnd_3308207] using wordTrace_append hprefix tailTrace_3308207
  have hstable : (prefixWord ++ tailWord_3308207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308207).length < 2 ^ (prefixWord ++ tailWord_3308207).sum := by decide
  have hdescent : baseEnd_3308207 < baseStart_3308207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308247 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_3308247 : Nat := 118140960795 + 3308247 * 2 ^ 59
def prefixEnd_3308247 : Nat := 4983230072969 + 3 ^ 40 * 3308247 * 2
def baseEnd_3308247 : Nat := 1698720834794823202098155

theorem tailTrace_3308247 : CollatzResearch.WordTrace tailWord_3308247 prefixEnd_3308247 1698720834794823202098155 := by
  unfold tailWord_3308247
  simp only [CollatzResearch.WordTrace]
  refine ⟨120661680845793597450474995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80441120563862398300316663 120661680845793597450474995)
  ·
    refine ⟨180992521268690396175712493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120661680845793597450474995 180992521268690396175712493)
    ·
      refine ⟨67872195475758898565892185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180992521268690396175712493 67872195475758898565892185)
      ·
        refine ⟨50904146606819173924419139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67872195475758898565892185 50904146606819173924419139)
        ·
          refine ⟨76356219910228760886628709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50904146606819173924419139 76356219910228760886628709)
          ·
            refine ⟨14316791233167892666242883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76356219910228760886628709 14316791233167892666242883)
            ·
              refine ⟨21475186849751838999364325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14316791233167892666242883 21475186849751838999364325)
              ·
                refine ⟨4026597534328469812380811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21475186849751838999364325 4026597534328469812380811)
                ·
                  refine ⟨6039896301492704718571217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026597534328469812380811 6039896301492704718571217)
                  ·
                    refine ⟨4529922226119528538928413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6039896301492704718571217 4529922226119528538928413)
                    ·
                      refine ⟨1698720834794823202098155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4529922226119528538928413 1698720834794823202098155)
                      ·
                        rfl

theorem cell23_3308247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_3308247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308247 prefixEnd_3308247 := by exact prefixLift 3308247
  have htrace : WordTrace (prefixWord ++ tailWord_3308247) baseStart_3308247 baseEnd_3308247 := by
    simpa [prefixWord, tailWord_3308247, baseEnd_3308247] using wordTrace_append hprefix tailTrace_3308247
  have hstable : (prefixWord ++ tailWord_3308247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308247).length < 2 ^ (prefixWord ++ tailWord_3308247).sum := by decide
  have hdescent : baseEnd_3308247 < baseStart_3308247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308283 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10]
def baseStart_3308283 : Nat := 118140960795 + 3308283 * 2 ^ 59
def prefixEnd_3308283 : Nat := 4983230072969 + 3 ^ 40 * 3308283 * 2
def baseEnd_3308283 : Nat := 1698739320098385061247989

theorem tailTrace_3308283 : CollatzResearch.WordTrace tailWord_3308283 prefixEnd_3308283 1698739320098385061247989 := by
  unfold tailWord_3308283
  simp only [CollatzResearch.WordTrace]
  refine ⟨120662993873663175598785503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80441995915775450399190335 120662993873663175598785503)
  ·
    refine ⟨180994490810494763398178255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120662993873663175598785503 180994490810494763398178255)
    ·
      refine ⟨271491736215742145097267383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180994490810494763398178255 271491736215742145097267383)
      ·
        refine ⟨407237604323613217645901075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271491736215742145097267383 407237604323613217645901075)
        ·
          refine ⟨610856406485419826468851613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407237604323613217645901075 610856406485419826468851613)
          ·
            refine ⟨229071152432032434925819355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610856406485419826468851613 229071152432032434925819355)
            ·
              refine ⟨343606728648048652388729033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229071152432032434925819355 343606728648048652388729033)
              ·
                refine ⟨257705046486036489291546775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343606728648048652388729033 257705046486036489291546775)
                ·
                  refine ⟨386557569729054733937320163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257705046486036489291546775 386557569729054733937320163)
                  ·
                    refine ⟨579836354593582100905980245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 386557569729054733937320163 579836354593582100905980245)
                    ·
                      refine ⟨1698739320098385061247989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 579836354593582100905980245 1698739320098385061247989)
                      ·
                        rfl

theorem cell23_3308283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_3308283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308283 prefixEnd_3308283 := by exact prefixLift 3308283
  have htrace : WordTrace (prefixWord ++ tailWord_3308283) baseStart_3308283 baseEnd_3308283 := by
    simpa [prefixWord, tailWord_3308283, baseEnd_3308283] using wordTrace_append hprefix tailTrace_3308283
  have hstable : (prefixWord ++ tailWord_3308283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308283).length < 2 ^ (prefixWord ++ tailWord_3308283).sum := by decide
  have hdescent : baseEnd_3308283 < baseStart_3308283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308287 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 3, 3, 2]
def baseStart_3308287 : Nat := 118140960795 + 3308287 * 2 ^ 59
def prefixEnd_3308287 : Nat := 4983230072969 + 3 ^ 40 * 3308287 * 2
def baseEnd_3308287 : Nat := 1698741374021003045597971

theorem tailTrace_3308287 : CollatzResearch.WordTrace tailWord_3308287 prefixEnd_3308287 1698741374021003045597971 := by
  unfold tailWord_3308287
  simp only [CollatzResearch.WordTrace]
  refine ⟨120663139765648684281931115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80442093177099122854620743 120663139765648684281931115)
  ·
    refine ⟨180994709648473026422896673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120663139765648684281931115 180994709648473026422896673)
    ·
      refine ⟨135746032236354769817172505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180994709648473026422896673 135746032236354769817172505)
      ·
        refine ⟨101809524177266077362879379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135746032236354769817172505 101809524177266077362879379)
        ·
          refine ⟨152714286265899116044319069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101809524177266077362879379 152714286265899116044319069)
          ·
            refine ⟨57267857349712168516619651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152714286265899116044319069 57267857349712168516619651)
            ·
              refine ⟨85901786024568252774929477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57267857349712168516619651 85901786024568252774929477)
              ·
                refine ⟨16106584879606547395299277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85901786024568252774929477 16106584879606547395299277)
                ·
                  refine ⟨6039969329852455273237229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16106584879606547395299277 6039969329852455273237229)
                  ·
                    refine ⟨2264988498694670727463961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6039969329852455273237229 2264988498694670727463961)
                    ·
                      refine ⟨1698741374021003045597971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2264988498694670727463961 1698741374021003045597971)
                      ·
                        rfl

theorem cell23_3308287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_3308287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308287 prefixEnd_3308287 := by exact prefixLift 3308287
  have htrace : WordTrace (prefixWord ++ tailWord_3308287) baseStart_3308287 baseEnd_3308287 := by
    simpa [prefixWord, tailWord_3308287, baseEnd_3308287] using wordTrace_append hprefix tailTrace_3308287
  have hstable : (prefixWord ++ tailWord_3308287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308287).length < 2 ^ (prefixWord ++ tailWord_3308287).sum := by decide
  have hdescent : baseEnd_3308287 < baseStart_3308287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308321 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_3308321 : Nat := 118140960795 + 3308321 * 2 ^ 59
def prefixEnd_3308321 : Nat := 4983230072969 + 3 ^ 40 * 3308321 * 2
def baseEnd_3308321 : Nat := 1698758832363255912572815

theorem tailTrace_3308321 : CollatzResearch.WordTrace tailWord_3308321 prefixEnd_3308321 1698758832363255912572815 := by
  unfold tailWord_3308321
  simp only [CollatzResearch.WordTrace]
  refine ⟨120664379847525508088668817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80442919898350338725779211 120664379847525508088668817)
  ·
    refine ⟨90498284885644131066501613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120664379847525508088668817 90498284885644131066501613)
    ·
      refine ⟨33936856832116549149938105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90498284885644131066501613 33936856832116549149938105)
      ·
        refine ⟨25452642624087411862453579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33936856832116549149938105 25452642624087411862453579)
        ·
          refine ⟨38178963936131117793680369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25452642624087411862453579 38178963936131117793680369)
          ·
            refine ⟨28634222952098338345260277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38178963936131117793680369 28634222952098338345260277)
            ·
              refine ⟨2684458401759219219868151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28634222952098338345260277 2684458401759219219868151)
              ·
                refine ⟨4026687602638828829802227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684458401759219219868151 4026687602638828829802227)
                ·
                  refine ⟨6040031403958243244703341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026687602638828829802227 6040031403958243244703341)
                  ·
                    refine ⟨2265011776484341216763753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6040031403958243244703341 2265011776484341216763753)
                    ·
                      refine ⟨1698758832363255912572815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265011776484341216763753 1698758832363255912572815)
                      ·
                        rfl

theorem cell23_3308321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_3308321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308321 prefixEnd_3308321 := by exact prefixLift 3308321
  have htrace : WordTrace (prefixWord ++ tailWord_3308321) baseStart_3308321 baseEnd_3308321 := by
    simpa [prefixWord, tailWord_3308321, baseEnd_3308321] using wordTrace_append hprefix tailTrace_3308321
  have hstable : (prefixWord ++ tailWord_3308321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308321).length < 2 ^ (prefixWord ++ tailWord_3308321).sum := by decide
  have hdescent : baseEnd_3308321 < baseStart_3308321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308351 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 2, 2, 2]
def baseStart_3308351 : Nat := 118140960795 + 3308351 * 2 ^ 59
def prefixEnd_3308351 : Nat := 4983230072969 + 3 ^ 40 * 3308351 * 2
def baseEnd_3308351 : Nat := 1698774236782890795197677

theorem tailTrace_3308351 : CollatzResearch.WordTrace tailWord_3308351 prefixEnd_3308351 1698774236782890795197677 := by
  unfold tailWord_3308351
  simp only [CollatzResearch.WordTrace]
  refine ⟨120665474037416823212260907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80443649358277882141507271 120665474037416823212260907)
  ·
    refine ⟨180998211056125234818391361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120665474037416823212260907 180998211056125234818391361)
    ·
      refine ⟨135748658292093926113793521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180998211056125234818391361 135748658292093926113793521)
      ·
        refine ⟨101811493719070444585345141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135748658292093926113793521 101811493719070444585345141)
        ·
          refine ⟨9544827536162854179876107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101811493719070444585345141 9544827536162854179876107)
          ·
            refine ⟨14317241304244281269814161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544827536162854179876107 14317241304244281269814161)
            ·
              refine ⟨10737930978183210952360621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14317241304244281269814161 10737930978183210952360621)
              ·
                refine ⟨4026724116818704107135233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10737930978183210952360621 4026724116818704107135233)
                ·
                  refine ⟨3020043087614028080351425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4026724116818704107135233 3020043087614028080351425)
                  ·
                    refine ⟨2265032315710521060263569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3020043087614028080351425 2265032315710521060263569)
                    ·
                      refine ⟨1698774236782890795197677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265032315710521060263569 1698774236782890795197677)
                      ·
                        rfl

theorem cell23_3308351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_3308351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308351 prefixEnd_3308351 := by exact prefixLift 3308351
  have htrace : WordTrace (prefixWord ++ tailWord_3308351) baseStart_3308351 baseEnd_3308351 := by
    simpa [prefixWord, tailWord_3308351, baseEnd_3308351] using wordTrace_append hprefix tailTrace_3308351
  have hstable : (prefixWord ++ tailWord_3308351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308351).length < 2 ^ (prefixWord ++ tailWord_3308351).sum := by decide
  have hdescent : baseEnd_3308351 < baseStart_3308351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308427 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 3]
def baseStart_3308427 : Nat := 118140960795 + 3308427 * 2 ^ 59
def prefixEnd_3308427 : Nat := 4983230072969 + 3 ^ 40 * 3308427 * 2
def baseEnd_3308427 : Nat := 1698813261312632497847327

theorem tailTrace_3308427 : CollatzResearch.WordTrace tailWord_3308427 prefixEnd_3308427 1698813261312632497847327 := by
  unfold tailWord_3308427
  simp only [CollatzResearch.WordTrace]
  refine ⟨120668245985141488192027535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80445497323427658794685023 120668245985141488192027535)
  ·
    refine ⟨181002368977712232288041303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120668245985141488192027535 181002368977712232288041303)
    ·
      refine ⟨271503553466568348432061955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181002368977712232288041303 271503553466568348432061955)
      ·
        refine ⟨407255330199852522648092933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271503553466568348432061955 407255330199852522648092933)
        ·
          refine ⟨76360374412472347996517425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407255330199852522648092933 76360374412472347996517425)
          ·
            refine ⟨57270280809354260997388069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76360374412472347996517425 57270280809354260997388069)
            ·
              refine ⟨10738177651753923937010263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57270280809354260997388069 10738177651753923937010263)
              ·
                refine ⟨16107266477630885905515395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738177651753923937010263 16107266477630885905515395)
                ·
                  refine ⟨24160899716446328858273093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16107266477630885905515395 24160899716446328858273093)
                  ·
                    refine ⟨4530168696833686660926205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24160899716446328858273093 4530168696833686660926205)
                    ·
                      refine ⟨1698813261312632497847327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4530168696833686660926205 1698813261312632497847327)
                      ·
                        rfl

theorem cell23_3308427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 3].length) (baseStart_3308427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308427 prefixEnd_3308427 := by exact prefixLift 3308427
  have htrace : WordTrace (prefixWord ++ tailWord_3308427) baseStart_3308427 baseEnd_3308427 := by
    simpa [prefixWord, tailWord_3308427, baseEnd_3308427] using wordTrace_append hprefix tailTrace_3308427
  have hstable : (prefixWord ++ tailWord_3308427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308427).length < 2 ^ (prefixWord ++ tailWord_3308427).sum := by decide
  have hdescent : baseEnd_3308427 < baseStart_3308427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308438 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3308438 : Nat := 118140960795 + 3308438 * 2 ^ 59
def prefixEnd_3308438 : Nat := 4983230072969 + 3 ^ 40 * 3308438 * 2
def baseEnd_3308438 : Nat := 566272969866610651603259

theorem tailTrace_3308438 : CollatzResearch.WordTrace tailWord_3308438 prefixEnd_3308438 566272969866610651603259 := by
  unfold tailWord_3308438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7541790449256352316917373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80445764792067758047118645 7541790449256352316917373)
  ·
    refine ⟨2828171418471132118844015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7541790449256352316917373 2828171418471132118844015)
    ·
      refine ⟨4242257127706698178266023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828171418471132118844015 4242257127706698178266023)
      ·
        refine ⟨6363385691560047267399035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4242257127706698178266023 6363385691560047267399035)
        ·
          refine ⟨9545078537340070901098553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363385691560047267399035 9545078537340070901098553)
          ·
            refine ⟨7158808903005053175823915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9545078537340070901098553 7158808903005053175823915)
            ·
              refine ⟨10738213354507579763735873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158808903005053175823915 10738213354507579763735873)
              ·
                refine ⟨8053660015880684822801905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10738213354507579763735873 8053660015880684822801905)
                ·
                  refine ⟨6040245011910513617101429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8053660015880684822801905 6040245011910513617101429)
                  ·
                    refine ⟨566272969866610651603259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6040245011910513617101429 566272969866610651603259)
                    ·
                      rfl

theorem cell23_3308438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3308438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308438 prefixEnd_3308438 := by exact prefixLift 3308438
  have htrace : WordTrace (prefixWord ++ tailWord_3308438) baseStart_3308438 baseEnd_3308438 := by
    simpa [prefixWord, tailWord_3308438, baseEnd_3308438] using wordTrace_append hprefix tailTrace_3308438
  have hstable : (prefixWord ++ tailWord_3308438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308438).length < 2 ^ (prefixWord ++ tailWord_3308438).sum := by decide
  have hdescent : baseEnd_3308438 < baseStart_3308438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308447 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 8]
def baseStart_3308447 : Nat := 118140960795 + 3308447 * 2 ^ 59
def prefixEnd_3308447 : Nat := 4983230072969 + 3 ^ 40 * 3308447 * 2
def baseEnd_3308447 : Nat := 188758170102858046621915

theorem tailTrace_3308447 : CollatzResearch.WordTrace tailWord_3308447 prefixEnd_3308447 188758170102858046621915 := by
  unfold tailWord_3308447
  simp only [CollatzResearch.WordTrace]
  refine ⟨120668975445069031607755595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80445983630046021071837063 120668975445069031607755595)
  ·
    refine ⟨181003463167603547411633393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120668975445069031607755595 181003463167603547411633393)
    ·
      refine ⟨135752597375702660558725045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181003463167603547411633393 135752597375702660558725045)
      ·
        refine ⟨12726806003972124427380473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135752597375702660558725045 12726806003972124427380473)
        ·
          refine ⟨9545104502979093320535355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12726806003972124427380473 9545104502979093320535355)
          ·
            refine ⟨14317656754468639980803033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9545104502979093320535355 14317656754468639980803033)
            ·
              refine ⟨10738242565851479985602275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14317656754468639980803033 10738242565851479985602275)
              ·
                refine ⟨16107363848777219978403413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738242565851479985602275 16107363848777219978403413)
                ·
                  refine ⟨188758170102858046621915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16107363848777219978403413 188758170102858046621915)
                  ·
                    rfl

theorem cell23_3308447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 8].length) (baseStart_3308447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308447 prefixEnd_3308447 := by exact prefixLift 3308447
  have htrace : WordTrace (prefixWord ++ tailWord_3308447) baseStart_3308447 baseEnd_3308447 := by
    simpa [prefixWord, tailWord_3308447, baseEnd_3308447] using wordTrace_append hprefix tailTrace_3308447
  have hstable : (prefixWord ++ tailWord_3308447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308447).length < 2 ^ (prefixWord ++ tailWord_3308447).sum := by decide
  have hdescent : baseEnd_3308447 < baseStart_3308447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308474 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_3308474 : Nat := 118140960795 + 3308474 * 2 ^ 59
def prefixEnd_3308474 : Nat := 4983230072969 + 3 ^ 40 * 3308474 * 2
def baseEnd_3308474 : Nat := 1698837394903393813959611

theorem tailTrace_3308474 : CollatzResearch.WordTrace tailWord_3308474 prefixEnd_3308474 1698837394903393813959611 := by
  unfold tailWord_3308474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30167490053992803804747119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80446640143980810145992317 30167490053992803804747119)
  ·
    refine ⟨45251235080989205707120679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30167490053992803804747119 45251235080989205707120679)
    ·
      refine ⟨67876852621483808560681019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45251235080989205707120679 67876852621483808560681019)
      ·
        refine ⟨101815278932225712841021529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67876852621483808560681019 101815278932225712841021529)
        ·
          refine ⟨76361459199169284630766147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101815278932225712841021529 76361459199169284630766147)
          ·
            refine ⟨114542188798753926946149221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76361459199169284630766147 114542188798753926946149221)
            ·
              refine ⟨21476660399766361302402979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114542188798753926946149221 21476660399766361302402979)
              ·
                refine ⟨32214990599649541953604469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21476660399766361302402979 32214990599649541953604469)
                ·
                  refine ⟨3020155368717144558150419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32214990599649541953604469 3020155368717144558150419)
                  ·
                    refine ⟨4530233053075716837225629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3020155368717144558150419 4530233053075716837225629)
                    ·
                      refine ⟨1698837394903393813959611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4530233053075716837225629 1698837394903393813959611)
                      ·
                        rfl

theorem cell23_3308474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_3308474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308474 prefixEnd_3308474 := by exact prefixLift 3308474
  have htrace : WordTrace (prefixWord ++ tailWord_3308474) baseStart_3308474 baseEnd_3308474 := by
    simpa [prefixWord, tailWord_3308474, baseEnd_3308474] using wordTrace_append hprefix tailTrace_3308474
  have hstable : (prefixWord ++ tailWord_3308474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308474).length < 2 ^ (prefixWord ++ tailWord_3308474).sum := by decide
  have hdescent : baseEnd_3308474 < baseStart_3308474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308502 : List Nat := [5, 2, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3308502 : Nat := 118140960795 + 3308502 * 2 ^ 59
def prefixEnd_3308502 : Nat := 4983230072969 + 3 ^ 40 * 3308502 * 2
def baseEnd_3308502 : Nat := 566283924120573234803161

theorem tailTrace_3308502 : CollatzResearch.WordTrace tailWord_3308502 prefixEnd_3308502 566283924120573234803161 := by
  unfold tailWord_3308502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7541936341241861000062985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80447320973246517334005173 7541936341241861000062985)
  ·
    refine ⟨5656452255931395750047239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7541936341241861000062985 5656452255931395750047239)
    ·
      refine ⟨8484678383897093625070859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5656452255931395750047239 8484678383897093625070859)
      ·
        refine ⟨12727017575845640437606289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8484678383897093625070859 12727017575845640437606289)
        ·
          refine ⟨9545263181884230328204717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12727017575845640437606289 9545263181884230328204717)
          ·
            refine ⟨3579473693206586373076769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9545263181884230328204717 3579473693206586373076769)
            ·
              refine ⟨2684605269904939779807577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579473693206586373076769 2684605269904939779807577)
              ·
                refine ⟨2013453952428704834855683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684605269904939779807577 2013453952428704834855683)
                ·
                  refine ⟨3020180928643057252283525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013453952428704834855683 3020180928643057252283525)
                  ·
                    refine ⟨566283924120573234803161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020180928643057252283525 566283924120573234803161)
                    ·
                      rfl

theorem cell23_3308502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3308502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308502 prefixEnd_3308502 := by exact prefixLift 3308502
  have htrace : WordTrace (prefixWord ++ tailWord_3308502) baseStart_3308502 baseEnd_3308502 := by
    simpa [prefixWord, tailWord_3308502, baseEnd_3308502] using wordTrace_append hprefix tailTrace_3308502
  have hstable : (prefixWord ++ tailWord_3308502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308502).length < 2 ^ (prefixWord ++ tailWord_3308502).sum := by decide
  have hdescent : baseEnd_3308502 < baseStart_3308502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308542 : List Nat := [4, 2, 2, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_3308542 : Nat := 118140960795 + 3308542 * 2 ^ 59
def prefixEnd_3308542 : Nat := 4983230072969 + 3 ^ 40 * 3308542 * 2
def baseEnd_3308542 : Nat := 1698872311587899547909299

theorem tailTrace_3308542 : CollatzResearch.WordTrace tailWord_3308542 prefixEnd_3308542 1698872311587899547909299 := by
  unfold tailWord_3308542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084055047465607854057985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80448293586483241888309253 15084055047465607854057985)
  ·
    refine ⟨11313041285599205890543489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15084055047465607854057985 11313041285599205890543489)
    ·
      refine ⟨8484780964199404417907617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11313041285599205890543489 8484780964199404417907617)
      ·
        refine ⟨6363585723149553313430713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8484780964199404417907617 6363585723149553313430713)
        ·
          refine ⟨4772689292362164985073035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6363585723149553313430713 4772689292362164985073035)
          ·
            refine ⟨7159033938543247477609553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772689292362164985073035 7159033938543247477609553)
            ·
              refine ⟨5369275453907435608207165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159033938543247477609553 5369275453907435608207165)
              ·
                refine ⟨2013478295215288353077687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5369275453907435608207165 2013478295215288353077687)
                ·
                  refine ⟨3020217442822932529616531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013478295215288353077687 3020217442822932529616531)
                  ·
                    refine ⟨4530326164234398794424797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3020217442822932529616531 4530326164234398794424797)
                    ·
                      refine ⟨1698872311587899547909299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4530326164234398794424797 1698872311587899547909299)
                      ·
                        rfl

theorem cell23_3308542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_3308542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308542 prefixEnd_3308542 := by exact prefixLift 3308542
  have htrace : WordTrace (prefixWord ++ tailWord_3308542) baseStart_3308542 baseEnd_3308542 := by
    simpa [prefixWord, tailWord_3308542, baseEnd_3308542] using wordTrace_append hprefix tailTrace_3308542
  have hstable : (prefixWord ++ tailWord_3308542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308542).length < 2 ^ (prefixWord ++ tailWord_3308542).sum := by decide
  have hdescent : baseEnd_3308542 < baseStart_3308542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308551 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3308551 : Nat := 118140960795 + 3308551 * 2 ^ 59
def prefixEnd_3308551 : Nat := 4983230072969 + 3 ^ 40 * 3308551 * 2
def baseEnd_3308551 : Nat := 1698876932913790012696757

theorem tailTrace_3308551 : CollatzResearch.WordTrace tailWord_3308551 prefixEnd_3308551 1698876932913790012696757 := by
  unfold tailWord_3308551
  simp only [CollatzResearch.WordTrace]
  refine ⟨120672768636692257369541507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80448512424461504913027671 120672768636692257369541507)
  ·
    refine ⟨181009152955038386054312261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120672768636692257369541507 181009152955038386054312261)
    ·
      refine ⟨33939216179069697385183549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181009152955038386054312261 33939216179069697385183549)
      ·
        refine ⟨12727206067151136519443831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33939216179069697385183549 12727206067151136519443831)
        ·
          refine ⟨19090809100726704779165747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12727206067151136519443831 19090809100726704779165747)
          ·
            refine ⟨28636213651090057168748621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19090809100726704779165747 28636213651090057168748621)
            ·
              refine ⟨10738580119158771438280733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28636213651090057168748621 10738580119158771438280733)
              ·
                refine ⟨4026967544684539289355275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10738580119158771438280733 4026967544684539289355275)
                ·
                  refine ⟨6040451317026808934032913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026967544684539289355275 6040451317026808934032913)
                  ·
                    refine ⟨4530338487770106700524685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6040451317026808934032913 4530338487770106700524685)
                    ·
                      refine ⟨1698876932913790012696757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4530338487770106700524685 1698876932913790012696757)
                      ·
                        rfl

theorem cell23_3308551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3308551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308551 prefixEnd_3308551 := by exact prefixLift 3308551
  have htrace : WordTrace (prefixWord ++ tailWord_3308551) baseStart_3308551 baseEnd_3308551 := by
    simpa [prefixWord, tailWord_3308551, baseEnd_3308551] using wordTrace_append hprefix tailTrace_3308551
  have hstable : (prefixWord ++ tailWord_3308551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308551).length < 2 ^ (prefixWord ++ tailWord_3308551).sum := by decide
  have hdescent : baseEnd_3308551 < baseStart_3308551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308558 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_3308558 : Nat := 118140960795 + 3308558 * 2 ^ 59
def prefixEnd_3308558 : Nat := 4983230072969 + 3 ^ 40 * 3308558 * 2
def baseEnd_3308558 : Nat := 566293509092790495103075

theorem tailTrace_3308558 : CollatzResearch.WordTrace tailWord_3308558 prefixEnd_3308558 566293509092790495103075 := by
  unfold tailWord_3308558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084127993458362195630791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80448682631777931710030885 15084127993458362195630791)
  ·
    refine ⟨22626191990187543293446187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15084127993458362195630791 22626191990187543293446187)
    ·
      refine ⟨33939287985281314940169281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22626191990187543293446187 33939287985281314940169281)
      ·
        refine ⟨25454465988960986205126961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33939287985281314940169281 25454465988960986205126961)
        ·
          refine ⟨19090849491720739653845221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25454465988960986205126961 19090849491720739653845221)
          ·
            refine ⟨3579534279697638685095979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19090849491720739653845221 3579534279697638685095979)
            ·
              refine ⟨5369301419546458027643969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579534279697638685095979 5369301419546458027643969)
              ·
                refine ⟨4026976064659843520732977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369301419546458027643969 4026976064659843520732977)
                ·
                  refine ⟨3020232048494882640549733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4026976064659843520732977 3020232048494882640549733)
                  ·
                    refine ⟨566293509092790495103075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020232048494882640549733 566293509092790495103075)
                    ·
                      rfl

theorem cell23_3308558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_3308558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308558 prefixEnd_3308558 := by exact prefixLift 3308558
  have htrace : WordTrace (prefixWord ++ tailWord_3308558) baseStart_3308558 baseEnd_3308558 := by
    simpa [prefixWord, tailWord_3308558, baseEnd_3308558] using wordTrace_append hprefix tailTrace_3308558
  have hstable : (prefixWord ++ tailWord_3308558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308558).length < 2 ^ (prefixWord ++ tailWord_3308558).sum := by decide
  have hdescent : baseEnd_3308558 < baseStart_3308558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308565 : List Nat := [1, 3, 2, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_3308565 : Nat := 118140960795 + 3308565 * 2 ^ 59
def prefixEnd_3308565 : Nat := 4983230072969 + 3 ^ 40 * 3308565 * 2
def baseEnd_3308565 : Nat := 1698884121642952957921693

theorem tailTrace_3308565 : CollatzResearch.WordTrace tailWord_3308565 prefixEnd_3308565 1698884121642952957921693 := by
  unfold tailWord_3308565
  simp only [CollatzResearch.WordTrace]
  refine ⟨120673279258641537760551149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80448852839094358507034099 120673279258641537760551149)
  ·
    refine ⟨45252479721990576660206681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120673279258641537760551149 45252479721990576660206681)
    ·
      refine ⟨33939359791492932495155011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45252479721990576660206681 33939359791492932495155011)
      ·
        refine ⟨50909039687239398742732517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33939359791492932495155011 50909039687239398742732517)
        ·
          refine ⟨9545444941357387264262347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50909039687239398742732517 9545444941357387264262347)
          ·
            refine ⟨14318167412036080896393521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9545444941357387264262347 14318167412036080896393521)
            ·
              refine ⟨10738625559027060672295141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14318167412036080896393521 10738625559027060672295141)
              ·
                refine ⟨2013492292317573876055339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10738625559027060672295141 2013492292317573876055339)
                ·
                  refine ⟨3020238438476360814083009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013492292317573876055339 3020238438476360814083009)
                  ·
                    refine ⟨2265178828857270610562257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3020238438476360814083009 2265178828857270610562257)
                    ·
                      refine ⟨1698884121642952957921693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265178828857270610562257 1698884121642952957921693)
                      ·
                        rfl

theorem cell23_3308565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_3308565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308565 prefixEnd_3308565 := by exact prefixLift 3308565
  have htrace : WordTrace (prefixWord ++ tailWord_3308565) baseStart_3308565 baseEnd_3308565 := by
    simpa [prefixWord, tailWord_3308565, baseEnd_3308565] using wordTrace_append hprefix tailTrace_3308565
  have hstable : (prefixWord ++ tailWord_3308565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308565).length < 2 ^ (prefixWord ++ tailWord_3308565).sum := by decide
  have hdescent : baseEnd_3308565 < baseStart_3308565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308598 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3308598 : Nat := 118140960795 + 3308598 * 2 ^ 59
def prefixEnd_3308598 : Nat := 4983230072969 + 3 ^ 40 * 3308598 * 2
def baseEnd_3308598 : Nat := 1698901066504551328809041

theorem tailTrace_3308598 : CollatzResearch.WordTrace tailWord_3308598 prefixEnd_3308598 1698901066504551328809041 := by
  unfold tailWord_3308598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542155179220124024781403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80449655245014656264334965 7542155179220124024781403)
  ·
    refine ⟨11313232768830186037172105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7542155179220124024781403 11313232768830186037172105)
    ·
      refine ⟨8484924576622639527879079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11313232768830186037172105 8484924576622639527879079)
      ·
        refine ⟨12727386864933959291818619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8484924576622639527879079 12727386864933959291818619)
        ·
          refine ⟨19091080297400938937727929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12727386864933959291818619 19091080297400938937727929)
          ·
            refine ⟨14318310223050704203295947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19091080297400938937727929 14318310223050704203295947)
            ·
              refine ⟨21477465334576056304943921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318310223050704203295947 21477465334576056304943921)
              ·
                refine ⟨16108099000932042228707941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21477465334576056304943921 16108099000932042228707941)
                ·
                  refine ⟨3020268562674757917882739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16108099000932042228707941 3020268562674757917882739)
                  ·
                    refine ⟨4530402844012136876824109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3020268562674757917882739 4530402844012136876824109)
                    ·
                      refine ⟨1698901066504551328809041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4530402844012136876824109 1698901066504551328809041)
                      ·
                        rfl

theorem cell23_3308598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3308598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308598 prefixEnd_3308598 := by exact prefixLift 3308598
  have htrace : WordTrace (prefixWord ++ tailWord_3308598) baseStart_3308598 baseEnd_3308598 := by
    simpa [prefixWord, tailWord_3308598, baseEnd_3308598] using wordTrace_append hprefix tailTrace_3308598
  have hstable : (prefixWord ++ tailWord_3308598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308598).length < 2 ^ (prefixWord ++ tailWord_3308598).sum := by decide
  have hdescent : baseEnd_3308598 < baseStart_3308598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308617 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_3308617 : Nat := 118140960795 + 3308617 * 2 ^ 59
def prefixEnd_3308617 : Nat := 4983230072969 + 3 ^ 40 * 3308617 * 2
def baseEnd_3308617 : Nat := 1698910822636986754471453

theorem tailTrace_3308617 : CollatzResearch.WordTrace tailWord_3308617 prefixEnd_3308617 1698910822636986754471453 := by
  unfold tailWord_3308617
  simp only [CollatzResearch.WordTrace]
  refine ⟨120675175854453150641444105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80450117236302100427629403 120675175854453150641444105)
  ·
    refine ⟨90506381890839862981083079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120675175854453150641444105 90506381890839862981083079)
    ·
      refine ⟨135759572836259794471624619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90506381890839862981083079 135759572836259794471624619)
      ·
        refine ⟨203639359254389691707436929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135759572836259794471624619 203639359254389691707436929)
        ·
          refine ⟨152729519440792268780577697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203639359254389691707436929 152729519440792268780577697)
          ·
            refine ⟨114547139580594201585433273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152729519440792268780577697 114547139580594201585433273)
            ·
              refine ⟨85910354685445651189074955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114547139580594201585433273 85910354685445651189074955)
              ·
                refine ⟨128865532028168476783612433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85910354685445651189074955 128865532028168476783612433)
                ·
                  refine ⟨96649149021126357587709325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128865532028168476783612433 96649149021126357587709325)
                  ·
                    refine ⟨36243430882922384095390997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96649149021126357587709325 36243430882922384095390997)
                    ·
                      refine ⟨1698910822636986754471453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36243430882922384095390997 1698910822636986754471453)
                      ·
                        rfl

theorem cell23_3308617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_3308617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308617 prefixEnd_3308617 := by exact prefixLift 3308617
  have htrace : WordTrace (prefixWord ++ tailWord_3308617) baseStart_3308617 baseEnd_3308617 := by
    simpa [prefixWord, tailWord_3308617, baseEnd_3308617] using wordTrace_append hprefix tailTrace_3308617
  have hstable : (prefixWord ++ tailWord_3308617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308617).length < 2 ^ (prefixWord ++ tailWord_3308617).sum := by decide
  have hdescent : baseEnd_3308617 < baseStart_3308617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308642 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3308642 : Nat := 118140960795 + 3308642 * 2 ^ 59
def prefixEnd_3308642 : Nat := 4983230072969 + 3 ^ 40 * 3308642 * 2
def baseEnd_3308642 : Nat := 1698923659653349156658839

theorem tailTrace_3308642 : CollatzResearch.WordTrace tailWord_3308642 prefixEnd_3308642 1698923659653349156658839 := by
  unfold tailWord_3308642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30169021919840644977776045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80450725119575053274069453 30169021919840644977776045)
  ·
    refine ⟨11313383219940241866666017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30169021919840644977776045 11313383219940241866666017)
    ·
      refine ⟨8485037414955181399999513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11313383219940241866666017 8485037414955181399999513)
      ·
        refine ⟨6363778061216386049999635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8485037414955181399999513 6363778061216386049999635)
        ·
          refine ⟨9545667091824579074999453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363778061216386049999635 9545667091824579074999453)
          ·
            refine ⟨3579625159434217153124795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9545667091824579074999453 3579625159434217153124795)
            ·
              refine ⟨5369437739151325729687193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579625159434217153124795 5369437739151325729687193)
              ·
                refine ⟨4027078304363494297265395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369437739151325729687193 4027078304363494297265395)
                ·
                  refine ⟨6040617456545241445898093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027078304363494297265395 6040617456545241445898093)
                  ·
                    refine ⟨2265231546204465542211785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6040617456545241445898093 2265231546204465542211785)
                    ·
                      refine ⟨1698923659653349156658839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265231546204465542211785 1698923659653349156658839)
                      ·
                        rfl

theorem cell23_3308642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3308642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308642 prefixEnd_3308642 := by exact prefixLift 3308642
  have htrace : WordTrace (prefixWord ++ tailWord_3308642) baseStart_3308642 baseEnd_3308642 := by
    simpa [prefixWord, tailWord_3308642, baseEnd_3308642] using wordTrace_append hprefix tailTrace_3308642
  have hstable : (prefixWord ++ tailWord_3308642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308642).length < 2 ^ (prefixWord ++ tailWord_3308642).sum := by decide
  have hdescent : baseEnd_3308642 < baseStart_3308642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308681 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 2, 5, 2]
def baseStart_3308681 : Nat := 118140960795 + 3308681 * 2 ^ 59
def prefixEnd_3308681 : Nat := 4983230072969 + 3 ^ 40 * 3308681 * 2
def baseEnd_3308681 : Nat := 1698943685398874504071159

theorem tailTrace_3308681 : CollatzResearch.WordTrace tailWord_3308681 prefixEnd_3308681 1698943685398874504071159 := by
  unfold tailWord_3308681
  simp only [CollatzResearch.WordTrace]
  refine ⟨120677510126221289571773897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80451673417480859714515931 120677510126221289571773897)
  ·
    refine ⟨90508132594665967178830423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120677510126221289571773897 90508132594665967178830423)
    ·
      refine ⟨135762198891998950768245635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90508132594665967178830423 135762198891998950768245635)
      ·
        refine ⟨203643298337998426152368453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135762198891998950768245635 203643298337998426152368453)
        ·
          refine ⟨38183118438374704903569085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203643298337998426152368453 38183118438374704903569085)
          ·
            refine ⟨14318669414390514338838407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38183118438374704903569085 14318669414390514338838407)
            ·
              refine ⟨21478004121585771508257611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318669414390514338838407 21478004121585771508257611)
              ·
                refine ⟨32217006182378657262386417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21478004121585771508257611 32217006182378657262386417)
                ·
                  refine ⟨24162754636783992946789813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32217006182378657262386417 24162754636783992946789813)
                  ·
                    refine ⟨2265258247198499338761545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24162754636783992946789813 2265258247198499338761545)
                    ·
                      refine ⟨1698943685398874504071159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265258247198499338761545 1698943685398874504071159)
                      ·
                        rfl

theorem cell23_3308681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 5, 2].length) (baseStart_3308681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308681 prefixEnd_3308681 := by exact prefixLift 3308681
  have htrace : WordTrace (prefixWord ++ tailWord_3308681) baseStart_3308681 baseEnd_3308681 := by
    simpa [prefixWord, tailWord_3308681, baseEnd_3308681] using wordTrace_append hprefix tailTrace_3308681
  have hstable : (prefixWord ++ tailWord_3308681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308681).length < 2 ^ (prefixWord ++ tailWord_3308681).sum := by decide
  have hdescent : baseEnd_3308681 < baseStart_3308681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308708 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_3308708 : Nat := 118140960795 + 3308708 * 2 ^ 59
def prefixEnd_3308708 : Nat := 4983230072969 + 3 ^ 40 * 3308708 * 2
def baseEnd_3308708 : Nat := 566319183125515299477845

theorem tailTrace_3308708 : CollatzResearch.WordTrace tailWord_3308708 prefixEnd_3308708 566319183125515299477845 := by
  unfold tailWord_3308708
  simp only [CollatzResearch.WordTrace]
  refine ⟨60339247448561736591503389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80452329931415648788671185 60339247448561736591503389)
  ·
    refine ⟨22627217793210651221813771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60339247448561736591503389 22627217793210651221813771)
    ·
      refine ⟨33940826689815976832720657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22627217793210651221813771 33940826689815976832720657)
      ·
        refine ⟨25455620017361982624540493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33940826689815976832720657 25455620017361982624540493)
        ·
          refine ⟨9545857506510743484202685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25455620017361982624540493 9545857506510743484202685)
          ·
            refine ⟨3579696564941528806576007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9545857506510743484202685 3579696564941528806576007)
            ·
              refine ⟨5369544847412293209864011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579696564941528806576007 5369544847412293209864011)
              ·
                refine ⟨8054317271118439814796017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369544847412293209864011 8054317271118439814796017)
                ·
                  refine ⟨6040737953338829861097013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8054317271118439814796017 6040737953338829861097013)
                  ·
                    refine ⟨566319183125515299477845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6040737953338829861097013 566319183125515299477845)
                    ·
                      rfl

theorem cell23_3308708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_3308708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308708 prefixEnd_3308708 := by exact prefixLift 3308708
  have htrace : WordTrace (prefixWord ++ tailWord_3308708) baseStart_3308708 baseEnd_3308708 := by
    simpa [prefixWord, tailWord_3308708, baseEnd_3308708] using wordTrace_append hprefix tailTrace_3308708
  have hstable : (prefixWord ++ tailWord_3308708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308708).length < 2 ^ (prefixWord ++ tailWord_3308708).sum := by decide
  have hdescent : baseEnd_3308708 < baseStart_3308708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308802 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 6]
def baseStart_3308802 : Nat := 118140960795 + 3308802 * 2 ^ 59
def prefixEnd_3308802 : Nat := 4983230072969 + 3 ^ 40 * 3308802 * 2
def baseEnd_3308802 : Nat := 188778424062007614517567

theorem tailTrace_3308802 : CollatzResearch.WordTrace tailWord_3308802 prefixEnd_3308802 188778424062007614517567 := by
  unfold tailWord_3308802
  simp only [CollatzResearch.WordTrace]
  refine ⟨30170480839695731809232165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80454615572521951491285773 30170480839695731809232165)
  ·
    refine ⟨5656965157442949714231031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30170480839695731809232165 5656965157442949714231031)
    ·
      refine ⟨8485447736164424571346547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5656965157442949714231031 8485447736164424571346547)
      ·
        refine ⟨12728171604246636857019821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8485447736164424571346547 12728171604246636857019821)
        ·
          refine ⟨4773064351592488821382433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12728171604246636857019821 4773064351592488821382433)
          ·
            refine ⟨3579798263694366616036825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773064351592488821382433 3579798263694366616036825)
            ·
              refine ⟨2684848697770774962027619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579798263694366616036825 2684848697770774962027619)
              ·
                refine ⟨4027273046656162443041429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684848697770774962027619 4027273046656162443041429)
                ·
                  refine ⟨188778424062007614517567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4027273046656162443041429 188778424062007614517567)
                  ·
                    rfl

theorem cell23_3308802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_3308802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308802 prefixEnd_3308802 := by exact prefixLift 3308802
  have htrace : WordTrace (prefixWord ++ tailWord_3308802) baseStart_3308802 baseEnd_3308802 := by
    simpa [prefixWord, tailWord_3308802, baseEnd_3308802] using wordTrace_append hprefix tailTrace_3308802
  have hstable : (prefixWord ++ tailWord_3308802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308802).length < 2 ^ (prefixWord ++ tailWord_3308802).sum := by decide
  have hdescent : baseEnd_3308802 < baseStart_3308802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308835 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 1, 1, 4]
def baseStart_3308835 : Nat := 118140960795 + 3308835 * 2 ^ 59
def prefixEnd_3308835 : Nat := 4983230072969 + 3 ^ 40 * 3308835 * 2
def baseEnd_3308835 : Nat := 1699022761419666901545451

theorem tailTrace_3308835 : CollatzResearch.WordTrace tailWord_3308835 prefixEnd_3308835 1699022761419666901545451 := by
  unfold tailWord_3308835
  simp only [CollatzResearch.WordTrace]
  refine ⟨120683126967663373872879959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80455417978442249248586639 120683126967663373872879959)
  ·
    refine ⟨181024690451495060809319939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120683126967663373872879959 181024690451495060809319939)
    ·
      refine ⟨271537035677242591213979909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181024690451495060809319939 271537035677242591213979909)
      ·
        refine ⟨50913194189482985852621233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271537035677242591213979909 50913194189482985852621233)
        ·
          refine ⟨38184895642112239389465925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50913194189482985852621233 38184895642112239389465925)
          ·
            refine ⟨7159667932896044885524861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38184895642112239389465925 7159667932896044885524861)
            ·
              refine ⟨2684875474836016832071823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7159667932896044885524861 2684875474836016832071823)
              ·
                refine ⟨4027313212254025248107735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684875474836016832071823 4027313212254025248107735)
                ·
                  refine ⟨6040969818381037872161603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027313212254025248107735 6040969818381037872161603)
                  ·
                    refine ⟨9061454727571556808242405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6040969818381037872161603 9061454727571556808242405)
                    ·
                      refine ⟨1699022761419666901545451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9061454727571556808242405 1699022761419666901545451)
                      ·
                        rfl

theorem cell23_3308835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_3308835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308835 prefixEnd_3308835 := by exact prefixLift 3308835
  have htrace : WordTrace (prefixWord ++ tailWord_3308835) baseStart_3308835 baseEnd_3308835 := by
    simpa [prefixWord, tailWord_3308835, baseEnd_3308835] using wordTrace_append hprefix tailTrace_3308835
  have hstable : (prefixWord ++ tailWord_3308835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308835).length < 2 ^ (prefixWord ++ tailWord_3308835).sum := by decide
  have hdescent : baseEnd_3308835 < baseStart_3308835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308852 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_3308852 : Nat := 118140960795 + 3308852 * 2 ^ 59
def prefixEnd_3308852 : Nat := 4983230072969 + 3 ^ 40 * 3308852 * 2
def baseEnd_3308852 : Nat := 1699031490590793335032873

theorem tailTrace_3308852 : CollatzResearch.WordTrace tailWord_3308852 prefixEnd_3308852 1699031490590793335032873 := by
  unfold tailWord_3308852
  simp only [CollatzResearch.WordTrace]
  refine ⟨60341873504300892888124405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80455831339067857184165873 60341873504300892888124405)
  ·
    refine ⟨5657050641028208708261663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60341873504300892888124405 5657050641028208708261663)
    ·
      refine ⟨8485575961542313062392495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5657050641028208708261663 8485575961542313062392495)
      ·
        refine ⟨12728363942313469593588743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8485575961542313062392495 12728363942313469593588743)
        ·
          refine ⟨19092545913470204390383115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12728363942313469593588743 19092545913470204390383115)
          ·
            refine ⟨28638818870205306585574673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19092545913470204390383115 28638818870205306585574673)
            ·
              refine ⟨21479114152653979939181005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28638818870205306585574673 21479114152653979939181005)
              ·
                refine ⟨8054667807245242477192877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21479114152653979939181005 8054667807245242477192877)
                ·
                  refine ⟨3020500427716965928947329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8054667807245242477192877 3020500427716965928947329)
                  ·
                    refine ⟨2265375320787724446710497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3020500427716965928947329 2265375320787724446710497)
                    ·
                      refine ⟨1699031490590793335032873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265375320787724446710497 1699031490590793335032873)
                      ·
                        rfl

theorem cell23_3308852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_3308852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308852 prefixEnd_3308852 := by exact prefixLift 3308852
  have htrace : WordTrace (prefixWord ++ tailWord_3308852) baseStart_3308852 baseEnd_3308852 := by
    simpa [prefixWord, tailWord_3308852, baseEnd_3308852] using wordTrace_append hprefix tailTrace_3308852
  have hstable : (prefixWord ++ tailWord_3308852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308852).length < 2 ^ (prefixWord ++ tailWord_3308852).sum := by decide
  have hdescent : baseEnd_3308852 < baseStart_3308852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308865 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3308865 : Nat := 118140960795 + 3308865 * 2 ^ 59
def prefixEnd_3308865 : Nat := 4983230072969 + 3 ^ 40 * 3308865 * 2
def baseEnd_3308865 : Nat := 1699038165839301784170313

theorem tailTrace_3308865 : CollatzResearch.WordTrace tailWord_3308865 prefixEnd_3308865 1699038165839301784170313 := by
  unfold tailWord_3308865
  simp only [CollatzResearch.WordTrace]
  refine ⟨120684221157554688996472049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80456147438369792664314699 120684221157554688996472049)
  ·
    refine ⟨90513165868166016747354037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120684221157554688996472049 90513165868166016747354037)
    ·
      refine ⟨8485609300140564070064441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90513165868166016747354037 8485609300140564070064441)
      ·
        refine ⟨6364206975105423052548331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8485609300140564070064441 6364206975105423052548331)
        ·
          refine ⟨9546310462658134578822497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364206975105423052548331 9546310462658134578822497)
          ·
            refine ⟨7159732846993600934116873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9546310462658134578822497 7159732846993600934116873)
            ·
              refine ⟨5369799635245200700587655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159732846993600934116873 5369799635245200700587655)
              ·
                refine ⟨8054699452867801050881483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369799635245200700587655 8054699452867801050881483)
                ·
                  refine ⟨12082049179301701576322225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8054699452867801050881483 12082049179301701576322225)
                  ·
                    refine ⟨9061536884476276182241669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12082049179301701576322225 9061536884476276182241669)
                    ·
                      refine ⟨1699038165839301784170313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9061536884476276182241669 1699038165839301784170313)
                      ·
                        rfl

theorem cell23_3308865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3308865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308865 prefixEnd_3308865 := by exact prefixLift 3308865
  have htrace : WordTrace (prefixWord ++ tailWord_3308865) baseStart_3308865 baseEnd_3308865 := by
    simpa [prefixWord, tailWord_3308865, baseEnd_3308865] using wordTrace_append hprefix tailTrace_3308865
  have hstable : (prefixWord ++ tailWord_3308865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308865).length < 2 ^ (prefixWord ++ tailWord_3308865).sum := by decide
  have hdescent : baseEnd_3308865 < baseStart_3308865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308881 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3308881 : Nat := 118140960795 + 3308881 * 2 ^ 59
def prefixEnd_3308881 : Nat := 4983230072969 + 3 ^ 40 * 3308881 * 2
def baseEnd_3308881 : Nat := 1699046381529773721570239

theorem tailTrace_3308881 : CollatzResearch.WordTrace tailWord_3308881 prefixEnd_3308881 1699046381529773721570239 := by
  unfold tailWord_3308881
  simp only [CollatzResearch.WordTrace]
  refine ⟨120684804725496723729054497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80456536483664482486036331 120684804725496723729054497)
  ·
    refine ⟨90513603544122542796790873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120684804725496723729054497 90513603544122542796790873)
    ·
      refine ⟨67885202658091907097593155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90513603544122542796790873 67885202658091907097593155)
      ·
        refine ⟨101827803987137860646389733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67885202658091907097593155 101827803987137860646389733)
        ·
          refine ⟨19092713247588348871198075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101827803987137860646389733 19092713247588348871198075)
          ·
            refine ⟨28639069871382523306797113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19092713247588348871198075 28639069871382523306797113)
            ·
              refine ⟨21479302403536892480097835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28639069871382523306797113 21479302403536892480097835)
              ·
                refine ⟨32218953605305338720146753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21479302403536892480097835 32218953605305338720146753)
                ·
                  refine ⟨24164215203979004040110065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32218953605305338720146753 24164215203979004040110065)
                  ·
                    refine ⟨18123161402984253030082549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24164215203979004040110065 18123161402984253030082549)
                    ·
                      refine ⟨1699046381529773721570239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18123161402984253030082549 1699046381529773721570239)
                      ·
                        rfl

theorem cell23_3308881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3308881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308881 prefixEnd_3308881 := by exact prefixLift 3308881
  have htrace : WordTrace (prefixWord ++ tailWord_3308881) baseStart_3308881 baseEnd_3308881 := by
    simpa [prefixWord, tailWord_3308881, baseEnd_3308881] using wordTrace_append hprefix tailTrace_3308881
  have hstable : (prefixWord ++ tailWord_3308881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308881).length < 2 ^ (prefixWord ++ tailWord_3308881).sum := by decide
  have hdescent : baseEnd_3308881 < baseStart_3308881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308886 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3308886 : Nat := 118140960795 + 3308886 * 2 ^ 59
def prefixEnd_3308886 : Nat := 4983230072969 + 3 ^ 40 * 3308886 * 2
def baseEnd_3308886 : Nat := 1699048948933046202007717

theorem tailTrace_3308886 : CollatzResearch.WordTrace tailWord_3308886 prefixEnd_3308886 1699048948933046202007717 := by
  unfold tailWord_3308886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542811693154913098936657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80456658060319073055324341 7542811693154913098936657)
  ·
    refine ⟨5657108769866184824202493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7542811693154913098936657 5657108769866184824202493)
    ·
      refine ⟨2121415788699819309075935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5657108769866184824202493 2121415788699819309075935)
      ·
        refine ⟨3182123683049728963613903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121415788699819309075935 3182123683049728963613903)
        ·
          refine ⟨4773185524574593445420855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182123683049728963613903 4773185524574593445420855)
          ·
            refine ⟨7159778286861890168131283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773185524574593445420855 7159778286861890168131283)
            ·
              refine ⟨10739667430292835252196925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7159778286861890168131283 10739667430292835252196925)
              ·
                refine ⟨4027375286359813219573847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10739667430292835252196925 4027375286359813219573847)
                ·
                  refine ⟨6041062929539719829360771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027375286359813219573847 6041062929539719829360771)
                  ·
                    refine ⟨9061594394309579744041157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6041062929539719829360771 9061594394309579744041157)
                    ·
                      refine ⟨1699048948933046202007717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9061594394309579744041157 1699048948933046202007717)
                      ·
                        rfl

theorem cell23_3308886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3308886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308886 prefixEnd_3308886 := by exact prefixLift 3308886
  have htrace : WordTrace (prefixWord ++ tailWord_3308886) baseStart_3308886 baseEnd_3308886 := by
    simpa [prefixWord, tailWord_3308886, baseEnd_3308886] using wordTrace_append hprefix tailTrace_3308886
  have hstable : (prefixWord ++ tailWord_3308886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308886).length < 2 ^ (prefixWord ++ tailWord_3308886).sum := by decide
  have hdescent : baseEnd_3308886 < baseStart_3308886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308901 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 4, 6]
def baseStart_3308901 : Nat := 118140960795 + 3308901 * 2 ^ 59
def prefixEnd_3308901 : Nat := 4983230072969 + 3 ^ 40 * 3308901 * 2
def baseEnd_3308901 : Nat := 566352217047621214440049

theorem tailTrace_3308901 : CollatzResearch.WordTrace tailWord_3308901 prefixEnd_3308901 566352217047621214440049 := by
  unfold tailWord_3308901
  simp only [CollatzResearch.WordTrace]
  refine ⟨120685534185424267144782557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80457022790282844763188371 120685534185424267144782557)
  ·
    refine ⟨45257075319534100179293459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120685534185424267144782557 45257075319534100179293459)
    ·
      refine ⟨67885612979301150268940189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45257075319534100179293459 67885612979301150268940189)
      ·
        refine ⟨25457104867237931350852571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67885612979301150268940189 25457104867237931350852571)
        ·
          refine ⟨38185657300856897026278857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25457104867237931350852571 38185657300856897026278857)
          ·
            refine ⟨28639242975642672769709143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38185657300856897026278857 28639242975642672769709143)
            ·
              refine ⟨42958864463464009154563715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28639242975642672769709143 42958864463464009154563715)
              ·
                refine ⟨64438296695196013731845573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42958864463464009154563715 64438296695196013731845573)
                ·
                  refine ⟨12082180630349252574721045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64438296695196013731845573 12082180630349252574721045)
                  ·
                    refine ⟨566352217047621214440049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12082180630349252574721045 566352217047621214440049)
                    ·
                      rfl

theorem cell23_3308901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_3308901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308901 prefixEnd_3308901 := by exact prefixLift 3308901
  have htrace : WordTrace (prefixWord ++ tailWord_3308901) baseStart_3308901 baseEnd_3308901 := by
    simpa [prefixWord, tailWord_3308901, baseEnd_3308901] using wordTrace_append hprefix tailTrace_3308901
  have hstable : (prefixWord ++ tailWord_3308901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308901).length < 2 ^ (prefixWord ++ tailWord_3308901).sum := by decide
  have hdescent : baseEnd_3308901 < baseStart_3308901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308929 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_3308929 : Nat := 118140960795 + 3308929 * 2 ^ 59
def prefixEnd_3308929 : Nat := 4983230072969 + 3 ^ 40 * 3308929 * 2
def baseEnd_3308929 : Nat := 1699071028601189533770019

theorem tailTrace_3308929 : CollatzResearch.WordTrace tailWord_3308929 prefixEnd_3308929 1699071028601189533770019 := by
  unfold tailWord_3308929
  simp only [CollatzResearch.WordTrace]
  refine ⟨120686555429322827926801841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80457703619548551951201227 120686555429322827926801841)
  ·
    refine ⟨90514916571992120945101381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120686555429322827926801841 90514916571992120945101381)
    ·
      refine ⟨16971546857248522677206509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90514916571992120945101381 16971546857248522677206509)
      ·
        refine ⟨6364330071468196003952441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16971546857248522677206509 6364330071468196003952441)
        ·
          refine ⟨4773247553601147002964331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6364330071468196003952441 4773247553601147002964331)
          ·
            refine ⟨7159871330401720504446497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773247553601147002964331 7159871330401720504446497)
            ·
              refine ⟨5369903497801290378334873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159871330401720504446497 5369903497801290378334873)
              ·
                refine ⟨4027427623350967783751155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369903497801290378334873 4027427623350967783751155)
                ·
                  refine ⟨6041141435026451675626733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027427623350967783751155 6041141435026451675626733)
                  ·
                    refine ⟨2265428038134919378360025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6041141435026451675626733 2265428038134919378360025)
                    ·
                      refine ⟨1699071028601189533770019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265428038134919378360025 1699071028601189533770019)
                      ·
                        rfl

theorem cell23_3308929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_3308929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308929 prefixEnd_3308929 := by exact prefixLift 3308929
  have htrace : WordTrace (prefixWord ++ tailWord_3308929) baseStart_3308929 baseEnd_3308929 := by
    simpa [prefixWord, tailWord_3308929, baseEnd_3308929] using wordTrace_append hprefix tailTrace_3308929
  have hstable : (prefixWord ++ tailWord_3308929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308929).length < 2 ^ (prefixWord ++ tailWord_3308929).sum := by decide
  have hdescent : baseEnd_3308929 < baseStart_3308929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3308991 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 2, 8]
def baseStart_3308991 : Nat := 118140960795 + 3308991 * 2 ^ 59
def prefixEnd_3308991 : Nat := 4983230072969 + 3 ^ 40 * 3308991 * 2
def baseEnd_3308991 : Nat := 566367621467256097064911

theorem tailTrace_3308991 : CollatzResearch.WordTrace tailWord_3308991 prefixEnd_3308991 566367621467256097064911 := by
  unfold tailWord_3308991
  simp only [CollatzResearch.WordTrace]
  refine ⟨120688816755098212515558827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80459211170065475010372551 120688816755098212515558827)
  ·
    refine ⟨181033225132647318773338241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120688816755098212515558827 181033225132647318773338241)
    ·
      refine ⟨135774918849485489080003681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181033225132647318773338241 135774918849485489080003681)
      ·
        refine ⟨101831189137114116810002761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135774918849485489080003681 101831189137114116810002761)
        ·
          refine ⟨76373391852835587607502071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101831189137114116810002761 76373391852835587607502071)
          ·
            refine ⟨114560087779253381411253107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76373391852835587607502071 114560087779253381411253107)
            ·
              refine ⟨171840131668880072116879661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114560087779253381411253107 171840131668880072116879661)
              ·
                refine ⟨64440049375830027043829873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171840131668880072116879661 64440049375830027043829873)
                ·
                  refine ⟨48330037031872520282872405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64440049375830027043829873 48330037031872520282872405)
                  ·
                    refine ⟨566367621467256097064911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48330037031872520282872405 566367621467256097064911)
                    ·
                      rfl

theorem cell23_3308991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_3308991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3308991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3308991 prefixEnd_3308991 := by exact prefixLift 3308991
  have htrace : WordTrace (prefixWord ++ tailWord_3308991) baseStart_3308991 baseEnd_3308991 := by
    simpa [prefixWord, tailWord_3308991, baseEnd_3308991] using wordTrace_append hprefix tailTrace_3308991
  have hstable : (prefixWord ++ tailWord_3308991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3308991).length < 2 ^ (prefixWord ++ tailWord_3308991).sum := by decide
  have hdescent : baseEnd_3308991 < baseStart_3308991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3308991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309008 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 5, 4]
def baseStart_3309008 : Nat := 118140960795 + 3309008 * 2 ^ 59
def prefixEnd_3309008 : Nat := 4983230072969 + 3 ^ 40 * 3309008 * 2
def baseEnd_3309008 : Nat := 566370531190964908227385

theorem tailTrace_3309008 : CollatzResearch.WordTrace tailWord_3309008 prefixEnd_3309008 566370531190964908227385 := by
  unfold tailWord_3309008
  simp only [CollatzResearch.WordTrace]
  refine ⟨60344718398018312209463839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80459624530691082945951785 60344718398018312209463839)
  ·
    refine ⟨90517077597027468314195759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60344718398018312209463839 90517077597027468314195759)
    ·
      refine ⟨135775616395541202471293639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90517077597027468314195759 135775616395541202471293639)
      ·
        refine ⟨203663424593311803706940459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135775616395541202471293639 203663424593311803706940459)
        ·
          refine ⟨305495136889967705560410689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203663424593311803706940459 305495136889967705560410689)
          ·
            refine ⟨229121352667475779170308017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305495136889967705560410689 229121352667475779170308017)
            ·
              refine ⟨171841014500606834377731013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229121352667475779170308017 171841014500606834377731013)
              ·
                refine ⟨32220190218863781445824565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171841014500606834377731013 32220190218863781445824565)
                ·
                  refine ⟨3020642833018479510546053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32220190218863781445824565 3020642833018479510546053)
                  ·
                    refine ⟨566370531190964908227385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020642833018479510546053 566370531190964908227385)
                    ·
                      rfl

theorem cell23_3309008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_3309008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309008 prefixEnd_3309008 := by exact prefixLift 3309008
  have htrace : WordTrace (prefixWord ++ tailWord_3309008) baseStart_3309008 baseEnd_3309008 := by
    simpa [prefixWord, tailWord_3309008, baseEnd_3309008] using wordTrace_append hprefix tailTrace_3309008
  have hstable : (prefixWord ++ tailWord_3309008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309008).length < 2 ^ (prefixWord ++ tailWord_3309008).sum := by decide
  have hdescent : baseEnd_3309008 < baseStart_3309008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309042 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3309042 : Nat := 118140960795 + 3309042 * 2 ^ 59
def prefixEnd_3309042 : Nat := 4983230072969 + 3 ^ 40 * 3309042 * 2
def baseEnd_3309042 : Nat := 566376350638382530552333

theorem tailTrace_3309042 : CollatzResearch.WordTrace tailWord_3309042 prefixEnd_3309042 566376350638382530552333 := by
  unfold tailWord_3309042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30172669219478362056416345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80460451251942298817110253 30172669219478362056416345)
  ·
    refine ⟨22629501914608771542312259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30172669219478362056416345 22629501914608771542312259)
    ·
      refine ⟨33944252871913157313468389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22629501914608771542312259 33944252871913157313468389)
      ·
        refine ⟨6364547413483716996275323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33944252871913157313468389 6364547413483716996275323)
        ·
          refine ⟨9546821120225575494412985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364547413483716996275323 9546821120225575494412985)
          ·
            refine ⟨7160115840169181620809739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9546821120225575494412985 7160115840169181620809739)
            ·
              refine ⟨10740173760253772431214609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160115840169181620809739 10740173760253772431214609)
              ·
                refine ⟨8055130320190329323410957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10740173760253772431214609 8055130320190329323410957)
                ·
                  refine ⟨3020673870071373496279109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8055130320190329323410957 3020673870071373496279109)
                  ·
                    refine ⟨566376350638382530552333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020673870071373496279109 566376350638382530552333)
                    ·
                      rfl

theorem cell23_3309042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3309042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309042 prefixEnd_3309042 := by exact prefixLift 3309042
  have htrace : WordTrace (prefixWord ++ tailWord_3309042) baseStart_3309042 baseEnd_3309042 := by
    simpa [prefixWord, tailWord_3309042, baseEnd_3309042] using wordTrace_append hprefix tailTrace_3309042
  have hstable : (prefixWord ++ tailWord_3309042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309042).length < 2 ^ (prefixWord ++ tailWord_3309042).sum := by decide
  have hdescent : baseEnd_3309042 < baseStart_3309042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309065 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 3]
def baseStart_3309065 : Nat := 118140960795 + 3309065 * 2 ^ 59
def prefixEnd_3309065 : Nat := 4983230072969 + 3 ^ 40 * 3309065 * 2
def baseEnd_3309065 : Nat := 1699140861970201001669393

theorem tailTrace_3309065 : CollatzResearch.WordTrace tailWord_3309065 prefixEnd_3309065 1699140861970201001669393 := by
  unfold tailWord_3309065
  simp only [CollatzResearch.WordTrace]
  refine ⟨120691515756830123153752649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80461010504553415435835099 120691515756830123153752649)
  ·
    refine ⟨90518636817622592365314487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120691515756830123153752649 90518636817622592365314487)
    ·
      refine ⟨135777955226433888547971731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90518636817622592365314487 135777955226433888547971731)
      ·
        refine ⟨203666932839650832821957597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135777955226433888547971731 203666932839650832821957597)
        ·
          refine ⟨76375099814869062308234099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203666932839650832821957597 76375099814869062308234099)
          ·
            refine ⟨114562649722303593462351149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76375099814869062308234099 114562649722303593462351149)
            ·
              refine ⟨42960993645863847548381681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114562649722303593462351149 42960993645863847548381681)
              ·
                refine ⟨32220745234397885661286261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42960993645863847548381681 32220745234397885661286261)
                ·
                  refine ⟨3020694865724801780745587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32220745234397885661286261 3020694865724801780745587)
                  ·
                    refine ⟨4531042298587202671118381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3020694865724801780745587 4531042298587202671118381)
                    ·
                      refine ⟨1699140861970201001669393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531042298587202671118381 1699140861970201001669393)
                      ·
                        rfl

theorem cell23_3309065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 1, 3].length) (baseStart_3309065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309065 prefixEnd_3309065 := by exact prefixLift 3309065
  have htrace : WordTrace (prefixWord ++ tailWord_3309065) baseStart_3309065 baseEnd_3309065 := by
    simpa [prefixWord, tailWord_3309065, baseEnd_3309065] using wordTrace_append hprefix tailTrace_3309065
  have hstable : (prefixWord ++ tailWord_3309065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309065).length < 2 ^ (prefixWord ++ tailWord_3309065).sum := by decide
  have hdescent : baseEnd_3309065 < baseStart_3309065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309102 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3309102 : Nat := 118140960795 + 3309102 * 2 ^ 59
def prefixEnd_3309102 : Nat := 4983230072969 + 3 ^ 40 * 3309102 * 2
def baseEnd_3309102 : Nat := 566386620251472452302241

theorem tailTrace_3309102 : CollatzResearch.WordTrace tailWord_3309102 prefixEnd_3309102 566386620251472452302241 := by
  unfold tailWord_3309102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15086608157212009809106195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80461910171797385648566373 15086608157212009809106195)
  ·
    refine ⟨22629912235818014713659293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15086608157212009809106195 22629912235818014713659293)
    ·
      refine ⟨8486217088431755517622235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22629912235818014713659293 8486217088431755517622235)
      ·
        refine ⟨12729325632647633276433353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8486217088431755517622235 12729325632647633276433353)
        ·
          refine ⟨9546994224485724957325015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12729325632647633276433353 9546994224485724957325015)
          ·
            refine ⟨14320491336728587435987523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9546994224485724957325015 14320491336728587435987523)
            ·
              refine ⟨21480737005092881153981285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14320491336728587435987523 21480737005092881153981285)
              ·
                refine ⟨4027638188454915216371491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21480737005092881153981285 4027638188454915216371491)
                ·
                  refine ⟨6041457282682372824557237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027638188454915216371491 6041457282682372824557237)
                  ·
                    refine ⟨566386620251472452302241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6041457282682372824557237 566386620251472452302241)
                    ·
                      rfl

theorem cell23_3309102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3309102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309102 prefixEnd_3309102 := by exact prefixLift 3309102
  have htrace : WordTrace (prefixWord ++ tailWord_3309102) baseStart_3309102 baseEnd_3309102 := by
    simpa [prefixWord, tailWord_3309102, baseEnd_3309102] using wordTrace_append hprefix tailTrace_3309102
  have hstable : (prefixWord ++ tailWord_3309102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309102).length < 2 ^ (prefixWord ++ tailWord_3309102).sum := by decide
  have hdescent : baseEnd_3309102 < baseStart_3309102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309105 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 8, 2]
def baseStart_3309105 : Nat := 118140960795 + 3309105 * 2 ^ 59
def prefixEnd_3309105 : Nat := 4983230072969 + 3 ^ 40 * 3309105 * 2
def baseEnd_3309105 : Nat := 1699161401196380845169209

theorem tailTrace_3309105 : CollatzResearch.WordTrace tailWord_3309105 prefixEnd_3309105 1699161401196380845169209 := by
  unfold tailWord_3309105
  simp only [CollatzResearch.WordTrace]
  refine ⟨120692974676685209985208769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80461983117790139990139179 120692974676685209985208769)
  ·
    refine ⟨90519731007513907488906577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120692974676685209985208769 90519731007513907488906577)
    ·
      refine ⟨67889798255635430616679933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90519731007513907488906577 67889798255635430616679933)
      ·
        refine ⟨25458674345863286481254975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67889798255635430616679933 25458674345863286481254975)
        ·
          refine ⟨38188011518794929721882463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25458674345863286481254975 38188011518794929721882463)
          ·
            refine ⟨57282017278192394582823695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38188011518794929721882463 57282017278192394582823695)
            ·
              refine ⟨85923025917288591874235543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57282017278192394582823695 85923025917288591874235543)
              ·
                refine ⟨128884538875932887811353315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85923025917288591874235543 128884538875932887811353315)
                ·
                  refine ⟨193326808313899331717029973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128884538875932887811353315 193326808313899331717029973)
                  ·
                    refine ⟨2265548534928507793558945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 193326808313899331717029973 2265548534928507793558945)
                    ·
                      refine ⟨1699161401196380845169209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265548534928507793558945 1699161401196380845169209)
                      ·
                        rfl

theorem cell23_3309105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_3309105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309105 prefixEnd_3309105 := by exact prefixLift 3309105
  have htrace : WordTrace (prefixWord ++ tailWord_3309105) baseStart_3309105 baseEnd_3309105 := by
    simpa [prefixWord, tailWord_3309105, baseEnd_3309105] using wordTrace_append hprefix tailTrace_3309105
  have hstable : (prefixWord ++ tailWord_3309105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309105).length < 2 ^ (prefixWord ++ tailWord_3309105).sum := by decide
  have hdescent : baseEnd_3309105 < baseStart_3309105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309125 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_3309125 : Nat := 118140960795 + 3309125 * 2 ^ 59
def prefixEnd_3309125 : Nat := 4983230072969 + 3 ^ 40 * 3309125 * 2
def baseEnd_3309125 : Nat := 1699171670809470766919117

theorem tailTrace_3309125 : CollatzResearch.WordTrace tailWord_3309125 prefixEnd_3309125 1699171670809470766919117 := by
  unfold tailWord_3309125
  simp only [CollatzResearch.WordTrace]
  refine ⟨120693704136612753400936829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80462469424408502267291219 120693704136612753400936829)
  ·
    refine ⟨45260139051229782525351311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120693704136612753400936829 45260139051229782525351311)
    ·
      refine ⟨67890208576844673788026967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45260139051229782525351311 67890208576844673788026967)
      ·
        refine ⟨101835312865267010682040451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67890208576844673788026967 101835312865267010682040451)
        ·
          refine ⟨152752969297900516023060677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101835312865267010682040451 152752969297900516023060677)
          ·
            refine ⟨28641181743356346754323877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152752969297900516023060677 28641181743356346754323877)
            ·
              refine ⟨5370221576879315016435727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28641181743356346754323877 5370221576879315016435727)
              ·
                refine ⟨8055332365318972524653591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370221576879315016435727 8055332365318972524653591)
                ·
                  refine ⟨12082998547978458786980387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8055332365318972524653591 12082998547978458786980387)
                  ·
                    refine ⟨18124497821967688180470581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12082998547978458786980387 18124497821967688180470581)
                    ·
                      refine ⟨1699171670809470766919117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18124497821967688180470581 1699171670809470766919117)
                      ·
                        rfl

theorem cell23_3309125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_3309125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309125 prefixEnd_3309125 := by exact prefixLift 3309125
  have htrace : WordTrace (prefixWord ++ tailWord_3309125) baseStart_3309125 baseEnd_3309125 := by
    simpa [prefixWord, tailWord_3309125, baseEnd_3309125] using wordTrace_append hprefix tailTrace_3309125
  have hstable : (prefixWord ++ tailWord_3309125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309125).length < 2 ^ (prefixWord ++ tailWord_3309125).sum := by decide
  have hdescent : baseEnd_3309125 < baseStart_3309125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309133 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_3309133 : Nat := 118140960795 + 3309133 * 2 ^ 59
def prefixEnd_3309133 : Nat := 4983230072969 + 3 ^ 40 * 3309133 * 2
def baseEnd_3309133 : Nat := 1699175778654706735619081

theorem tailTrace_3309133 : CollatzResearch.WordTrace tailWord_3309133 prefixEnd_3309133 1699175778654706735619081 := by
  unfold tailWord_3309133
  simp only [CollatzResearch.WordTrace]
  refine ⟨120693995920583770767228053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80462663947055847178152035 120693995920583770767228053)
  ·
    refine ⟨5657531058777364254713815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120693995920583770767228053 5657531058777364254713815)
    ·
      refine ⟨8486296588166046382070723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5657531058777364254713815 8486296588166046382070723)
      ·
        refine ⟨12729444882249069573106085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8486296588166046382070723 12729444882249069573106085)
        ·
          refine ⟨2386770915421700544957391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12729444882249069573106085 2386770915421700544957391)
          ·
            refine ⟨3580156373132550817436087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386770915421700544957391 3580156373132550817436087)
            ·
              refine ⟨5370234559698826226154131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580156373132550817436087 5370234559698826226154131)
              ·
                refine ⟨8055351839548239339231197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370234559698826226154131 8055351839548239339231197)
                ·
                  refine ⟨3020756939830589752211699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8055351839548239339231197 3020756939830589752211699)
                  ·
                    refine ⟨4531135409745884628317549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3020756939830589752211699 4531135409745884628317549)
                    ·
                      refine ⟨1699175778654706735619081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531135409745884628317549 1699175778654706735619081)
                      ·
                        rfl

theorem cell23_3309133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_3309133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309133 prefixEnd_3309133 := by exact prefixLift 3309133
  have htrace : WordTrace (prefixWord ++ tailWord_3309133) baseStart_3309133 baseEnd_3309133 := by
    simpa [prefixWord, tailWord_3309133, baseEnd_3309133] using wordTrace_append hprefix tailTrace_3309133
  have hstable : (prefixWord ++ tailWord_3309133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309133).length < 2 ^ (prefixWord ++ tailWord_3309133).sum := by decide
  have hdescent : baseEnd_3309133 < baseStart_3309133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309189 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_3309189 : Nat := 118140960795 + 3309189 * 2 ^ 59
def prefixEnd_3309189 : Nat := 4983230072969 + 3 ^ 40 * 3309189 * 2
def baseEnd_3309189 : Nat := 1699204533571358516518823

theorem tailTrace_3309189 : CollatzResearch.WordTrace tailWord_3309189 prefixEnd_3309189 1699204533571358516518823 := by
  unfold tailWord_3309189
  simp only [CollatzResearch.WordTrace]
  refine ⟨120696038408380892331266621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80464025605587261554177747 120696038408380892331266621)
  ·
    refine ⟨45261014403142834624224983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120696038408380892331266621 45261014403142834624224983)
    ·
      refine ⟨67891521604714251936337475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45261014403142834624224983 67891521604714251936337475)
      ·
        refine ⟨101837282407071377904506213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67891521604714251936337475 101837282407071377904506213)
        ·
          refine ⟨19094490451325883357094915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101837282407071377904506213 19094490451325883357094915)
          ·
            refine ⟨28641735676988825035642373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19094490451325883357094915 28641735676988825035642373)
            ·
              refine ⟨5370325439435404694182945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28641735676988825035642373 5370325439435404694182945)
              ·
                refine ⟨4027744079576553520637209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5370325439435404694182945 4027744079576553520637209)
                ·
                  refine ⟨3020808059682415140477907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4027744079576553520637209 3020808059682415140477907)
                  ·
                    refine ⟨4531212089523622710716861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3020808059682415140477907 4531212089523622710716861)
                    ·
                      refine ⟨1699204533571358516518823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531212089523622710716861 1699204533571358516518823)
                      ·
                        rfl

theorem cell23_3309189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_3309189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309189 prefixEnd_3309189 := by exact prefixLift 3309189
  have htrace : WordTrace (prefixWord ++ tailWord_3309189) baseStart_3309189 baseEnd_3309189 := by
    simpa [prefixWord, tailWord_3309189, baseEnd_3309189] using wordTrace_append hprefix tailTrace_3309189
  have hstable : (prefixWord ++ tailWord_3309189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309189).length < 2 ^ (prefixWord ++ tailWord_3309189).sum := by decide
  have hdescent : baseEnd_3309189 < baseStart_3309189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309229 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_3309229 : Nat := 118140960795 + 3309229 * 2 ^ 59
def prefixEnd_3309229 : Nat := 4983230072969 + 3 ^ 40 * 3309229 * 2
def baseEnd_3309229 : Nat := 1699225072797538360018639

theorem tailTrace_3309229 : CollatzResearch.WordTrace tailWord_3309229 prefixEnd_3309229 1699225072797538360018639 := by
  unfold tailWord_3309229
  simp only [CollatzResearch.WordTrace]
  refine ⟨120697497328235979162722741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80464998218823986108481827 120697497328235979162722741)
  ·
    refine ⟨11315390374522123046505257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120697497328235979162722741 11315390374522123046505257)
    ·
      refine ⟨8486542780891592284878943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11315390374522123046505257 8486542780891592284878943)
      ·
        refine ⟨12729814171337388427318415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8486542780891592284878943 12729814171337388427318415)
        ·
          refine ⟨19094721257006082640977623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12729814171337388427318415 19094721257006082640977623)
          ·
            refine ⟨28642081885509123961466435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19094721257006082640977623 28642081885509123961466435)
            ·
              refine ⟨42963122828263685942199653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28642081885509123961466435 42963122828263685942199653)
              ·
                refine ⟨8055585530299441114162435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42963122828263685942199653 8055585530299441114162435)
                ·
                  refine ⟨12083378295449161671243653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8055585530299441114162435 12083378295449161671243653)
                  ·
                    refine ⟨2265633430396717813358185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12083378295449161671243653 2265633430396717813358185)
                    ·
                      refine ⟨1699225072797538360018639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265633430396717813358185 1699225072797538360018639)
                      ·
                        rfl

theorem cell23_3309229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_3309229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309229 prefixEnd_3309229 := by exact prefixLift 3309229
  have htrace : WordTrace (prefixWord ++ tailWord_3309229) baseStart_3309229 baseEnd_3309229 := by
    simpa [prefixWord, tailWord_3309229, baseEnd_3309229] using wordTrace_append hprefix tailTrace_3309229
  have hstable : (prefixWord ++ tailWord_3309229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309229).length < 2 ^ (prefixWord ++ tailWord_3309229).sum := by decide
  have hdescent : baseEnd_3309229 < baseStart_3309229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309246 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_3309246 : Nat := 118140960795 + 3309246 * 2 ^ 59
def prefixEnd_3309246 : Nat := 4983230072969 + 3 ^ 40 * 3309246 * 2
def baseEnd_3309246 : Nat := 1699233801968664793506061

theorem tailTrace_3309246 : CollatzResearch.WordTrace tailWord_3309246 prefixEnd_3309246 1699233801968664793506061 := by
  unfold tailWord_3309246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087264671146798883261449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80465411579449594044061061 15087264671146798883261449)
  ·
    refine ⟨11315448503360099162446087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15087264671146798883261449 11315448503360099162446087)
    ·
      refine ⟨16973172755040148743669131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315448503360099162446087 16973172755040148743669131)
      ·
        refine ⟨25459759132560223115503697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16973172755040148743669131 25459759132560223115503697)
        ·
          refine ⟨19094819349420167336627773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25459759132560223115503697 19094819349420167336627773)
          ·
            refine ⟨7160557256032562751235415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19094819349420167336627773 7160557256032562751235415)
            ·
              refine ⟨10740835884048844126853123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160557256032562751235415 10740835884048844126853123)
              ·
                refine ⟨16111253826073266190279685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10740835884048844126853123 16111253826073266190279685)
                ·
                  refine ⟨3020860092388737410677441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16111253826073266190279685 3020860092388737410677441)
                  ·
                    refine ⟨2265645069291553058008081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3020860092388737410677441 2265645069291553058008081)
                    ·
                      refine ⟨1699233801968664793506061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265645069291553058008081 1699233801968664793506061)
                      ·
                        rfl

theorem cell23_3309246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_3309246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309246 prefixEnd_3309246 := by exact prefixLift 3309246
  have htrace : WordTrace (prefixWord ++ tailWord_3309246) baseStart_3309246 baseEnd_3309246 := by
    simpa [prefixWord, tailWord_3309246, baseEnd_3309246] using wordTrace_append hprefix tailTrace_3309246
  have hstable : (prefixWord ++ tailWord_3309246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309246).length < 2 ^ (prefixWord ++ tailWord_3309246).sum := by decide
  have hdescent : baseEnd_3309246 < baseStart_3309246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309252 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 7]
def baseStart_3309252 : Nat := 118140960795 + 3309252 * 2 ^ 59
def prefixEnd_3309252 : Nat := 4983230072969 + 3 ^ 40 * 3309252 * 2
def baseEnd_3309252 : Nat := 188804098094732418892337

theorem tailTrace_3309252 : CollatzResearch.WordTrace tailWord_3309252 prefixEnd_3309252 188804098094732418892337 := by
  unfold tailWord_3309252
  simp only [CollatzResearch.WordTrace]
  refine ⟨60349168103576327045405005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80465557471435102727206673 60349168103576327045405005)
  ·
    refine ⟨22630938038841122642026877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60349168103576327045405005 22630938038841122642026877)
    ·
      refine ⟨8486601764565420990760079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22630938038841122642026877 8486601764565420990760079)
      ·
        refine ⟨12729902646848131486140119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8486601764565420990760079 12729902646848131486140119)
        ·
          refine ⟨19094853970272197229210179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12729902646848131486140119 19094853970272197229210179)
          ·
            refine ⟨28642280955408295843815269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19094853970272197229210179 28642280955408295843815269)
            ·
              refine ⟨5370427679139055470715363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28642280955408295843815269 5370427679139055470715363)
              ·
                refine ⟨8055641518708583206073045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370427679139055470715363 8055641518708583206073045)
                ·
                  refine ⟨188804098094732418892337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8055641518708583206073045 188804098094732418892337)
                  ·
                    rfl

theorem cell23_3309252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_3309252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309252 prefixEnd_3309252 := by exact prefixLift 3309252
  have htrace : WordTrace (prefixWord ++ tailWord_3309252) baseStart_3309252 baseEnd_3309252 := by
    simpa [prefixWord, tailWord_3309252, baseEnd_3309252] using wordTrace_append hprefix tailTrace_3309252
  have hstable : (prefixWord ++ tailWord_3309252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309252).length < 2 ^ (prefixWord ++ tailWord_3309252).sum := by decide
  have hdescent : baseEnd_3309252 < baseStart_3309252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309262 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3309262 : Nat := 118140960795 + 3309262 * 2 ^ 59
def prefixEnd_3309262 : Nat := 4983230072969 + 3 ^ 40 * 3309262 * 2
def baseEnd_3309262 : Nat := 1699242017659136730905987

theorem tailTrace_3309262 : CollatzResearch.WordTrace tailWord_3309262 prefixEnd_3309262 1699242017659136730905987 := by
  unfold tailWord_3309262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087337617139553224834255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80465800624744283865782693 15087337617139553224834255)
  ·
    refine ⟨22631006425709329837251383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15087337617139553224834255 22631006425709329837251383)
    ·
      refine ⟨33946509638563994755877075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22631006425709329837251383 33946509638563994755877075)
      ·
        refine ⟨50919764457845992133815613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33946509638563994755877075 50919764457845992133815613)
        ·
          refine ⟨19094911671692247050180855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50919764457845992133815613 19094911671692247050180855)
          ·
            refine ⟨28642367507538370575271283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19094911671692247050180855 28642367507538370575271283)
            ·
              refine ⟨42963551261307555862906925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28642367507538370575271283 42963551261307555862906925)
              ·
                refine ⟨16111331722990333448590097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42963551261307555862906925 16111331722990333448590097)
                ·
                  refine ⟨12083498792242750086442573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16111331722990333448590097 12083498792242750086442573)
                  ·
                    refine ⟨4531312047091031282415965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12083498792242750086442573 4531312047091031282415965)
                    ·
                      refine ⟨1699242017659136730905987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531312047091031282415965 1699242017659136730905987)
                      ·
                        rfl

theorem cell23_3309262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3309262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309262 prefixEnd_3309262 := by exact prefixLift 3309262
  have htrace : WordTrace (prefixWord ++ tailWord_3309262) baseStart_3309262 baseEnd_3309262 := by
    simpa [prefixWord, tailWord_3309262, baseEnd_3309262] using wordTrace_append hprefix tailTrace_3309262
  have hstable : (prefixWord ++ tailWord_3309262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309262).length < 2 ^ (prefixWord ++ tailWord_3309262).sum := by decide
  have hdescent : baseEnd_3309262 < baseStart_3309262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309265 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 1, 7]
def baseStart_3309265 : Nat := 118140960795 + 3309265 * 2 ^ 59
def prefixEnd_3309265 : Nat := 4983230072969 + 3 ^ 40 * 3309265 * 2
def baseEnd_3309265 : Nat := 566414519367033406389491

theorem tailTrace_3309265 : CollatzResearch.WordTrace tailWord_3309265 prefixEnd_3309265 566414519367033406389491 := by
  unfold tailWord_3309265
  simp only [CollatzResearch.WordTrace]
  refine ⟨120698810356105557311033249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80465873570737038207355499 120698810356105557311033249)
  ·
    refine ⟨90524107767079167983274937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120698810356105557311033249 90524107767079167983274937)
    ·
      refine ⟨67893080825309375987456203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90524107767079167983274937 67893080825309375987456203)
      ·
        refine ⟨101839621237964063981184305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67893080825309375987456203 101839621237964063981184305)
        ·
          refine ⟨76379715928473047985888229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101839621237964063981184305 76379715928473047985888229)
          ·
            refine ⟨14321196736588696497354043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76379715928473047985888229 14321196736588696497354043)
            ·
              refine ⟨21481795104883044746031065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14321196736588696497354043 21481795104883044746031065)
              ·
                refine ⟨16111346328662283559523299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21481795104883044746031065 16111346328662283559523299)
                ·
                  refine ⟨24167019492993425339284949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16111346328662283559523299 24167019492993425339284949)
                  ·
                    refine ⟨566414519367033406389491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24167019492993425339284949 566414519367033406389491)
                    ·
                      rfl

theorem cell23_3309265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_3309265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309265 prefixEnd_3309265 := by exact prefixLift 3309265
  have htrace : WordTrace (prefixWord ++ tailWord_3309265) baseStart_3309265 baseEnd_3309265 := by
    simpa [prefixWord, tailWord_3309265, baseEnd_3309265] using wordTrace_append hprefix tailTrace_3309265
  have hstable : (prefixWord ++ tailWord_3309265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309265).length < 2 ^ (prefixWord ++ tailWord_3309265).sum := by decide
  have hdescent : baseEnd_3309265 < baseStart_3309265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309315 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6]
def baseStart_3309315 : Nat := 118140960795 + 3309315 * 2 ^ 59
def prefixEnd_3309315 : Nat := 4983230072969 + 3 ^ 40 * 3309315 * 2
def baseEnd_3309315 : Nat := 1699269232133825023543243

theorem tailTrace_3309315 : CollatzResearch.WordTrace tailWord_3309315 prefixEnd_3309315 1699269232133825023543243 := by
  unfold tailWord_3309315
  simp only [CollatzResearch.WordTrace]
  refine ⟨120700634005924415850353399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80467089337282943900235599 120700634005924415850353399)
  ·
    refine ⟨181050951008886623775530099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120700634005924415850353399 181050951008886623775530099)
    ·
      refine ⟨271576426513329935663295149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181050951008886623775530099 271576426513329935663295149)
      ·
        refine ⟨101841159942498725873735681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271576426513329935663295149 101841159942498725873735681)
        ·
          refine ⟨76380869956874044405301761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101841159942498725873735681 76380869956874044405301761)
          ·
            refine ⟨57285652467655533303976321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76380869956874044405301761 57285652467655533303976321)
            ·
              refine ⟨42964239350741649977982241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57285652467655533303976321 42964239350741649977982241)
              ·
                refine ⟨32223179513056237483486681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42964239350741649977982241 32223179513056237483486681)
                ·
                  refine ⟨24167384634792178112615011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32223179513056237483486681 24167384634792178112615011)
                  ·
                    refine ⟨36251076952188267168922517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24167384634792178112615011 36251076952188267168922517)
                    ·
                      refine ⟨1699269232133825023543243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36251076952188267168922517 1699269232133825023543243)
                      ·
                        rfl

theorem cell23_3309315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_3309315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309315 prefixEnd_3309315 := by exact prefixLift 3309315
  have htrace : WordTrace (prefixWord ++ tailWord_3309315) baseStart_3309315 baseEnd_3309315 := by
    simpa [prefixWord, tailWord_3309315, baseEnd_3309315] using wordTrace_append hprefix tailTrace_3309315
  have hstable : (prefixWord ++ tailWord_3309315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309315).length < 2 ^ (prefixWord ++ tailWord_3309315).sum := by decide
  have hdescent : baseEnd_3309315 < baseStart_3309315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309346 : List Nat := [3, 3, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3309346 : Nat := 118140960795 + 3309346 * 2 ^ 59
def prefixEnd_3309346 : Nat := 4983230072969 + 3 ^ 40 * 3309346 * 2
def baseEnd_3309346 : Nat := 566428383344704800751867

theorem tailTrace_3309346 : CollatzResearch.WordTrace tailWord_3309346 prefixEnd_3309346 566428383344704800751867 := by
  unfold tailWord_3309346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30175441167203027036182973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80467843112541405429821261 30175441167203027036182973)
  ·
    refine ⟨11315790437701135138568615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30175441167203027036182973 11315790437701135138568615)
    ·
      refine ⟨16973685656551702707852923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315790437701135138568615 16973685656551702707852923)
      ·
        refine ⟨25460528484827554061779385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16973685656551702707852923 25460528484827554061779385)
        ·
          refine ⟨19095396363620665546334539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25460528484827554061779385 19095396363620665546334539)
          ·
            refine ⟨28643094545430998319501809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19095396363620665546334539 28643094545430998319501809)
            ·
              refine ⟨21482320909073248739626357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28643094545430998319501809 21482320909073248739626357)
              ·
                refine ⟨2013967585225617069339971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21482320909073248739626357 2013967585225617069339971)
                ·
                  refine ⟨3020951377838425604009957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013967585225617069339971 3020951377838425604009957)
                  ·
                    refine ⟨566428383344704800751867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020951377838425604009957 566428383344704800751867)
                    ·
                      rfl

theorem cell23_3309346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3309346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309346 prefixEnd_3309346 := by exact prefixLift 3309346
  have htrace : WordTrace (prefixWord ++ tailWord_3309346) baseStart_3309346 baseEnd_3309346 := by
    simpa [prefixWord, tailWord_3309346, baseEnd_3309346] using wordTrace_append hprefix tailTrace_3309346
  have hstable : (prefixWord ++ tailWord_3309346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309346).length < 2 ^ (prefixWord ++ tailWord_3309346).sum := by decide
  have hdescent : baseEnd_3309346 < baseStart_3309346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309372 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_3309372 : Nat := 118140960795 + 3309372 * 2 ^ 59
def prefixEnd_3309372 : Nat := 4983230072969 + 3 ^ 40 * 3309372 * 2
def baseEnd_3309372 : Nat := 566432833510377100176827

theorem tailTrace_3309372 : CollatzResearch.WordTrace tailWord_3309372 prefixEnd_3309372 566432833510377100176827 := by
  unfold tailWord_3309372
  simp only [CollatzResearch.WordTrace]
  refine ⟨60351356483358957292589185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80468475311145276390118913 60351356483358957292589185)
  ·
    refine ⟨45263517362519217969441889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60351356483358957292589185 45263517362519217969441889)
    ·
      refine ⟨33947638021889413477081417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45263517362519217969441889 33947638021889413477081417)
      ·
        refine ⟨25460728516417060107811063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33947638021889413477081417 25460728516417060107811063)
        ·
          refine ⟨38191092774625590161716595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25460728516417060107811063 38191092774625590161716595)
          ·
            refine ⟨57286639161938385242574893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38191092774625590161716595 57286639161938385242574893)
            ·
              refine ⟨21482489685726894465965585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57286639161938385242574893 21482489685726894465965585)
              ·
                refine ⟨16111867264295170849474189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21482489685726894465965585 16111867264295170849474189)
                ·
                  refine ⟨6041950224110689068552821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16111867264295170849474189 6041950224110689068552821)
                  ·
                    refine ⟨566432833510377100176827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6041950224110689068552821 566432833510377100176827)
                    ·
                      rfl

theorem cell23_3309372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_3309372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309372 prefixEnd_3309372 := by exact prefixLift 3309372
  have htrace : WordTrace (prefixWord ++ tailWord_3309372) baseStart_3309372 baseEnd_3309372 := by
    simpa [prefixWord, tailWord_3309372, baseEnd_3309372] using wordTrace_append hprefix tailTrace_3309372
  have hstable : (prefixWord ++ tailWord_3309372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309372).length < 2 ^ (prefixWord ++ tailWord_3309372).sum := by decide
  have hdescent : baseEnd_3309372 < baseStart_3309372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309396 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_3309396 : Nat := 118140960795 + 3309396 * 2 ^ 59
def prefixEnd_3309396 : Nat := 4983230072969 + 3 ^ 40 * 3309396 * 2
def baseEnd_3309396 : Nat := 1699310824066839206630371

theorem tailTrace_3309396 : CollatzResearch.WordTrace tailWord_3309396 prefixEnd_3309396 1699310824066839206630371 := by
  unfold tailWord_3309396
  simp only [CollatzResearch.WordTrace]
  refine ⟨60351794159315483342026021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80469058879087311122701361 60351794159315483342026021)
  ·
    refine ⟨11315961404871653126629879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60351794159315483342026021 11315961404871653126629879)
    ·
      refine ⟨16973942107307479689944819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315961404871653126629879 16973942107307479689944819)
      ·
        refine ⟨25460913160961219534917229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16973942107307479689944819 25460913160961219534917229)
        ·
          refine ⟨9547842435360457325593961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25460913160961219534917229 9547842435360457325593961)
          ·
            refine ⟨7160881826520342994195471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9547842435360457325593961 7160881826520342994195471)
            ·
              refine ⟨10741322739780514491293207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160881826520342994195471 10741322739780514491293207)
              ·
                refine ⟨16111984109670771736939811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10741322739780514491293207 16111984109670771736939811)
                ·
                  refine ⟨24167976164506157605409717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16111984109670771736939811 24167976164506157605409717)
                  ·
                    refine ⟨2265747765422452275507161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24167976164506157605409717 2265747765422452275507161)
                    ·
                      refine ⟨1699310824066839206630371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265747765422452275507161 1699310824066839206630371)
                      ·
                        rfl

theorem cell23_3309396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_3309396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309396 prefixEnd_3309396 := by exact prefixLift 3309396
  have htrace : WordTrace (prefixWord ++ tailWord_3309396) baseStart_3309396 baseEnd_3309396 := by
    simpa [prefixWord, tailWord_3309396, baseEnd_3309396] using wordTrace_append hprefix tailTrace_3309396
  have hstable : (prefixWord ++ tailWord_3309396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309396).length < 2 ^ (prefixWord ++ tailWord_3309396).sum := by decide
  have hdescent : baseEnd_3309396 < baseStart_3309396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309402 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_3309402 : Nat := 118140960795 + 3309402 * 2 ^ 59
def prefixEnd_3309402 : Nat := 4983230072969 + 3 ^ 40 * 3309402 * 2
def baseEnd_3309402 : Nat := 566437968316922061051781

theorem tailTrace_3309402 : CollatzResearch.WordTrace tailWord_3309402 prefixEnd_3309402 566437968316922061051781 := by
  unfold tailWord_3309402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30175951789152307427192615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80469204771072819805846973 30175951789152307427192615)
  ·
    refine ⟨45263927683728461140788923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30175951789152307427192615 45263927683728461140788923)
    ·
      refine ⟨67895891525592691711183385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45263927683728461140788923 67895891525592691711183385)
      ·
        refine ⟨50921918644194518783387539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67895891525592691711183385 50921918644194518783387539)
        ·
          refine ⟨76382877966291778175081309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50921918644194518783387539 76382877966291778175081309)
          ·
            refine ⟨28643579237359416815655491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76382877966291778175081309 28643579237359416815655491)
            ·
              refine ⟨42965368856039125223483237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28643579237359416815655491 42965368856039125223483237)
              ·
                refine ⟨8056006660507335979403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42965368856039125223483237 8056006660507335979403107)
                ·
                  refine ⟨12084009990761003969104661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8056006660507335979403107 12084009990761003969104661)
                  ·
                    refine ⟨566437968316922061051781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12084009990761003969104661 566437968316922061051781)
                    ·
                      rfl

theorem cell23_3309402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_3309402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309402 prefixEnd_3309402 := by exact prefixLift 3309402
  have htrace : WordTrace (prefixWord ++ tailWord_3309402) baseStart_3309402 baseEnd_3309402 := by
    simpa [prefixWord, tailWord_3309402, baseEnd_3309402] using wordTrace_append hprefix tailTrace_3309402
  have hstable : (prefixWord ++ tailWord_3309402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309402).length < 2 ^ (prefixWord ++ tailWord_3309402).sum := by decide
  have hdescent : baseEnd_3309402 < baseStart_3309402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309409 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_3309409 : Nat := 118140960795 + 3309409 * 2 ^ 59
def prefixEnd_3309409 : Nat := 4983230072969 + 3 ^ 40 * 3309409 * 2
def baseEnd_3309409 : Nat := 1699317499315347655767811

theorem tailTrace_3309409 : CollatzResearch.WordTrace tailWord_3309409 prefixEnd_3309409 1699317499315347655767811 := by
  unfold tailWord_3309409
  simp only [CollatzResearch.WordTrace]
  refine ⟨120704062467583869904275281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80469374978389246602850187 120704062467583869904275281)
  ·
    refine ⟨90528046850687902428206461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120704062467583869904275281 90528046850687902428206461)
    ·
      refine ⟨33948017569007963410577423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90528046850687902428206461 33948017569007963410577423)
      ·
        refine ⟨50922026353511945115866135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33948017569007963410577423 50922026353511945115866135)
        ·
          refine ⟨76383039530267917673799203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50922026353511945115866135 76383039530267917673799203)
          ·
            refine ⟨114574559295401876510698805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76383039530267917673799203 114574559295401876510698805)
            ·
              refine ⟨10741364933943925922878013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114574559295401876510698805 10741364933943925922878013)
              ·
                refine ⟨4028011850228972221079255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10741364933943925922878013 4028011850228972221079255)
                ·
                  refine ⟨6042017775343458331618883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028011850228972221079255 6042017775343458331618883)
                  ·
                    refine ⟨9063026663015187497428325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6042017775343458331618883 9063026663015187497428325)
                    ·
                      refine ⟨1699317499315347655767811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9063026663015187497428325 1699317499315347655767811)
                      ·
                        rfl

theorem cell23_3309409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_3309409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309409 prefixEnd_3309409 := by exact prefixLift 3309409
  have htrace : WordTrace (prefixWord ++ tailWord_3309409) baseStart_3309409 baseEnd_3309409 := by
    simpa [prefixWord, tailWord_3309409, baseEnd_3309409] using wordTrace_append hprefix tailTrace_3309409
  have hstable : (prefixWord ++ tailWord_3309409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309409).length < 2 ^ (prefixWord ++ tailWord_3309409).sum := by decide
  have hdescent : baseEnd_3309409 < baseStart_3309409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309429 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3309429 : Nat := 118140960795 + 3309429 * 2 ^ 59
def prefixEnd_3309429 : Nat := 4983230072969 + 3 ^ 40 * 3309429 * 2
def baseEnd_3309429 : Nat := 1699327768928437577517719

theorem tailTrace_3309429 : CollatzResearch.WordTrace tailWord_3309429 prefixEnd_3309429 1699327768928437577517719 := by
  unfold tailWord_3309429
  simp only [CollatzResearch.WordTrace]
  refine ⟨120704791927511413320003341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80469861285007608880002227 120704791927511413320003341)
  ·
    refine ⟨45264296972816779995001253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120704791927511413320003341 45264296972816779995001253)
    ·
      refine ⟨8487055682403146249062735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45264296972816779995001253 8487055682403146249062735)
      ·
        refine ⟨12730583523604719373594103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8487055682403146249062735 12730583523604719373594103)
        ·
          refine ⟨19095875285407079060391155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12730583523604719373594103 19095875285407079060391155)
          ·
            refine ⟨28643812928110618590586733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19095875285407079060391155 28643812928110618590586733)
            ·
              refine ⟨10741429848041481971470025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28643812928110618590586733 10741429848041481971470025)
              ·
                refine ⟨8056072386031111478602519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10741429848041481971470025 8056072386031111478602519)
                ·
                  refine ⟨12084108579046667217903779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8056072386031111478602519 12084108579046667217903779)
                  ·
                    refine ⟨18126162868570000826855669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12084108579046667217903779 18126162868570000826855669)
                    ·
                      refine ⟨1699327768928437577517719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18126162868570000826855669 1699327768928437577517719)
                      ·
                        rfl

theorem cell23_3309429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3309429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309429 prefixEnd_3309429 := by exact prefixLift 3309429
  have htrace : WordTrace (prefixWord ++ tailWord_3309429) baseStart_3309429 baseEnd_3309429 := by
    simpa [prefixWord, tailWord_3309429, baseEnd_3309429] using wordTrace_append hprefix tailTrace_3309429
  have hstable : (prefixWord ++ tailWord_3309429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309429).length < 2 ^ (prefixWord ++ tailWord_3309429).sum := by decide
  have hdescent : baseEnd_3309429 < baseStart_3309429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309454 : List Nat := [4, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3309454 : Nat := 118140960795 + 3309454 * 2 ^ 59
def prefixEnd_3309454 : Nat := 4983230072969 + 3 ^ 40 * 3309454 * 2
def baseEnd_3309454 : Nat := 1699340605944799979705105

theorem tailTrace_3309454 : CollatzResearch.WordTrace tailWord_3309454 prefixEnd_3309454 1699340605944799979705105 := by
  unfold tailWord_3309454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088212969052605323707927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80470469168280561726442277 15088212969052605323707927)
  ·
    refine ⟨22632319453578907985561891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15088212969052605323707927 22632319453578907985561891)
    ·
      refine ⟨33948479180368361978342837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22632319453578907985561891 33948479180368361978342837)
      ·
        refine ⟨3182669923159533935469641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33948479180368361978342837 3182669923159533935469641)
        ·
          refine ⟨2387002442369650451602231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182669923159533935469641 2387002442369650451602231)
          ·
            refine ⟨3580503663554475677403347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387002442369650451602231 3580503663554475677403347)
            ·
              refine ⟨5370755495331713516105021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580503663554475677403347 5370755495331713516105021)
              ·
                refine ⟨2014033310749392568539383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5370755495331713516105021 2014033310749392568539383)
                ·
                  refine ⟨3021049966124088852809075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014033310749392568539383 3021049966124088852809075)
                  ·
                    refine ⟨4531574949186133279213613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3021049966124088852809075 4531574949186133279213613)
                    ·
                      refine ⟨1699340605944799979705105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531574949186133279213613 1699340605944799979705105)
                      ·
                        rfl

theorem cell23_3309454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3309454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309454 prefixEnd_3309454 := by exact prefixLift 3309454
  have htrace : WordTrace (prefixWord ++ tailWord_3309454) baseStart_3309454 baseEnd_3309454 := by
    simpa [prefixWord, tailWord_3309454, baseEnd_3309454] using wordTrace_append hprefix tailTrace_3309454
  have hstable : (prefixWord ++ tailWord_3309454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309454).length < 2 ^ (prefixWord ++ tailWord_3309454).sum := by decide
  have hdescent : baseEnd_3309454 < baseStart_3309454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309472 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3309472 : Nat := 118140960795 + 3309472 * 2 ^ 59
def prefixEnd_3309472 : Nat := 4983230072969 + 3 ^ 40 * 3309472 * 2
def baseEnd_3309472 : Nat := 1699349848596580909280021

theorem tailTrace_3309472 : CollatzResearch.WordTrace tailWord_3309472 prefixEnd_3309472 1699349848596580909280021 := by
  unfold tailWord_3309472
  simp only [CollatzResearch.WordTrace]
  refine ⟨60353180133177815831909335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80470906844237087775879113 60353180133177815831909335)
  ·
    refine ⟨90529770199766723747864003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60353180133177815831909335 90529770199766723747864003)
    ·
      refine ⟨135794655299650085621796005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90529770199766723747864003 135794655299650085621796005)
      ·
        refine ⟨25461497868684391054086751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135794655299650085621796005 25461497868684391054086751)
        ·
          refine ⟨38192246803026586581130127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25461497868684391054086751 38192246803026586581130127)
          ·
            refine ⟨57288370204539879871695191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38192246803026586581130127 57288370204539879871695191)
            ·
              refine ⟨85932555306809819807542787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57288370204539879871695191 85932555306809819807542787)
              ·
                refine ⟨128898832960214729711314181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85932555306809819807542787 128898832960214729711314181)
                ·
                  refine ⟨24168531180040261820871409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128898832960214729711314181 24168531180040261820871409)
                  ·
                    refine ⟨18126398385030196365653557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24168531180040261820871409 18126398385030196365653557)
                    ·
                      refine ⟨1699349848596580909280021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18126398385030196365653557 1699349848596580909280021)
                      ·
                        rfl

theorem cell23_3309472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3309472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309472 prefixEnd_3309472 := by exact prefixLift 3309472
  have htrace : WordTrace (prefixWord ++ tailWord_3309472) baseStart_3309472 baseEnd_3309472 := by
    simpa [prefixWord, tailWord_3309472, baseEnd_3309472] using wordTrace_append hprefix tailTrace_3309472
  have hstable : (prefixWord ++ tailWord_3309472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309472).length < 2 ^ (prefixWord ++ tailWord_3309472).sum := by decide
  have hdescent : baseEnd_3309472 < baseStart_3309472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309476 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_3309476 : Nat := 118140960795 + 3309476 * 2 ^ 59
def prefixEnd_3309476 : Nat := 4983230072969 + 3 ^ 40 * 3309476 * 2
def baseEnd_3309476 : Nat := 1699351902519198893630003

theorem tailTrace_3309476 : CollatzResearch.WordTrace tailWord_3309476 prefixEnd_3309476 1699351902519198893630003 := by
  unfold tailWord_3309476
  simp only [CollatzResearch.WordTrace]
  refine ⟨60353253079170570173482141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80471004105560760231309521 60353253079170570173482141)
  ·
    refine ⟨22632469904688963815055803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60353253079170570173482141 22632469904688963815055803)
    ·
      refine ⟨33948704857033445722583705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22632469904688963815055803 33948704857033445722583705)
      ·
        refine ⟨25461528642775084291937779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33948704857033445722583705 25461528642775084291937779)
        ·
          refine ⟨38192292964162626437906669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25461528642775084291937779 38192292964162626437906669)
          ·
            refine ⟨14322109861560984914215001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38192292964162626437906669 14322109861560984914215001)
            ·
              refine ⟨10741582396170738685661251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14322109861560984914215001 10741582396170738685661251)
              ·
                refine ⟨16112373594256108028491877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10741582396170738685661251 16112373594256108028491877)
                ·
                  refine ⟨3021070048923020255342227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16112373594256108028491877 3021070048923020255342227)
                  ·
                    refine ⟨4531605073384530383013341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3021070048923020255342227 4531605073384530383013341)
                    ·
                      refine ⟨1699351902519198893630003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531605073384530383013341 1699351902519198893630003)
                      ·
                        rfl

theorem cell23_3309476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_3309476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309476 prefixEnd_3309476 := by exact prefixLift 3309476
  have htrace : WordTrace (prefixWord ++ tailWord_3309476) baseStart_3309476 baseEnd_3309476 := by
    simpa [prefixWord, tailWord_3309476, baseEnd_3309476] using wordTrace_append hprefix tailTrace_3309476
  have hstable : (prefixWord ++ tailWord_3309476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309476).length < 2 ^ (prefixWord ++ tailWord_3309476).sum := by decide
  have hdescent : baseEnd_3309476 < baseStart_3309476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309493 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3309493 : Nat := 118140960795 + 3309493 * 2 ^ 59
def prefixEnd_3309493 : Nat := 4983230072969 + 3 ^ 40 * 3309493 * 2
def baseEnd_3309493 : Nat := 1699360631690325327117425

theorem tailTrace_3309493 : CollatzResearch.WordTrace tailWord_3309493 prefixEnd_3309493 1699360631690325327117425 := by
  unfold tailWord_3309493
  simp only [CollatzResearch.WordTrace]
  refine ⟨120707126199279552250333133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80471417466186368166888755 120707126199279552250333133)
  ·
    refine ⟨45265172324729832093874925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120707126199279552250333133 45265172324729832093874925)
    ·
      refine ⟨16974439621773687035203097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45265172324729832093874925 16974439621773687035203097)
      ·
        refine ⟨12730829716330265276402323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16974439621773687035203097 12730829716330265276402323)
        ·
          refine ⟨19096244574495397914603485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12730829716330265276402323 19096244574495397914603485)
          ·
            refine ⟨7161091715435774217976307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19096244574495397914603485 7161091715435774217976307)
            ·
              refine ⟨10741637573153661326964461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161091715435774217976307 10741637573153661326964461)
              ·
                refine ⟨4028114089932622997611673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10741637573153661326964461 4028114089932622997611673)
                ·
                  refine ⟨3021085567449467248208755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4028114089932622997611673 3021085567449467248208755)
                  ·
                    refine ⟨4531628351174200872313133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3021085567449467248208755 4531628351174200872313133)
                    ·
                      refine ⟨1699360631690325327117425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531628351174200872313133 1699360631690325327117425)
                      ·
                        rfl

theorem cell23_3309493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3309493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309493 prefixEnd_3309493 := by exact prefixLift 3309493
  have htrace : WordTrace (prefixWord ++ tailWord_3309493) baseStart_3309493 baseEnd_3309493 := by
    simpa [prefixWord, tailWord_3309493, baseEnd_3309493] using wordTrace_append hprefix tailTrace_3309493
  have hstable : (prefixWord ++ tailWord_3309493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309493).length < 2 ^ (prefixWord ++ tailWord_3309493).sum := by decide
  have hdescent : baseEnd_3309493 < baseStart_3309493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309516 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3309516 : Nat := 118140960795 + 3309516 * 2 ^ 59
def prefixEnd_3309516 : Nat := 4983230072969 + 3 ^ 40 * 3309516 * 2
def baseEnd_3309516 : Nat := 1699372441745378737129819

theorem tailTrace_3309516 : CollatzResearch.WordTrace tailWord_3309516 prefixEnd_3309516 1699372441745378737129819 := by
  unfold tailWord_3309516
  simp only [CollatzResearch.WordTrace]
  refine ⟨60353982539098113589210201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80471976718797484785613601 60353982539098113589210201)
  ·
    refine ⟨45265486904323585191907651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60353982539098113589210201 45265486904323585191907651)
    ·
      refine ⟨67898230356485377787861477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45265486904323585191907651 67898230356485377787861477)
      ·
        refine ⟨12730918191841008335224027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67898230356485377787861477 12730918191841008335224027)
        ·
          refine ⟨19096377287761512502836041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12730918191841008335224027 19096377287761512502836041)
          ·
            refine ⟨14322282965821134377127031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19096377287761512502836041 14322282965821134377127031)
            ·
              refine ⟨21483424448731701565690547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14322282965821134377127031 21483424448731701565690547)
              ·
                refine ⟨32225136673097552348535821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21483424448731701565690547 32225136673097552348535821)
                ·
                  refine ⟨12084426252411582130700933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32225136673097552348535821 12084426252411582130700933)
                  ·
                    refine ⟨2265829922327171649506425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12084426252411582130700933 2265829922327171649506425)
                    ·
                      refine ⟨1699372441745378737129819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265829922327171649506425 1699372441745378737129819)
                      ·
                        rfl

theorem cell23_3309516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3309516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309516 prefixEnd_3309516 := by exact prefixLift 3309516
  have htrace : WordTrace (prefixWord ++ tailWord_3309516) baseStart_3309516 baseEnd_3309516 := by
    simpa [prefixWord, tailWord_3309516, baseEnd_3309516] using wordTrace_append hprefix tailTrace_3309516
  have hstable : (prefixWord ++ tailWord_3309516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309516).length < 2 ^ (prefixWord ++ tailWord_3309516).sum := by decide
  have hdescent : baseEnd_3309516 < baseStart_3309516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309550 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_3309550 : Nat := 118140960795 + 3309550 * 2 ^ 59
def prefixEnd_3309550 : Nat := 4983230072969 + 3 ^ 40 * 3309550 * 2
def baseEnd_3309550 : Nat := 1699389900087631604104663

theorem tailTrace_3309550 : CollatzResearch.WordTrace tailWord_3309550 prefixEnd_3309550 1699389900087631604104663 := by
  unfold tailWord_3309550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088650645009131373144763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80472803440048700656772069 15088650645009131373144763)
  ·
    refine ⟨22632975967513697059717145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15088650645009131373144763 22632975967513697059717145)
    ·
      refine ⟨16974731975635272794787859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22632975967513697059717145 16974731975635272794787859)
      ·
        refine ⟨25462097963452909192181789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16974731975635272794787859 25462097963452909192181789)
        ·
          refine ⟨9548286736294840947068171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25462097963452909192181789 9548286736294840947068171)
          ·
            refine ⟨14322430104442261420602257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9548286736294840947068171 14322430104442261420602257)
            ·
              refine ⟨10741822578331696065451693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14322430104442261420602257 10741822578331696065451693)
              ·
                refine ⟨4028183466874386024544385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10741822578331696065451693 4028183466874386024544385)
                ·
                  refine ⟨3021137600155789518408289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4028183466874386024544385 3021137600155789518408289)
                  ·
                    refine ⟨2265853200116842138806217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3021137600155789518408289 2265853200116842138806217)
                    ·
                      refine ⟨1699389900087631604104663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265853200116842138806217 1699389900087631604104663)
                      ·
                        rfl

theorem cell23_3309550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_3309550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309550 prefixEnd_3309550 := by exact prefixLift 3309550
  have htrace : WordTrace (prefixWord ++ tailWord_3309550) baseStart_3309550 baseEnd_3309550 := by
    simpa [prefixWord, tailWord_3309550, baseEnd_3309550] using wordTrace_append hprefix tailTrace_3309550
  have hstable : (prefixWord ++ tailWord_3309550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309550).length < 2 ^ (prefixWord ++ tailWord_3309550).sum := by decide
  have hdescent : baseEnd_3309550 < baseStart_3309550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309569 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3309569 : Nat := 118140960795 + 3309569 * 2 ^ 59
def prefixEnd_3309569 : Nat := 4983230072969 + 3 ^ 40 * 3309569 * 2
def baseEnd_3309569 : Nat := 566466552073355676589025

theorem tailTrace_3309569 : CollatzResearch.WordTrace tailWord_3309569 prefixEnd_3309569 566466552073355676589025 := by
  unfold tailWord_3309569
  simp only [CollatzResearch.WordTrace]
  refine ⟨120709898147004217230099761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80473265431336144820066507 120709898147004217230099761)
  ·
    refine ⟨90532423610253162922574821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120709898147004217230099761 90532423610253162922574821)
    ·
      refine ⟨16974829426922468047982779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90532423610253162922574821 16974829426922468047982779)
      ·
        refine ⟨25462244140383702071974169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16974829426922468047982779 25462244140383702071974169)
        ·
          refine ⟨19096683105287776553980627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25462244140383702071974169 19096683105287776553980627)
          ·
            refine ⟨28645024657931664830970941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19096683105287776553980627 28645024657931664830970941)
            ·
              refine ⟨10741884246724374311614103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28645024657931664830970941 10741884246724374311614103)
              ·
                refine ⟨16112826370086561467421155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10741884246724374311614103 16112826370086561467421155)
                ·
                  refine ⟨24169239555129842201131733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16112826370086561467421155 24169239555129842201131733)
                  ·
                    refine ⟨566466552073355676589025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24169239555129842201131733 566466552073355676589025)
                    ·
                      rfl

theorem cell23_3309569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3309569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309569 prefixEnd_3309569 := by exact prefixLift 3309569
  have htrace : WordTrace (prefixWord ++ tailWord_3309569) baseStart_3309569 baseEnd_3309569 := by
    simpa [prefixWord, tailWord_3309569, baseEnd_3309569] using wordTrace_append hprefix tailTrace_3309569
  have hstable : (prefixWord ++ tailWord_3309569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309569).length < 2 ^ (prefixWord ++ tailWord_3309569).sum := by decide
  have hdescent : baseEnd_3309569 < baseStart_3309569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309616 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 3, 4]
def baseStart_3309616 : Nat := 118140960795 + 3309616 * 2 ^ 59
def prefixEnd_3309616 : Nat := 4983230072969 + 3 ^ 40 * 3309616 * 2
def baseEnd_3309616 : Nat := 566474596603609448626453

theorem tailTrace_3309616 : CollatzResearch.WordTrace tailWord_3309616 prefixEnd_3309616 566474596603609448626453 := by
  unfold tailWord_3309616
  simp only [CollatzResearch.WordTrace]
  refine ⟨60355806188916972128530351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80474408251889296171373801 60355806188916972128530351)
  ·
    refine ⟨90533709283375458192795527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60355806188916972128530351 90533709283375458192795527)
    ·
      refine ⟨135800563925063187289193291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90533709283375458192795527 135800563925063187289193291)
      ·
        refine ⟨203700845887594780933789937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135800563925063187289193291 203700845887594780933789937)
        ·
          refine ⟨152775634415696085700342453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203700845887594780933789937 152775634415696085700342453)
          ·
            refine ⟨14322715726471508034407105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152775634415696085700342453 14322715726471508034407105)
            ·
              refine ⟨10742036794853631025805329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14322715726471508034407105 10742036794853631025805329)
              ·
                refine ⟨8056527596140223269353997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10742036794853631025805329 8056527596140223269353997)
                ·
                  refine ⟨3021197848552583726007749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8056527596140223269353997 3021197848552583726007749)
                  ·
                    refine ⟨566474596603609448626453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3021197848552583726007749 566474596603609448626453)
                    ·
                      rfl

theorem cell23_3309616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_3309616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309616 prefixEnd_3309616 := by exact prefixLift 3309616
  have htrace : WordTrace (prefixWord ++ tailWord_3309616) baseStart_3309616 baseEnd_3309616 := by
    simpa [prefixWord, tailWord_3309616, baseEnd_3309616] using wordTrace_append hprefix tailTrace_3309616
  have hstable : (prefixWord ++ tailWord_3309616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309616).length < 2 ^ (prefixWord ++ tailWord_3309616).sum := by decide
  have hdescent : baseEnd_3309616 < baseStart_3309616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309626 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_3309626 : Nat := 118140960795 + 3309626 * 2 ^ 59
def prefixEnd_3309626 : Nat := 4983230072969 + 3 ^ 40 * 3309626 * 2
def baseEnd_3309626 : Nat := 1699428924617373306754313

theorem tailTrace_3309626 : CollatzResearch.WordTrace tailWord_3309626 prefixEnd_3309626 1699428924617373306754313 := by
  unfold tailWord_3309626
  simp only [CollatzResearch.WordTrace]
  refine ⟨30177994276949428991231183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80474651405198477309949821 30177994276949428991231183)
  ·
    refine ⟨45266991415424143486846775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30177994276949428991231183 45266991415424143486846775)
    ·
      refine ⟨67900487123136215230270163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45266991415424143486846775 67900487123136215230270163)
      ·
        refine ⟨101850730684704322845405245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67900487123136215230270163 101850730684704322845405245)
        ·
          refine ⟨38194024006764121067026967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101850730684704322845405245 38194024006764121067026967)
          ·
            refine ⟨57291036010146181600540451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38194024006764121067026967 57291036010146181600540451)
            ·
              refine ⟨85936554015219272400810677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57291036010146181600540451 85936554015219272400810677)
              ·
                refine ⟨8056551938926806787576001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85936554015219272400810677 8056551938926806787576001)
                ·
                  refine ⟨6042413954195105090682001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8056551938926806787576001 6042413954195105090682001)
                  ·
                    refine ⟨4531810465646328818011501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6042413954195105090682001 4531810465646328818011501)
                    ·
                      refine ⟨1699428924617373306754313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531810465646328818011501 1699428924617373306754313)
                      ·
                        rfl

theorem cell23_3309626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_3309626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309626 prefixEnd_3309626 := by exact prefixLift 3309626
  have htrace : WordTrace (prefixWord ++ tailWord_3309626) baseStart_3309626 baseEnd_3309626 := by
    simpa [prefixWord, tailWord_3309626, baseEnd_3309626] using wordTrace_append hprefix tailTrace_3309626
  have hstable : (prefixWord ++ tailWord_3309626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309626).length < 2 ^ (prefixWord ++ tailWord_3309626).sum := by decide
  have hdescent : baseEnd_3309626 < baseStart_3309626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309629 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 10]
def baseStart_3309629 : Nat := 118140960795 + 3309629 * 2 ^ 59
def prefixEnd_3309629 : Nat := 4983230072969 + 3 ^ 40 * 3309629 * 2
def baseEnd_3309629 : Nat := 188825607228815199446311

theorem tailTrace_3309629 : CollatzResearch.WordTrace tailWord_3309629 prefixEnd_3309629 188825607228815199446311 := by
  unfold tailWord_3309629
  simp only [CollatzResearch.WordTrace]
  refine ⟨120712086526786847477283941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80474724351191231651522627 120712086526786847477283941)
  ·
    refine ⟨22633516223772533901990739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120712086526786847477283941 22633516223772533901990739)
    ·
      refine ⟨33950274335658800852986109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22633516223772533901990739 33950274335658800852986109)
      ·
        refine ⟨12731352875872050319869791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33950274335658800852986109 12731352875872050319869791)
        ·
          refine ⟨19097029313808075479804687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12731352875872050319869791 19097029313808075479804687)
          ·
            refine ⟨28645543970712113219707031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19097029313808075479804687 28645543970712113219707031)
            ·
              refine ⟨42968315956068169829560547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28645543970712113219707031 42968315956068169829560547)
              ·
                refine ⟨64452473934102254744340821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42968315956068169829560547 64452473934102254744340821)
                ·
                  refine ⟨188825607228815199446311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 64452473934102254744340821 188825607228815199446311)
                  ·
                    rfl

theorem cell23_3309629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_3309629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309629 prefixEnd_3309629 := by exact prefixLift 3309629
  have htrace : WordTrace (prefixWord ++ tailWord_3309629) baseStart_3309629 baseEnd_3309629 := by
    simpa [prefixWord, tailWord_3309629, baseEnd_3309629] using wordTrace_append hprefix tailTrace_3309629
  have hstable : (prefixWord ++ tailWord_3309629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309629).length < 2 ^ (prefixWord ++ tailWord_3309629).sum := by decide
  have hdescent : baseEnd_3309629 < baseStart_3309629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309650 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3309650 : Nat := 118140960795 + 3309650 * 2 ^ 59
def prefixEnd_3309650 : Nat := 4983230072969 + 3 ^ 40 * 3309650 * 2
def baseEnd_3309650 : Nat := 566480416051027070951401

theorem tailTrace_3309650 : CollatzResearch.WordTrace tailWord_3309650 prefixEnd_3309650 566480416051027070951401 := by
  unfold tailWord_3309650
  simp only [CollatzResearch.WordTrace]
  refine ⟨30178213114927692015949601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80475234973140512042532269 30178213114927692015949601)
  ·
    refine ⟨22633659836195769011962201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30178213114927692015949601 22633659836195769011962201)
    ·
      refine ⟨16975244877146826758971651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22633659836195769011962201 16975244877146826758971651)
      ·
        refine ⟨25462867315720240138457477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16975244877146826758971651 25462867315720240138457477)
        ·
          refine ⟨4774287621697545025960777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25462867315720240138457477 4774287621697545025960777)
          ·
            refine ⟨3580715716273158769470583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4774287621697545025960777 3580715716273158769470583)
            ·
              refine ⟨5371073574409738154205875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580715716273158769470583 5371073574409738154205875)
              ·
                refine ⟨8056610361614607231308813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371073574409738154205875 8056610361614607231308813)
                ·
                  refine ⟨3021228885605477711740805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8056610361614607231308813 3021228885605477711740805)
                  ·
                    refine ⟨566480416051027070951401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3021228885605477711740805 566480416051027070951401)
                    ·
                      rfl

theorem cell23_3309650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3309650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309650 prefixEnd_3309650 := by exact prefixLift 3309650
  have htrace : WordTrace (prefixWord ++ tailWord_3309650) baseStart_3309650 baseEnd_3309650 := by
    simpa [prefixWord, tailWord_3309650, baseEnd_3309650] using wordTrace_append hprefix tailTrace_3309650
  have hstable : (prefixWord ++ tailWord_3309650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309650).length < 2 ^ (prefixWord ++ tailWord_3309650).sum := by decide
  have hdescent : baseEnd_3309650 < baseStart_3309650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309676 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_3309676 : Nat := 118140960795 + 3309676 * 2 ^ 59
def prefixEnd_3309676 : Nat := 4983230072969 + 3 ^ 40 * 3309676 * 2
def baseEnd_3309676 : Nat := 566484866216699370376361

theorem tailTrace_3309676 : CollatzResearch.WordTrace tailWord_3309676 prefixEnd_3309676 566484866216699370376361 := by
  unfold tailWord_3309676
  simp only [CollatzResearch.WordTrace]
  refine ⟨60356900378808287252122441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80475867171744383002829921 60356900378808287252122441)
  ·
    refine ⟨45267675284106215439091831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60356900378808287252122441 45267675284106215439091831)
    ·
      refine ⟨67901512926159323158637747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45267675284106215439091831 67901512926159323158637747)
      ·
        refine ⟨101852269389238984737956621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67901512926159323158637747 101852269389238984737956621)
        ·
          refine ⟨38194601020964619276733733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101852269389238984737956621 38194601020964619276733733)
          ·
            refine ⟨7161487691430866114387575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38194601020964619276733733 7161487691430866114387575)
            ·
              refine ⟨10742231537146299171581363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161487691430866114387575 10742231537146299171581363)
              ·
                refine ⟨16113347305719448757372045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742231537146299171581363 16113347305719448757372045)
                ·
                  refine ⟨6042505239644793284014517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16113347305719448757372045 6042505239644793284014517)
                  ·
                    refine ⟨566484866216699370376361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6042505239644793284014517 566484866216699370376361)
                    ·
                      rfl

theorem cell23_3309676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_3309676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309676 prefixEnd_3309676 := by exact prefixLift 3309676
  have htrace : WordTrace (prefixWord ++ tailWord_3309676) baseStart_3309676 baseEnd_3309676 := by
    simpa [prefixWord, tailWord_3309676, baseEnd_3309676] using wordTrace_append hprefix tailTrace_3309676
  have hstable : (prefixWord ++ tailWord_3309676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309676).length < 2 ^ (prefixWord ++ tailWord_3309676).sum := by decide
  have hdescent : baseEnd_3309676 < baseStart_3309676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309713 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 9, 2, 2]
def baseStart_3309713 : Nat := 118140960795 + 3309713 * 2 ^ 59
def prefixEnd_3309713 : Nat := 4983230072969 + 3 ^ 40 * 3309713 * 2
def baseEnd_3309713 : Nat := 1699473597434314466366413

theorem tailTrace_3309713 : CollatzResearch.WordTrace tailWord_3309713 prefixEnd_3309713 1699473597434314466366413 := by
  unfold tailWord_3309713
  simp only [CollatzResearch.WordTrace]
  refine ⟨120715150258482529823341793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80476766838988353215561195 120715150258482529823341793)
  ·
    refine ⟨90536362693861897367506345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120715150258482529823341793 90536362693861897367506345)
    ·
      refine ⟨67902272020396423025629759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90536362693861897367506345 67902272020396423025629759)
      ·
        refine ⟨101853408030594634538444639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67902272020396423025629759 101853408030594634538444639)
        ·
          refine ⟨152780112045891951807666959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101853408030594634538444639 152780112045891951807666959)
          ·
            refine ⟨229170168068837927711500439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152780112045891951807666959 229170168068837927711500439)
            ·
              refine ⟨343755252103256891567250659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229170168068837927711500439 343755252103256891567250659)
              ·
                refine ⟨515632878154885337350875989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343755252103256891567250659 515632878154885337350875989)
                ·
                  refine ⟨3021286395438781273540289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 515632878154885337350875989 3021286395438781273540289)
                  ·
                    refine ⟨2265964796579085955155217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3021286395438781273540289 2265964796579085955155217)
                    ·
                      refine ⟨1699473597434314466366413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265964796579085955155217 1699473597434314466366413)
                      ·
                        rfl

theorem cell23_3309713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_3309713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309713 prefixEnd_3309713 := by exact prefixLift 3309713
  have htrace : WordTrace (prefixWord ++ tailWord_3309713) baseStart_3309713 baseEnd_3309713 := by
    simpa [prefixWord, tailWord_3309713, baseEnd_3309713] using wordTrace_append hprefix tailTrace_3309713
  have hstable : (prefixWord ++ tailWord_3309713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309713).length < 2 ^ (prefixWord ++ tailWord_3309713).sum := by decide
  have hdescent : baseEnd_3309713 < baseStart_3309713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309733 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_3309733 : Nat := 118140960795 + 3309733 * 2 ^ 59
def prefixEnd_3309733 : Nat := 4983230072969 + 3 ^ 40 * 3309733 * 2
def baseEnd_3309733 : Nat := 1699483867047404388116321

theorem tailTrace_3309733 : CollatzResearch.WordTrace tailWord_3309733 prefixEnd_3309733 1699483867047404388116321 := by
  unfold tailWord_3309733
  simp only [CollatzResearch.WordTrace]
  refine ⟨120715879718410073239069853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80477253145606715492713235 120715879718410073239069853)
  ·
    refine ⟨45268454894403777464651195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120715879718410073239069853 45268454894403777464651195)
    ·
      refine ⟨67902682341605666196976793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45268454894403777464651195 67902682341605666196976793)
      ·
        refine ⟨50927011756204249647732595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67902682341605666196976793 50927011756204249647732595)
        ·
          refine ⟨76390517634306374471598893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50927011756204249647732595 76390517634306374471598893)
          ·
            refine ⟨28646444112864890426849585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76390517634306374471598893 28646444112864890426849585)
            ·
              refine ⟨21484833084648667820137189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28646444112864890426849585 21484833084648667820137189)
              ·
                refine ⟨4028406203371625216275723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21484833084648667820137189 4028406203371625216275723)
                ·
                  refine ⟨6042609305057437824413585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028406203371625216275723 6042609305057437824413585)
                  ·
                    refine ⟨4531956978793078368310189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6042609305057437824413585 4531956978793078368310189)
                    ·
                      refine ⟨1699483867047404388116321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4531956978793078368310189 1699483867047404388116321)
                      ·
                        rfl

theorem cell23_3309733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_3309733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309733 prefixEnd_3309733 := by exact prefixLift 3309733
  have htrace : WordTrace (prefixWord ++ tailWord_3309733) baseStart_3309733 baseEnd_3309733 := by
    simpa [prefixWord, tailWord_3309733, baseEnd_3309733] using wordTrace_append hprefix tailTrace_3309733
  have hstable : (prefixWord ++ tailWord_3309733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309733).length < 2 ^ (prefixWord ++ tailWord_3309733).sum := by decide
  have hdescent : baseEnd_3309733 < baseStart_3309733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309739 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6]
def baseStart_3309739 : Nat := 118140960795 + 3309739 * 2 ^ 59
def prefixEnd_3309739 : Nat := 4983230072969 + 3 ^ 40 * 3309739 * 2
def baseEnd_3309739 : Nat := 1699486947931331364641293

theorem tailTrace_3309739 : CollatzResearch.WordTrace tailWord_3309739 prefixEnd_3309739 1699486947931331364641293 := by
  unfold tailWord_3309739
  simp only [CollatzResearch.WordTrace]
  refine ⟨120716098556388336263788271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80477399037592224175858847 120716098556388336263788271)
  ·
    refine ⟨181074147834582504395682407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120716098556388336263788271 181074147834582504395682407)
    ·
      refine ⟨271611221751873756593523611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181074147834582504395682407 271611221751873756593523611)
      ·
        refine ⟨407416832627810634890285417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271611221751873756593523611 407416832627810634890285417)
        ·
          refine ⟨305562624470857976167714063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407416832627810634890285417 305562624470857976167714063)
          ·
            refine ⟨458343936706286964251571095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305562624470857976167714063 458343936706286964251571095)
            ·
              refine ⟨687515905059430446377356643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458343936706286964251571095 687515905059430446377356643)
              ·
                refine ⟨1031273857589145669566034965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687515905059430446377356643 1031273857589145669566034965)
                ·
                  refine ⟨48340962074491203260907889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1031273857589145669566034965 48340962074491203260907889)
                  ·
                    refine ⟨36255721555868402445680917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48340962074491203260907889 36255721555868402445680917)
                    ·
                      refine ⟨1699486947931331364641293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36255721555868402445680917 1699486947931331364641293)
                      ·
                        rfl

theorem cell23_3309739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_3309739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309739 prefixEnd_3309739 := by exact prefixLift 3309739
  have htrace : WordTrace (prefixWord ++ tailWord_3309739) baseStart_3309739 baseEnd_3309739 := by
    simpa [prefixWord, tailWord_3309739, baseEnd_3309739] using wordTrace_append hprefix tailTrace_3309739
  have hstable : (prefixWord ++ tailWord_3309739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309739).length < 2 ^ (prefixWord ++ tailWord_3309739).sum := by decide
  have hdescent : baseEnd_3309739 < baseStart_3309739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309764 : List Nat := [2, 3, 3, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_3309764 : Nat := 118140960795 + 3309764 * 2 ^ 59
def prefixEnd_3309764 : Nat := 4983230072969 + 3 ^ 40 * 3309764 * 2
def baseEnd_3309764 : Nat := 1699499784947693766828679

theorem tailTrace_3309764 : CollatzResearch.WordTrace tailWord_3309764 prefixEnd_3309764 1699499784947693766828679 := by
  unfold tailWord_3309764
  simp only [CollatzResearch.WordTrace]
  refine ⟨60358505190648882766724173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80478006920865177022298897 60358505190648882766724173)
  ·
    refine ⟨22634439446493331037521565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60358505190648882766724173 22634439446493331037521565)
    ·
      refine ⟨8487914792434999139070587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22634439446493331037521565 8487914792434999139070587)
      ·
        refine ⟨12731872188652498708605881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8487914792434999139070587 12731872188652498708605881)
        ·
          refine ⟨9548904141489374031454411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12731872188652498708605881 9548904141489374031454411)
          ·
            refine ⟨14323356212234061047181617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9548904141489374031454411 14323356212234061047181617)
            ·
              refine ⟨10742517159175545785386213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14323356212234061047181617 10742517159175545785386213)
              ·
                refine ⟨2014221967345414834759915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10742517159175545785386213 2014221967345414834759915)
                ·
                  refine ⟨3021332951018122252139873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014221967345414834759915 3021332951018122252139873)
                  ·
                    refine ⟨2265999713263591689104905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3021332951018122252139873 2265999713263591689104905)
                    ·
                      refine ⟨1699499784947693766828679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2265999713263591689104905 1699499784947693766828679)
                      ·
                        rfl

theorem cell23_3309764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_3309764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309764 prefixEnd_3309764 := by exact prefixLift 3309764
  have htrace : WordTrace (prefixWord ++ tailWord_3309764) baseStart_3309764 baseEnd_3309764 := by
    simpa [prefixWord, tailWord_3309764, baseEnd_3309764] using wordTrace_append hprefix tailTrace_3309764
  have hstable : (prefixWord ++ tailWord_3309764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309764).length < 2 ^ (prefixWord ++ tailWord_3309764).sum := by decide
  have hdescent : baseEnd_3309764 < baseStart_3309764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309786 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3309786 : Nat := 118140960795 + 3309786 * 2 ^ 59
def prefixEnd_3309786 : Nat := 4983230072969 + 3 ^ 40 * 3309786 * 2
def baseEnd_3309786 : Nat := 1699511081522092680753577

theorem tailTrace_3309786 : CollatzResearch.WordTrace tailWord_3309786 prefixEnd_3309786 1699511081522092680753577 := by
  unfold tailWord_3309786
  simp only [CollatzResearch.WordTrace]
  refine ⟨30179453196804515822687303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80478541858145375527166141 30179453196804515822687303)
  ·
    refine ⟨45269179795206773734030955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30179453196804515822687303 45269179795206773734030955)
    ·
      refine ⟨67903769692810160601046433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45269179795206773734030955 67903769692810160601046433)
      ·
        refine ⟨50927827269607620450784825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67903769692810160601046433 50927827269607620450784825)
        ·
          refine ⟨38195870452205715338088619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50927827269607620450784825 38195870452205715338088619)
          ·
            refine ⟨57293805678308573007132929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38195870452205715338088619 57293805678308573007132929)
            ·
              refine ⟨42970354258731429755349697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57293805678308573007132929 42970354258731429755349697)
              ·
                refine ⟨32227765694048572316512273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42970354258731429755349697 32227765694048572316512273)
                ·
                  refine ⟨24170824270536429237384205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32227765694048572316512273 24170824270536429237384205)
                  ·
                    refine ⟨9064059101451160964019077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24170824270536429237384205 9064059101451160964019077)
                    ·
                      refine ⟨1699511081522092680753577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9064059101451160964019077 1699511081522092680753577)
                      ·
                        rfl

theorem cell23_3309786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3309786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309786 prefixEnd_3309786 := by exact prefixLift 3309786
  have htrace : WordTrace (prefixWord ++ tailWord_3309786) baseStart_3309786 baseEnd_3309786 := by
    simpa [prefixWord, tailWord_3309786, baseEnd_3309786] using wordTrace_append hprefix tailTrace_3309786
  have hstable : (prefixWord ++ tailWord_3309786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309786).length < 2 ^ (prefixWord ++ tailWord_3309786).sum := by decide
  have hdescent : baseEnd_3309786 < baseStart_3309786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309803 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 3, 4, 2]
def baseStart_3309803 : Nat := 118140960795 + 3309803 * 2 ^ 59
def prefixEnd_3309803 : Nat := 4983230072969 + 3 ^ 40 * 3309803 * 2
def baseEnd_3309803 : Nat := 1699519810693219114240999

theorem tailTrace_3309803 : CollatzResearch.WordTrace tailWord_3309803 prefixEnd_3309803 1699519810693219114240999 := by
  unfold tailWord_3309803
  simp only [CollatzResearch.WordTrace]
  refine ⟨120718432828156475194118063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80478955218770983462745375 120718432828156475194118063)
  ·
    refine ⟨181077649242234712791177095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120718432828156475194118063 181077649242234712791177095)
    ·
      refine ⟨271616473863352069186765643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181077649242234712791177095 271616473863352069186765643)
      ·
        refine ⟨407424710795028103780148465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271616473863352069186765643 407424710795028103780148465)
        ·
          refine ⟨305568533096271077835111349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407424710795028103780148465 305568533096271077835111349)
          ·
            refine ⟨28647049977775413547041689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305568533096271077835111349 28647049977775413547041689)
            ·
              refine ⟨21485287483331560160281267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28647049977775413547041689 21485287483331560160281267)
              ·
                refine ⟨32227931224997340240421901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21485287483331560160281267 32227931224997340240421901)
                ·
                  refine ⟨12085474209374002590158213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32227931224997340240421901 12085474209374002590158213)
                  ·
                    refine ⟨2266026414257625485654665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12085474209374002590158213 2266026414257625485654665)
                    ·
                      refine ⟨1699519810693219114240999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266026414257625485654665 1699519810693219114240999)
                      ·
                        rfl

theorem cell23_3309803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 4, 2].length) (baseStart_3309803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309803 prefixEnd_3309803 := by exact prefixLift 3309803
  have htrace : WordTrace (prefixWord ++ tailWord_3309803) baseStart_3309803 baseEnd_3309803 := by
    simpa [prefixWord, tailWord_3309803, baseEnd_3309803] using wordTrace_append hprefix tailTrace_3309803
  have hstable : (prefixWord ++ tailWord_3309803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309803).length < 2 ^ (prefixWord ++ tailWord_3309803).sum := by decide
  have hdescent : baseEnd_3309803 < baseStart_3309803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309816 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_3309816 : Nat := 118140960795 + 3309816 * 2 ^ 59
def prefixEnd_3309816 : Nat := 4983230072969 + 3 ^ 40 * 3309816 * 2
def baseEnd_3309816 : Nat := 1699526485941727563378439

theorem tailTrace_3309816 : CollatzResearch.WordTrace tailWord_3309816 prefixEnd_3309816 1699526485941727563378439 := by
  unfold tailWord_3309816
  simp only [CollatzResearch.WordTrace]
  refine ⟨60359453488554689207170651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80479271318072918942894201 60359453488554689207170651)
  ·
    refine ⟨90539180232832033810755977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60359453488554689207170651 90539180232832033810755977)
    ·
      refine ⟨67904385174624025358066983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90539180232832033810755977 67904385174624025358066983)
      ·
        refine ⟨101856577761936038037100475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67904385174624025358066983 101856577761936038037100475)
        ·
          refine ⟨152784866642904057055650713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101856577761936038037100475 152784866642904057055650713)
          ·
            refine ⟨114588649982178042791738035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152784866642904057055650713 114588649982178042791738035)
            ·
              refine ⟨171882974973267064187607053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114588649982178042791738035 171882974973267064187607053)
              ·
                refine ⟨64456115614975149070352645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171882974973267064187607053 64456115614975149070352645)
                ·
                  refine ⟨12085521677807840450691121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64456115614975149070352645 12085521677807840450691121)
                  ·
                    refine ⟨9064141258355880338018341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12085521677807840450691121 9064141258355880338018341)
                    ·
                      refine ⟨1699526485941727563378439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9064141258355880338018341 1699526485941727563378439)
                      ·
                        rfl

theorem cell23_3309816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_3309816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309816 prefixEnd_3309816 := by exact prefixLift 3309816
  have htrace : WordTrace (prefixWord ++ tailWord_3309816) baseStart_3309816 baseEnd_3309816 := by
    simpa [prefixWord, tailWord_3309816, baseEnd_3309816] using wordTrace_append hprefix tailTrace_3309816
  have hstable : (prefixWord ++ tailWord_3309816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309816).length < 2 ^ (prefixWord ++ tailWord_3309816).sum := by decide
  have hdescent : baseEnd_3309816 < baseStart_3309816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309831 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3309831 : Nat := 118140960795 + 3309831 * 2 ^ 59
def prefixEnd_3309831 : Nat := 4983230072969 + 3 ^ 40 * 3309831 * 2
def baseEnd_3309831 : Nat := 1699534188151545004690871

theorem tailTrace_3309831 : CollatzResearch.WordTrace tailWord_3309831 prefixEnd_3309831 1699534188151545004690871 := by
  unfold tailWord_3309831
  simp only [CollatzResearch.WordTrace]
  refine ⟨120719454072055035976137347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80479636048036690650758231 120719454072055035976137347)
  ·
    refine ⟨181079181108082553964206021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120719454072055035976137347 181079181108082553964206021)
    ·
      refine ⟨33952346457765478868288629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181079181108082553964206021 33952346457765478868288629)
      ·
        refine ⟨3183032480415513643902059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33952346457765478868288629 3183032480415513643902059)
        ·
          refine ⟨4774548720623270465853089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183032480415513643902059 4774548720623270465853089)
          ·
            refine ⟨3580911540467452849389817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4774548720623270465853089 3580911540467452849389817)
            ·
              refine ⟨2685683655350589637042363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3580911540467452849389817 2685683655350589637042363)
              ·
                refine ⟨4028525483025884455563545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685683655350589637042363 4028525483025884455563545)
                ·
                  refine ⟨3021394112269413341672659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4028525483025884455563545 3021394112269413341672659)
                  ·
                    refine ⟨4532091168404120012508989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3021394112269413341672659 4532091168404120012508989)
                    ·
                      refine ⟨1699534188151545004690871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4532091168404120012508989 1699534188151545004690871)
                      ·
                        rfl

theorem cell23_3309831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3309831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309831 prefixEnd_3309831 := by exact prefixLift 3309831
  have htrace : WordTrace (prefixWord ++ tailWord_3309831) baseStart_3309831 baseEnd_3309831 := by
    simpa [prefixWord, tailWord_3309831, baseEnd_3309831] using wordTrace_append hprefix tailTrace_3309831
  have hstable : (prefixWord ++ tailWord_3309831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309831).length < 2 ^ (prefixWord ++ tailWord_3309831).sum := by decide
  have hdescent : baseEnd_3309831 < baseStart_3309831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309854 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3309854 : Nat := 118140960795 + 3309854 * 2 ^ 59
def prefixEnd_3309854 : Nat := 4983230072969 + 3 ^ 40 * 3309854 * 2
def baseEnd_3309854 : Nat := 1699545998206598414703265

theorem tailTrace_3309854 : CollatzResearch.WordTrace tailWord_3309854 prefixEnd_3309854 1699545998206598414703265 := by
  unfold tailWord_3309854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090036618871463863028077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80480195300647807269483077 15090036618871463863028077)
  ·
    refine ⟨5658763732076798948635529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15090036618871463863028077 5658763732076798948635529)
    ·
      refine ⟨4244072799057599211476647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5658763732076798948635529 4244072799057599211476647)
      ·
        refine ⟨6366109198586398817214971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4244072799057599211476647 6366109198586398817214971)
        ·
          refine ⟨9549163797879598225822457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6366109198586398817214971 9549163797879598225822457)
          ·
            refine ⟨7161872848409698669366843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9549163797879598225822457 7161872848409698669366843)
            ·
              refine ⟨10742809272614548004050265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161872848409698669366843 10742809272614548004050265)
              ·
                refine ⟨8057106954460911003037699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10742809272614548004050265 8057106954460911003037699)
                ·
                  refine ⟨12085660431691366504556549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8057106954460911003037699 12085660431691366504556549)
                  ·
                    refine ⟨2266061330942131219604353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12085660431691366504556549 2266061330942131219604353)
                    ·
                      refine ⟨1699545998206598414703265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266061330942131219604353 1699545998206598414703265)
                      ·
                        rfl

theorem cell23_3309854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3309854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309854 prefixEnd_3309854 := by exact prefixLift 3309854
  have htrace : WordTrace (prefixWord ++ tailWord_3309854) baseStart_3309854 baseEnd_3309854 := by
    simpa [prefixWord, tailWord_3309854, baseEnd_3309854] using wordTrace_append hprefix tailTrace_3309854
  have hstable : (prefixWord ++ tailWord_3309854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309854).length < 2 ^ (prefixWord ++ tailWord_3309854).sum := by decide
  have hdescent : baseEnd_3309854 < baseStart_3309854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309933 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 8]
def baseStart_3309933 : Nat := 118140960795 + 3309933 * 2 ^ 59
def prefixEnd_3309933 : Nat := 4983230072969 + 3 ^ 40 * 3309933 * 2
def baseEnd_3309933 : Nat := 188842951464255956179489

theorem tailTrace_3309933 : CollatzResearch.WordTrace tailWord_3309933 prefixEnd_3309933 188842951464255956179489 := by
  unfold tailWord_3309933
  simp only [CollatzResearch.WordTrace]
  refine ⟨120723174317685507396350453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80482116211790338264233635 120723174317685507396350453)
  ·
    refine ⟨11317797592283016318407855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120723174317685507396350453 11317797592283016318407855)
    ·
      refine ⟨16976696388424524477611783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11317797592283016318407855 16976696388424524477611783)
      ·
        refine ⟨25465044582636786716417675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16976696388424524477611783 25465044582636786716417675)
        ·
          refine ⟨38197566873955180074626513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25465044582636786716417675 38197566873955180074626513)
          ·
            refine ⟨28648175155466385055969885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38197566873955180074626513 28648175155466385055969885)
            ·
              refine ⟨10743065683299894395988707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28648175155466385055969885 10743065683299894395988707)
              ·
                refine ⟨16114598524949841593983061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10743065683299894395988707 16114598524949841593983061)
                ·
                  refine ⟨188842951464255956179489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16114598524949841593983061 188842951464255956179489)
                  ·
                    rfl

theorem cell23_3309933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_3309933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309933 prefixEnd_3309933 := by exact prefixLift 3309933
  have htrace : WordTrace (prefixWord ++ tailWord_3309933) baseStart_3309933 baseEnd_3309933 := by
    simpa [prefixWord, tailWord_3309933, baseEnd_3309933] using wordTrace_append hprefix tailTrace_3309933
  have hstable : (prefixWord ++ tailWord_3309933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309933).length < 2 ^ (prefixWord ++ tailWord_3309933).sum := by decide
  have hdescent : baseEnd_3309933 < baseStart_3309933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309987 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 2, 3, 2]
def baseStart_3309987 : Nat := 118140960795 + 3309987 * 2 ^ 59
def prefixEnd_3309987 : Nat := 4983230072969 + 3 ^ 40 * 3309987 * 2
def baseEnd_3309987 : Nat := 1699614291133646394340153

theorem tailTrace_3309987 : CollatzResearch.WordTrace tailWord_3309987 prefixEnd_3309987 1699614291133646394340153 := by
  unfold tailWord_3309987
  simp only [CollatzResearch.WordTrace]
  refine ⟨120725143859489874618816215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80483429239659916412544143 120725143859489874618816215)
  ·
    refine ⟨181087715789234811928224323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120725143859489874618816215 181087715789234811928224323)
    ·
      refine ⟨271631573683852217892336485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181087715789234811928224323 271631573683852217892336485)
      ·
        refine ⟨50930920065722290854813091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271631573683852217892336485 50930920065722290854813091)
        ·
          refine ⟨76396380098583436282219637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50930920065722290854813091 76396380098583436282219637)
          ·
            refine ⟨7162160634242197151458091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76396380098583436282219637 7162160634242197151458091)
            ·
              refine ⟨10743240951363295727187137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7162160634242197151458091 10743240951363295727187137)
              ·
                refine ⟨8057430713522471795390353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10743240951363295727187137 8057430713522471795390353)
                ·
                  refine ⟨6043073035141853846542765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8057430713522471795390353 6043073035141853846542765)
                  ·
                    refine ⟨2266152388178195192453537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6043073035141853846542765 2266152388178195192453537)
                    ·
                      refine ⟨1699614291133646394340153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266152388178195192453537 1699614291133646394340153)
                      ·
                        rfl

theorem cell23_3309987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_3309987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3309987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3309987 prefixEnd_3309987 := by exact prefixLift 3309987
  have htrace : WordTrace (prefixWord ++ tailWord_3309987) baseStart_3309987 baseEnd_3309987 := by
    simpa [prefixWord, tailWord_3309987, baseEnd_3309987] using wordTrace_append hprefix tailTrace_3309987
  have hstable : (prefixWord ++ tailWord_3309987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309987).length < 2 ^ (prefixWord ++ tailWord_3309987).sum := by decide
  have hdescent : baseEnd_3309987 < baseStart_3309987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310003 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 3]
def baseStart_3310003 : Nat := 118140960795 + 3310003 * 2 ^ 59
def prefixEnd_3310003 : Nat := 4983230072969 + 3 ^ 40 * 3310003 * 2
def baseEnd_3310003 : Nat := 1699622506824118331740079

theorem tailTrace_3310003 : CollatzResearch.WordTrace tailWord_3310003 prefixEnd_3310003 1699622506824118331740079 := by
  unfold tailWord_3310003
  simp only [CollatzResearch.WordTrace]
  refine ⟨120725727427431909351398663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80483818284954606234265775 120725727427431909351398663)
  ·
    refine ⟨181088591141147864027097995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120725727427431909351398663 181088591141147864027097995)
    ·
      refine ⟨271632886711721796040646993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181088591141147864027097995 271632886711721796040646993)
      ·
        refine ⟨203724665033791347030485245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271632886711721796040646993 203724665033791347030485245)
        ·
          refine ⟨76396749387671755136431967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203724665033791347030485245 76396749387671755136431967)
          ·
            refine ⟨114595124081507632704647951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76396749387671755136431967 114595124081507632704647951)
            ·
              refine ⟨171892686122261449056971927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114595124081507632704647951 171892686122261449056971927)
              ·
                refine ⟨257839029183392173585457891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171892686122261449056971927 257839029183392173585457891)
                ·
                  refine ⟨386758543775088260378186837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257839029183392173585457891 386758543775088260378186837)
                  ·
                    refine ⟨4532326684864315551306877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 386758543775088260378186837 4532326684864315551306877)
                    ·
                      refine ⟨1699622506824118331740079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4532326684864315551306877 1699622506824118331740079)
                      ·
                        rfl

theorem cell23_3310003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_3310003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310003 prefixEnd_3310003 := by exact prefixLift 3310003
  have htrace : WordTrace (prefixWord ++ tailWord_3310003) baseStart_3310003 baseEnd_3310003 := by
    simpa [prefixWord, tailWord_3310003, baseEnd_3310003] using wordTrace_append hprefix tailTrace_3310003
  have hstable : (prefixWord ++ tailWord_3310003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310003).length < 2 ^ (prefixWord ++ tailWord_3310003).sum := by decide
  have hdescent : baseEnd_3310003 < baseStart_3310003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310023 : List Nat := [1, 1, 4, 1, 1, 4, 2, 9]
def baseStart_3310023 : Nat := 118140960795 + 3310023 * 2 ^ 59
def prefixEnd_3310023 : Nat := 4983230072969 + 3 ^ 40 * 3310023 * 2
def baseEnd_3310023 : Nat := 62949362090266972351481

theorem tailTrace_3310023 : CollatzResearch.WordTrace tailWord_3310023 prefixEnd_3310023 62949362090266972351481 := by
  unfold tailWord_3310023
  simp only [CollatzResearch.WordTrace]
  refine ⟨120726456887359452767126723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80484304591572968511417815 120726456887359452767126723)
  ·
    refine ⟨181089685331039179150690085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120726456887359452767126723 181089685331039179150690085)
    ·
      refine ⟨33954315999569846090754391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181089685331039179150690085 33954315999569846090754391)
      ·
        refine ⟨50931473999354769136131587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33954315999569846090754391 50931473999354769136131587)
        ·
          refine ⟨76397210999032153704197381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50931473999354769136131587 76397210999032153704197381)
          ·
            refine ⟨14324477062318528819537009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76397210999032153704197381 14324477062318528819537009)
            ·
              refine ⟨10743357796738896614652757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14324477062318528819537009 10743357796738896614652757)
              ·
                refine ⟨62949362090266972351481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10743357796738896614652757 62949362090266972351481)
                ·
                  rfl

theorem cell23_3310023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 9].length) (baseStart_3310023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310023 prefixEnd_3310023 := by exact prefixLift 3310023
  have htrace : WordTrace (prefixWord ++ tailWord_3310023) baseStart_3310023 baseEnd_3310023 := by
    simpa [prefixWord, tailWord_3310023, baseEnd_3310023] using wordTrace_append hprefix tailTrace_3310023
  have hstable : (prefixWord ++ tailWord_3310023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310023).length < 2 ^ (prefixWord ++ tailWord_3310023).sum := by decide
  have hdescent : baseEnd_3310023 < baseStart_3310023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310037 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3310037 : Nat := 118140960795 + 3310037 * 2 ^ 59
def prefixEnd_3310037 : Nat := 4983230072969 + 3 ^ 40 * 3310037 * 2
def baseEnd_3310037 : Nat := 1699639965166371198714923

theorem tailTrace_3310037 : CollatzResearch.WordTrace tailWord_3310037 prefixEnd_3310037 1699639965166371198714923 := by
  unfold tailWord_3310037
  simp only [CollatzResearch.WordTrace]
  refine ⟨120726967509308733158136365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80484645006205822105424243 120726967509308733158136365)
  ·
    refine ⟨45272612815990774934301137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120726967509308733158136365 45272612815990774934301137)
    ·
      refine ⟨33954459611993081200725853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45272612815990774934301137 33954459611993081200725853)
      ·
        refine ⟨12732922354497405450272195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33954459611993081200725853 12732922354497405450272195)
        ·
          refine ⟨19099383531746108175408293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12732922354497405450272195 19099383531746108175408293)
          ·
            refine ⟨3581134412202395282889055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19099383531746108175408293 3581134412202395282889055)
            ·
              refine ⟨5371701618303592924333583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581134412202395282889055 5371701618303592924333583)
              ·
                refine ⟨8057552427455389386500375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371701618303592924333583 8057552427455389386500375)
                ·
                  refine ⟨12086328641183084079750563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8057552427455389386500375 12086328641183084079750563)
                  ·
                    refine ⟨18129492961774626119625845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12086328641183084079750563 18129492961774626119625845)
                    ·
                      refine ⟨1699639965166371198714923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18129492961774626119625845 1699639965166371198714923)
                      ·
                        rfl

theorem cell23_3310037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3310037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310037 prefixEnd_3310037 := by exact prefixLift 3310037
  have htrace : WordTrace (prefixWord ++ tailWord_3310037) baseStart_3310037 baseEnd_3310037 := by
    simpa [prefixWord, tailWord_3310037, baseEnd_3310037] using wordTrace_append hprefix tailTrace_3310037
  have hstable : (prefixWord ++ tailWord_3310037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310037).length < 2 ^ (prefixWord ++ tailWord_3310037).sum := by decide
  have hdescent : baseEnd_3310037 < baseStart_3310037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310063 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 5]
def baseStart_3310063 : Nat := 118140960795 + 3310063 * 2 ^ 59
def prefixEnd_3310063 : Nat := 4983230072969 + 3 ^ 40 * 3310063 * 2
def baseEnd_3310063 : Nat := 1699653315663388096989803

theorem tailTrace_3310063 : CollatzResearch.WordTrace tailWord_3310063 prefixEnd_3310063 1699653315663388096989803 := by
  unfold tailWord_3310063
  simp only [CollatzResearch.WordTrace]
  refine ⟨120727915807214539598582843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80485277204809693065721895 120727915807214539598582843)
  ·
    refine ⟨181091873710821809397874265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120727915807214539598582843 181091873710821809397874265)
    ·
      refine ⟨135818905283116357048405699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181091873710821809397874265 135818905283116357048405699)
      ·
        refine ⟨203728357924674535572608549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135818905283116357048405699 203728357924674535572608549)
        ·
          refine ⟨38199067110876475419864103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203728357924674535572608549 38199067110876475419864103)
          ·
            refine ⟨57298600666314713129796155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38199067110876475419864103 57298600666314713129796155)
            ·
              refine ⟨85947900999472069694694233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57298600666314713129796155 85947900999472069694694233)
              ·
                refine ⟨64460925749604052271020675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85947900999472069694694233 64460925749604052271020675)
                ·
                  refine ⟨96691388624406078406531013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64460925749604052271020675 96691388624406078406531013)
                  ·
                    refine ⟨18129635367076139701224565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96691388624406078406531013 18129635367076139701224565)
                    ·
                      refine ⟨1699653315663388096989803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18129635367076139701224565 1699653315663388096989803)
                      ·
                        rfl

theorem cell23_3310063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_3310063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310063 prefixEnd_3310063 := by exact prefixLift 3310063
  have htrace : WordTrace (prefixWord ++ tailWord_3310063) baseStart_3310063 baseEnd_3310063 := by
    simpa [prefixWord, tailWord_3310063, baseEnd_3310063] using wordTrace_append hprefix tailTrace_3310063
  have hstable : (prefixWord ++ tailWord_3310063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310063).length < 2 ^ (prefixWord ++ tailWord_3310063).sum := by decide
  have hdescent : baseEnd_3310063 < baseStart_3310063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310067 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 3]
def baseStart_3310067 : Nat := 118140960795 + 3310067 * 2 ^ 59
def prefixEnd_3310067 : Nat := 4983230072969 + 3 ^ 40 * 3310067 * 2
def baseEnd_3310067 : Nat := 1699655369586006081339785

theorem tailTrace_3310067 : CollatzResearch.WordTrace tailWord_3310067 prefixEnd_3310067 1699655369586006081339785 := by
  unfold tailWord_3310067
  simp only [CollatzResearch.WordTrace]
  refine ⟨120728061699200048281728455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80485374466133365521152303 120728061699200048281728455)
  ·
    refine ⟨181092092548800072422592683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120728061699200048281728455 181092092548800072422592683)
    ·
      refine ⟨271638138823200108633889025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181092092548800072422592683 271638138823200108633889025)
      ·
        refine ⟨203728604117400081475416769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271638138823200108633889025 203728604117400081475416769)
        ·
          refine ⟨152796453088050061106562577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203728604117400081475416769 152796453088050061106562577)
          ·
            refine ⟨114597339816037545829921933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152796453088050061106562577 114597339816037545829921933)
            ·
              refine ⟨42974002431014079686220725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114597339816037545829921933 42974002431014079686220725)
              ·
                refine ⟨4028812727907569970583193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42974002431014079686220725 4028812727907569970583193)
                ·
                  refine ⟨3021609545930677477937395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4028812727907569970583193 3021609545930677477937395)
                  ·
                    refine ⟨4532414318896016216906093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3021609545930677477937395 4532414318896016216906093)
                    ·
                      refine ⟨1699655369586006081339785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4532414318896016216906093 1699655369586006081339785)
                      ·
                        rfl

theorem cell23_3310067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 3].length) (baseStart_3310067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310067 prefixEnd_3310067 := by exact prefixLift 3310067
  have htrace : WordTrace (prefixWord ++ tailWord_3310067) baseStart_3310067 baseEnd_3310067 := by
    simpa [prefixWord, tailWord_3310067, baseEnd_3310067] using wordTrace_append hprefix tailTrace_3310067
  have hstable : (prefixWord ++ tailWord_3310067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310067).length < 2 ^ (prefixWord ++ tailWord_3310067).sum := by decide
  have hdescent : baseEnd_3310067 < baseStart_3310067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310070 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_3310070 : Nat := 118140960795 + 3310070 * 2 ^ 59
def prefixEnd_3310070 : Nat := 4983230072969 + 3 ^ 40 * 3310070 * 2
def baseEnd_3310070 : Nat := 566552303342656523200757

theorem tailTrace_3310070 : CollatzResearch.WordTrace tailWord_3310070 prefixEnd_3310070 566552303342656523200757 := by
  unfold tailWord_3310070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7545510694886823737130479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80485447412126119862725109 7545510694886823737130479)
  ·
    refine ⟨11318266042330235605695719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7545510694886823737130479 11318266042330235605695719)
    ·
      refine ⟨16977399063495353408543579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11318266042330235605695719 16977399063495353408543579)
      ·
        refine ⟨25466098595243030112815369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16977399063495353408543579 25466098595243030112815369)
        ·
          refine ⟨19099573946432272584611527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25466098595243030112815369 19099573946432272584611527)
          ·
            refine ⟨28649360919648408876917291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19099573946432272584611527 28649360919648408876917291)
            ·
              refine ⟨42974041379472613315375937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28649360919648408876917291 42974041379472613315375937)
              ·
                refine ⟨32230531034604459986531953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42974041379472613315375937 32230531034604459986531953)
                ·
                  refine ⟨24172898275953344989898965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32230531034604459986531953 24172898275953344989898965)
                  ·
                    refine ⟨566552303342656523200757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24172898275953344989898965 566552303342656523200757)
                    ·
                      rfl

theorem cell23_3310070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_3310070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310070 prefixEnd_3310070 := by exact prefixLift 3310070
  have htrace : WordTrace (prefixWord ++ tailWord_3310070) baseStart_3310070 baseEnd_3310070 := by
    simpa [prefixWord, tailWord_3310070, baseEnd_3310070] using wordTrace_append hprefix tailTrace_3310070
  have hstable : (prefixWord ++ tailWord_3310070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310070).length < 2 ^ (prefixWord ++ tailWord_3310070).sum := by decide
  have hdescent : baseEnd_3310070 < baseStart_3310070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310077 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_3310077 : Nat := 118140960795 + 3310077 * 2 ^ 59
def prefixEnd_3310077 : Nat := 4983230072969 + 3 ^ 40 * 3310077 * 2
def baseEnd_3310077 : Nat := 1699660504392551042214739

theorem tailTrace_3310077 : CollatzResearch.WordTrace tailWord_3310077 prefixEnd_3310077 1699660504392551042214739 := by
  unfold tailWord_3310077
  simp only [CollatzResearch.WordTrace]
  refine ⟨120728426429163819989592485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80485617619442546659728323 120728426429163819989592485)
  ·
    refine ⟨22636579955468216248048591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120728426429163819989592485 22636579955468216248048591)
    ·
      refine ⟨33954869933202324372072887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22636579955468216248048591 33954869933202324372072887)
      ·
        refine ⟨50932304899803486558109331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33954869933202324372072887 50932304899803486558109331)
        ·
          refine ⟨76398457349705229837163997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50932304899803486558109331 76398457349705229837163997)
          ·
            refine ⟨28649421506139461188936499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76398457349705229837163997 28649421506139461188936499)
            ·
              refine ⟨42974132259209191783404749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28649421506139461188936499 42974132259209191783404749)
              ·
                refine ⟨16115299597203446918776781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42974132259209191783404749 16115299597203446918776781)
                ·
                  refine ⟨6043237348951292594541293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16115299597203446918776781 6043237348951292594541293)
                  ·
                    refine ⟨2266214005856734722952985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6043237348951292594541293 2266214005856734722952985)
                    ·
                      refine ⟨1699660504392551042214739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266214005856734722952985 1699660504392551042214739)
                      ·
                        rfl

theorem cell23_3310077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_3310077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310077 prefixEnd_3310077 := by exact prefixLift 3310077
  have htrace : WordTrace (prefixWord ++ tailWord_3310077) baseStart_3310077 baseEnd_3310077 := by
    simpa [prefixWord, tailWord_3310077, baseEnd_3310077] using wordTrace_append hprefix tailTrace_3310077
  have hstable : (prefixWord ++ tailWord_3310077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310077).length < 2 ^ (prefixWord ++ tailWord_3310077).sum := by decide
  have hdescent : baseEnd_3310077 < baseStart_3310077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310083 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 1, 8]
def baseStart_3310083 : Nat := 118140960795 + 3310083 * 2 ^ 59
def prefixEnd_3310083 : Nat := 4983230072969 + 3 ^ 40 * 3310083 * 2
def baseEnd_3310083 : Nat := 566554528425492672913237

theorem tailTrace_3310083 : CollatzResearch.WordTrace tailWord_3310083 prefixEnd_3310083 566554528425492672913237 := by
  unfold tailWord_3310083
  simp only [CollatzResearch.WordTrace]
  refine ⟨120728645267142083014310903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80485763511428055342873935 120728645267142083014310903)
  ·
    refine ⟨181092967900713124521466355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120728645267142083014310903 181092967900713124521466355)
    ·
      refine ⟨271639451851069686782199533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181092967900713124521466355 271639451851069686782199533)
      ·
        refine ⟨101864794444151132543324825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271639451851069686782199533 101864794444151132543324825)
        ·
          refine ⟨76398595833113349407493619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101864794444151132543324825 76398595833113349407493619)
          ·
            refine ⟨114597893749670024111240429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76398595833113349407493619 114597893749670024111240429)
            ·
              refine ⟨42974210156126259041715161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114597893749670024111240429 42974210156126259041715161)
              ·
                refine ⟨32230657617094694281286371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42974210156126259041715161 32230657617094694281286371)
                ·
                  refine ⟨48345986425642041421929557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32230657617094694281286371 48345986425642041421929557)
                  ·
                    refine ⟨566554528425492672913237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48345986425642041421929557 566554528425492672913237)
                    ·
                      rfl

theorem cell23_3310083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 8].length) (baseStart_3310083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310083 prefixEnd_3310083 := by exact prefixLift 3310083
  have htrace : WordTrace (prefixWord ++ tailWord_3310083) baseStart_3310083 baseEnd_3310083 := by
    simpa [prefixWord, tailWord_3310083, baseEnd_3310083] using wordTrace_append hprefix tailTrace_3310083
  have hstable : (prefixWord ++ tailWord_3310083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310083).length < 2 ^ (prefixWord ++ tailWord_3310083).sum := by decide
  have hdescent : baseEnd_3310083 < baseStart_3310083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310123 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9]
def baseStart_3310123 : Nat := 118140960795 + 3310123 * 2 ^ 59
def prefixEnd_3310123 : Nat := 4983230072969 + 3 ^ 40 * 3310123 * 2
def baseEnd_3310123 : Nat := 1699684124502657862239527

theorem tailTrace_3310123 : CollatzResearch.WordTrace tailWord_3310123 prefixEnd_3310123 1699684124502657862239527 := by
  unfold tailWord_3310123
  simp only [CollatzResearch.WordTrace]
  refine ⟨120730104186997169845767023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80486736124664779897178015 120730104186997169845767023)
  ·
    refine ⟨181095156280495754768650535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120730104186997169845767023 181095156280495754768650535)
    ·
      refine ⟨271642734420743632152975803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181095156280495754768650535 271642734420743632152975803)
      ·
        refine ⟨407464101631115448229463705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271642734420743632152975803 407464101631115448229463705)
        ·
          refine ⟨305598076223336586172097779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407464101631115448229463705 305598076223336586172097779)
          ·
            refine ⟨458397114335004879258146669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305598076223336586172097779 458397114335004879258146669)
            ·
              refine ⟨171898917875626829721805001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458397114335004879258146669 171898917875626829721805001)
              ·
                refine ⟨128924188406720122291353751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171898917875626829721805001 128924188406720122291353751)
                ·
                  refine ⟨193386282610080183437030627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128924188406720122291353751 193386282610080183437030627)
                  ·
                    refine ⟨290079423915120275155545941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193386282610080183437030627 290079423915120275155545941)
                    ·
                      refine ⟨1699684124502657862239527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 290079423915120275155545941 1699684124502657862239527)
                      ·
                        rfl

theorem cell23_3310123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_3310123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310123 prefixEnd_3310123 := by exact prefixLift 3310123
  have htrace : WordTrace (prefixWord ++ tailWord_3310123) baseStart_3310123 baseEnd_3310123 := by
    simpa [prefixWord, tailWord_3310123, baseEnd_3310123] using wordTrace_append hprefix tailTrace_3310123
  have hstable : (prefixWord ++ tailWord_3310123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310123).length < 2 ^ (prefixWord ++ tailWord_3310123).sum := by decide
  have hdescent : baseEnd_3310123 < baseStart_3310123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310124 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 2, 2, 2]
def baseStart_3310124 : Nat := 118140960795 + 3310124 * 2 ^ 59
def prefixEnd_3310124 : Nat := 4983230072969 + 3 ^ 40 * 3310124 * 2
def baseEnd_3310124 : Nat := 1699684637983312358327023

theorem tailTrace_3310124 : CollatzResearch.WordTrace tailWord_3310124 prefixEnd_3310124 1699684637983312358327023 := by
  unfold tailWord_3310124
  simp only [CollatzResearch.WordTrace]
  refine ⟨60365070329996773508276713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80486760439995698011035617 60365070329996773508276713)
  ·
    refine ⟨45273802747497580131207535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60365070329996773508276713 45273802747497580131207535)
    ·
      refine ⟨67910704121246370196811303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45273802747497580131207535 67910704121246370196811303)
      ·
        refine ⟨101866056181869555295216955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67910704121246370196811303 101866056181869555295216955)
        ·
          refine ⟨152799084272804332942825433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101866056181869555295216955 152799084272804332942825433)
          ·
            refine ⟨114599313204603249707119075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152799084272804332942825433 114599313204603249707119075)
            ·
              refine ⟨171898969806904874560678613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114599313204603249707119075 171898969806904874560678613)
              ·
                refine ⟨4028882104849332997515905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171898969806904874560678613 4028882104849332997515905)
                ·
                  refine ⟨3021661578636999748136929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4028882104849332997515905 3021661578636999748136929)
                  ·
                    refine ⟨2266246183977749811102697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3021661578636999748136929 2266246183977749811102697)
                    ·
                      refine ⟨1699684637983312358327023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266246183977749811102697 1699684637983312358327023)
                      ·
                        rfl

theorem cell23_3310124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_3310124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310124 prefixEnd_3310124 := by exact prefixLift 3310124
  have htrace : WordTrace (prefixWord ++ tailWord_3310124) baseStart_3310124 baseEnd_3310124 := by
    simpa [prefixWord, tailWord_3310124, baseEnd_3310124] using wordTrace_append hprefix tailTrace_3310124
  have hstable : (prefixWord ++ tailWord_3310124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310124).length < 2 ^ (prefixWord ++ tailWord_3310124).sum := by decide
  have hdescent : baseEnd_3310124 < baseStart_3310124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310130 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 7]
def baseStart_3310130 : Nat := 118140960795 + 3310130 * 2 ^ 59
def prefixEnd_3310130 : Nat := 4983230072969 + 3 ^ 40 * 3310130 * 2
def baseEnd_3310130 : Nat := 188854190985248814983555

theorem tailTrace_3310130 : CollatzResearch.WordTrace tailWord_3310130 prefixEnd_3310130 188854190985248814983555 := by
  unfold tailWord_3310130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30182589874492952510317961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80486906331981206694181229 30182589874492952510317961)
  ·
    refine ⟨22636942405869714382738471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30182589874492952510317961 22636942405869714382738471)
    ·
      refine ⟨33955413608804571574107707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22636942405869714382738471 33955413608804571574107707)
      ·
        refine ⟨50933120413206857361161561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33955413608804571574107707 50933120413206857361161561)
        ·
          refine ⟨38199840309905143020871171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50933120413206857361161561 38199840309905143020871171)
          ·
            refine ⟨57299760464857714531306757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38199840309905143020871171 57299760464857714531306757)
            ·
              refine ⟨10743705087160821474620017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57299760464857714531306757 10743705087160821474620017)
              ·
                refine ⟨8057778815370616105965013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10743705087160821474620017 8057778815370616105965013)
                ·
                  refine ⟨188854190985248814983555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8057778815370616105965013 188854190985248814983555)
                  ·
                    rfl

theorem cell23_3310130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_3310130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310130 prefixEnd_3310130 := by exact prefixLift 3310130
  have htrace : WordTrace (prefixWord ++ tailWord_3310130) baseStart_3310130 baseEnd_3310130 := by
    simpa [prefixWord, tailWord_3310130, baseEnd_3310130] using wordTrace_append hprefix tailTrace_3310130
  have hstable : (prefixWord ++ tailWord_3310130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310130).length < 2 ^ (prefixWord ++ tailWord_3310130).sum := by decide
  have hdescent : baseEnd_3310130 < baseStart_3310130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310167 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 2, 5, 2]
def baseStart_3310167 : Nat := 118140960795 + 3310167 * 2 ^ 59
def prefixEnd_3310167 : Nat := 4983230072969 + 3 ^ 40 * 3310167 * 2
def baseEnd_3310167 : Nat := 1699706717651455690089325

theorem tailTrace_3310167 : CollatzResearch.WordTrace tailWord_3310167 prefixEnd_3310167 1699706717651455690089325 := by
  unfold tailWord_3310167
  simp only [CollatzResearch.WordTrace]
  refine ⟨120731708998837765360368755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80487805999225176906912503 120731708998837765360368755)
  ·
    refine ⟨181097563498256648040553133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120731708998837765360368755 181097563498256648040553133)
    ·
      refine ⟨67911586311846243015207425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181097563498256648040553133 67911586311846243015207425)
      ·
        refine ⟨50933689733884682261405569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67911586311846243015207425 50933689733884682261405569)
        ·
          refine ⟨38200267300413511696054177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50933689733884682261405569 38200267300413511696054177)
          ·
            refine ⟨28650200475310133772040633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38200267300413511696054177 28650200475310133772040633)
            ·
              refine ⟨21487650356482600329030475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28650200475310133772040633 21487650356482600329030475)
              ·
                refine ⟨32231475534723900493545713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21487650356482600329030475 32231475534723900493545713)
                ·
                  refine ⟨24173606651042925370159285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32231475534723900493545713 24173606651042925370159285)
                  ·
                    refine ⟨2266275623535274253452433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24173606651042925370159285 2266275623535274253452433)
                    ·
                      refine ⟨1699706717651455690089325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266275623535274253452433 1699706717651455690089325)
                      ·
                        rfl

theorem cell23_3310167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_3310167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310167 prefixEnd_3310167 := by exact prefixLift 3310167
  have htrace : WordTrace (prefixWord ++ tailWord_3310167) baseStart_3310167 baseEnd_3310167 := by
    simpa [prefixWord, tailWord_3310167, baseEnd_3310167] using wordTrace_append hprefix tailTrace_3310167
  have hstable : (prefixWord ++ tailWord_3310167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310167).length < 2 ^ (prefixWord ++ tailWord_3310167).sum := by decide
  have hdescent : baseEnd_3310167 < baseStart_3310167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310194 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3310194 : Nat := 118140960795 + 3310194 * 2 ^ 59
def prefixEnd_3310194 : Nat := 4983230072969 + 3 ^ 40 * 3310194 * 2
def baseEnd_3310194 : Nat := 566573527209709028150567

theorem tailTrace_3310194 : CollatzResearch.WordTrace tailWord_3310194 prefixEnd_3310194 566573527209709028150567 := by
  unfold tailWord_3310194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30183173442434987242900409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80488462513159965981067757 30183173442434987242900409)
  ·
    refine ⟨22637380081826240432175307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30183173442434987242900409 22637380081826240432175307)
    ·
      refine ⟨33956070122739360648262961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22637380081826240432175307 33956070122739360648262961)
      ·
        refine ⟨25467052592054520486197221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33956070122739360648262961 25467052592054520486197221)
        ·
          refine ⟨4775072361010222591161979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25467052592054520486197221 4775072361010222591161979)
          ·
            refine ⟨7162608541515333886742969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775072361010222591161979 7162608541515333886742969)
            ·
              refine ⟨5371956406136500415057227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7162608541515333886742969 5371956406136500415057227)
              ·
                refine ⟨8057934609204750622585841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371956406136500415057227 8057934609204750622585841)
                ·
                  refine ⟨6043450956903562966939381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8057934609204750622585841 6043450956903562966939381)
                  ·
                    refine ⟨566573527209709028150567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6043450956903562966939381 566573527209709028150567)
                    ·
                      rfl

theorem cell23_3310194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3310194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310194 prefixEnd_3310194 := by exact prefixLift 3310194
  have htrace : WordTrace (prefixWord ++ tailWord_3310194) baseStart_3310194 baseEnd_3310194 := by
    simpa [prefixWord, tailWord_3310194, baseEnd_3310194] using wordTrace_append hprefix tailTrace_3310194
  have hstable : (prefixWord ++ tailWord_3310194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310194).length < 2 ^ (prefixWord ++ tailWord_3310194).sum := by decide
  have hdescent : baseEnd_3310194 < baseStart_3310194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310237 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 6]
def baseStart_3310237 : Nat := 118140960795 + 3310237 * 2 ^ 59
def prefixEnd_3310237 : Nat := 4983230072969 + 3 ^ 40 * 3310237 * 2
def baseEnd_3310237 : Nat := 188860295699696712912667

theorem tailTrace_3310237 : CollatzResearch.WordTrace tailWord_3310237 prefixEnd_3310237 188860295699696712912667 := by
  unfold tailWord_3310237
  simp only [CollatzResearch.WordTrace]
  refine ⟨120734262108584167315416965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80489508072389444876944643 120734262108584167315416965)
  ·
    refine ⟨22637674145359531371640681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120734262108584167315416965 22637674145359531371640681)
    ·
      refine ⟨16978255609019648528730511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22637674145359531371640681 16978255609019648528730511)
      ·
        refine ⟨25467383413529472793095767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16978255609019648528730511 25467383413529472793095767)
        ·
          refine ⟨38201075120294209189643651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25467383413529472793095767 38201075120294209189643651)
          ·
            refine ⟨57301612680441313784465477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38201075120294209189643651 57301612680441313784465477)
            ·
              refine ⟨10744052377582746334587277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57301612680441313784465477 10744052377582746334587277)
              ·
                refine ⟨4029019641593529875470229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10744052377582746334587277 4029019641593529875470229)
                ·
                  refine ⟨188860295699696712912667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4029019641593529875470229 188860295699696712912667)
                  ·
                    rfl

theorem cell23_3310237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_3310237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310237 prefixEnd_3310237 := by exact prefixLift 3310237
  have htrace : WordTrace (prefixWord ++ tailWord_3310237) baseStart_3310237 baseEnd_3310237 := by
    simpa [prefixWord, tailWord_3310237, baseEnd_3310237] using wordTrace_append hprefix tailTrace_3310237
  have hstable : (prefixWord ++ tailWord_3310237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310237).length < 2 ^ (prefixWord ++ tailWord_3310237).sum := by decide
  have hdescent : baseEnd_3310237 < baseStart_3310237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310334 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3310334 : Nat := 118140960795 + 3310334 * 2 ^ 59
def prefixEnd_3310334 : Nat := 4983230072969 + 3 ^ 40 * 3310334 * 2
def baseEnd_3310334 : Nat := 1699792468920756536701057

theorem tailTrace_3310334 : CollatzResearch.WordTrace tailWord_3310334 prefixEnd_3310334 1699792468920756536701057 := by
  unfold tailWord_3310334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092224998654094110212257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80491866659488501921132037 15092224998654094110212257)
  ·
    refine ⟨11319168748990570582659193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15092224998654094110212257 11319168748990570582659193)
    ·
      refine ⟨8489376561742927936994395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11319168748990570582659193 8489376561742927936994395)
      ·
        refine ⟨12734064842614391905491593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489376561742927936994395 12734064842614391905491593)
        ·
          refine ⟨9550548631960793929118695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12734064842614391905491593 9550548631960793929118695)
          ·
            refine ⟨14325822947941190893678043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550548631960793929118695 14325822947941190893678043)
            ·
              refine ⟨21488734421911786340517065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14325822947941190893678043 21488734421911786340517065)
              ·
                refine ⟨16116550816433839755387799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21488734421911786340517065 16116550816433839755387799)
                ·
                  refine ⟨24174826224650759633081699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16116550816433839755387799 24174826224650759633081699)
                  ·
                    refine ⟨36262239336976139449622549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24174826224650759633081699 36262239336976139449622549)
                    ·
                      refine ⟨1699792468920756536701057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36262239336976139449622549 1699792468920756536701057)
                      ·
                        rfl

theorem cell23_3310334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3310334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310334 prefixEnd_3310334 := by exact prefixLift 3310334
  have htrace : WordTrace (prefixWord ++ tailWord_3310334) baseStart_3310334 baseEnd_3310334 := by
    simpa [prefixWord, tailWord_3310334, baseEnd_3310334] using wordTrace_append hprefix tailTrace_3310334
  have hstable : (prefixWord ++ tailWord_3310334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310334).length < 2 ^ (prefixWord ++ tailWord_3310334).sum := by decide
  have hdescent : baseEnd_3310334 < baseStart_3310334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310428 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3310428 : Nat := 118140960795 + 3310428 * 2 ^ 59
def prefixEnd_3310428 : Nat := 4983230072969 + 3 ^ 40 * 3310428 * 2
def baseEnd_3310428 : Nat := 1699840736102279168925625

theorem tailTrace_3310428 : CollatzResearch.WordTrace tailWord_3310428 prefixEnd_3310428 1699840736102279168925625 := by
  unfold tailWord_3310428
  simp only [CollatzResearch.WordTrace]
  refine ⟨60370614225446103467809969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80494152300594804623746625 60370614225446103467809969)
  ·
    refine ⟨45277960669084577600857477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60370614225446103467809969 45277960669084577600857477)
    ·
      refine ⟨8489617625453358300160777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45277960669084577600857477 8489617625453358300160777)
      ·
        refine ⟨6367213219090018725120583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8489617625453358300160777 6367213219090018725120583)
        ·
          refine ⟨9550819828635028087680875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367213219090018725120583 9550819828635028087680875)
          ·
            refine ⟨14326229742952542131521313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550819828635028087680875 14326229742952542131521313)
            ·
              refine ⟨10744672307214406598640985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14326229742952542131521313 10744672307214406598640985)
              ·
                refine ⟨8058504230410804948980739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10744672307214406598640985 8058504230410804948980739)
                ·
                  refine ⟨12087756345616207423471109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058504230410804948980739 12087756345616207423471109)
                  ·
                    refine ⟨2266454314803038891900833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12087756345616207423471109 2266454314803038891900833)
                    ·
                      refine ⟨1699840736102279168925625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266454314803038891900833 1699840736102279168925625)
                      ·
                        rfl

theorem cell23_3310428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3310428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310428 prefixEnd_3310428 := by exact prefixLift 3310428
  have htrace : WordTrace (prefixWord ++ tailWord_3310428) baseStart_3310428 baseEnd_3310428 := by
    simpa [prefixWord, tailWord_3310428, baseEnd_3310428] using wordTrace_append hprefix tailTrace_3310428
  have hstable : (prefixWord ++ tailWord_3310428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310428).length < 2 ^ (prefixWord ++ tailWord_3310428).sum := by decide
  have hdescent : baseEnd_3310428 < baseStart_3310428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310444 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 3]
def baseStart_3310444 : Nat := 118140960795 + 3310444 * 2 ^ 59
def prefixEnd_3310444 : Nat := 4983230072969 + 3 ^ 40 * 3310444 * 2
def baseEnd_3310444 : Nat := 1699848951792751106325551

theorem tailTrace_3310444 : CollatzResearch.WordTrace tailWord_3310444 prefixEnd_3310444 1699848951792751106325551 := by
  unfold tailWord_3310444
  simp only [CollatzResearch.WordTrace]
  refine ⟨60370906009417120834101193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80494541345889494445468257 60370906009417120834101193)
  ·
    refine ⟨45278179507062840625575895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60370906009417120834101193 45278179507062840625575895)
    ·
      refine ⟨67917269260594260938363843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45278179507062840625575895 67917269260594260938363843)
      ·
        refine ⟨101875903890891391407545765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67917269260594260938363843 101875903890891391407545765)
        ·
          refine ⟨19101731979542135888914831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101875903890891391407545765 19101731979542135888914831)
          ·
            refine ⟨28652597969313203833372247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19101731979542135888914831 28652597969313203833372247)
            ·
              refine ⟨42978896953969805750058371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28652597969313203833372247 42978896953969805750058371)
              ·
                refine ⟨64468345430954708625087557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42978896953969805750058371 64468345430954708625087557)
                ·
                  refine ⟨12087814768304007867203917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64468345430954708625087557 12087814768304007867203917)
                  ·
                    refine ⟨4532930538114002950201469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12087814768304007867203917 4532930538114002950201469)
                    ·
                      refine ⟨1699848951792751106325551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4532930538114002950201469 1699848951792751106325551)
                      ·
                        rfl

theorem cell23_3310444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_3310444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310444 prefixEnd_3310444 := by exact prefixLift 3310444
  have htrace : WordTrace (prefixWord ++ tailWord_3310444) baseStart_3310444 baseEnd_3310444 := by
    simpa [prefixWord, tailWord_3310444, baseEnd_3310444] using wordTrace_append hprefix tailTrace_3310444
  have hstable : (prefixWord ++ tailWord_3310444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310444).length < 2 ^ (prefixWord ++ tailWord_3310444).sum := by decide
  have hdescent : baseEnd_3310444 < baseStart_3310444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310462 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3310462 : Nat := 118140960795 + 3310462 * 2 ^ 59
def prefixEnd_3310462 : Nat := 4983230072969 + 3 ^ 40 * 3310462 * 2
def baseEnd_3310462 : Nat := 1699858194444532035900469

theorem tailTrace_3310462 : CollatzResearch.WordTrace tailWord_3310462 prefixEnd_3310462 1699858194444532035900469 := by
  unfold tailWord_3310462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092808566596128842794705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80494979021846020494905093 15092808566596128842794705)
  ·
    refine ⟨11319606424947096632096029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15092808566596128842794705 11319606424947096632096029)
    ·
      refine ⟨4244852409355161237036011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11319606424947096632096029 4244852409355161237036011)
      ·
        refine ⟨6367278614032741855554017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4244852409355161237036011 6367278614032741855554017)
        ·
          refine ⟨4775458960524556391665513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6367278614032741855554017 4775458960524556391665513)
          ·
            refine ⟨3581594220393417293749135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4775458960524556391665513 3581594220393417293749135)
            ·
              refine ⟨5372391330590125940623703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581594220393417293749135 5372391330590125940623703)
              ·
                refine ⟨8058586995885188910935555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5372391330590125940623703 8058586995885188910935555)
                ·
                  refine ⟨12087880493827783366403333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058586995885188910935555 12087880493827783366403333)
                  ·
                    refine ⟨2266477592592709381200625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12087880493827783366403333 2266477592592709381200625)
                    ·
                      refine ⟨1699858194444532035900469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266477592592709381200625 1699858194444532035900469)
                      ·
                        rfl

theorem cell23_3310462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3310462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310462 prefixEnd_3310462 := by exact prefixLift 3310462
  have htrace : WordTrace (prefixWord ++ tailWord_3310462) baseStart_3310462 baseEnd_3310462 := by
    simpa [prefixWord, tailWord_3310462, baseEnd_3310462] using wordTrace_append hprefix tailTrace_3310462
  have hstable : (prefixWord ++ tailWord_3310462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310462).length < 2 ^ (prefixWord ++ tailWord_3310462).sum := by decide
  have hdescent : baseEnd_3310462 < baseStart_3310462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310551 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_3310551 : Nat := 118140960795 + 3310551 * 2 ^ 59
def prefixEnd_3310551 : Nat := 4983230072969 + 3 ^ 40 * 3310551 * 2
def baseEnd_3310551 : Nat := 1699903894222782187687559

theorem tailTrace_3310551 : CollatzResearch.WordTrace tailWord_3310551 prefixEnd_3310551 1699903894222782187687559 := by
  unfold tailWord_3310551
  simp only [CollatzResearch.WordTrace]
  refine ⟨120745714629446598942347507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80497143086297732628231671 120745714629446598942347507)
  ·
    refine ⟨181118571944169898413521261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120745714629446598942347507 181118571944169898413521261)
    ·
      refine ⟨67919464479063711905070473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181118571944169898413521261 67919464479063711905070473)
      ·
        refine ⟨50939598359297783928802855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67919464479063711905070473 50939598359297783928802855)
        ·
          refine ⟨76409397538946675893204283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50939598359297783928802855 76409397538946675893204283)
          ·
            refine ⟨114614096308420013839806425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76409397538946675893204283 114614096308420013839806425)
            ·
              refine ⟨85960572231315010379854819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114614096308420013839806425 85960572231315010379854819)
              ·
                refine ⟨128940858346972515569782229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85960572231315010379854819 128940858346972515569782229)
                ·
                  refine ⟨3022051367507168333666771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128940858346972515569782229 3022051367507168333666771)
                  ·
                    refine ⟨4533077051260752500500157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3022051367507168333666771 4533077051260752500500157)
                    ·
                      refine ⟨1699903894222782187687559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4533077051260752500500157 1699903894222782187687559)
                      ·
                        rfl

theorem cell23_3310551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_3310551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310551 prefixEnd_3310551 := by exact prefixLift 3310551
  have htrace : WordTrace (prefixWord ++ tailWord_3310551) baseStart_3310551 baseEnd_3310551 := by
    simpa [prefixWord, tailWord_3310551, baseEnd_3310551] using wordTrace_append hprefix tailTrace_3310551
  have hstable : (prefixWord ++ tailWord_3310551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310551).length < 2 ^ (prefixWord ++ tailWord_3310551).sum := by decide
  have hdescent : baseEnd_3310551 < baseStart_3310551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310561 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_3310561 : Nat := 118140960795 + 3310561 * 2 ^ 59
def prefixEnd_3310561 : Nat := 4983230072969 + 3 ^ 40 * 3310561 * 2
def baseEnd_3310561 : Nat := 1699909029029327148562513

theorem tailTrace_3310561 : CollatzResearch.WordTrace tailWord_3310561 prefixEnd_3310561 1699909029029327148562513 := by
  unfold tailWord_3310561
  simp only [CollatzResearch.WordTrace]
  refine ⟨120746079359410370650211537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80497386239606913766807691 120746079359410370650211537)
  ·
    refine ⟨90559559519557777987658653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120746079359410370650211537 90559559519557777987658653)
    ·
      refine ⟨33959834819834166745371995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90559559519557777987658653 33959834819834166745371995)
      ·
        refine ⟨50939752229751250118057993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33959834819834166745371995 50939752229751250118057993)
        ·
          refine ⟨38204814172313437588543495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50939752229751250118057993 38204814172313437588543495)
          ·
            refine ⟨57307221258470156382815243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38204814172313437588543495 57307221258470156382815243)
            ·
              refine ⟨85960831887705234574222865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57307221258470156382815243 85960831887705234574222865)
              ·
                refine ⟨64470623915778925930667149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85960831887705234574222865 64470623915778925930667149)
                ·
                  refine ⟨24176483968417097224000181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64470623915778925930667149 24176483968417097224000181)
                  ·
                    refine ⟨2266545372039102864750017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24176483968417097224000181 2266545372039102864750017)
                    ·
                      refine ⟨1699909029029327148562513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266545372039102864750017 1699909029029327148562513)
                      ·
                        rfl

theorem cell23_3310561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_3310561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310561 prefixEnd_3310561 := by exact prefixLift 3310561
  have htrace : WordTrace (prefixWord ++ tailWord_3310561) baseStart_3310561 baseEnd_3310561 := by
    simpa [prefixWord, tailWord_3310561, baseEnd_3310561] using wordTrace_append hprefix tailTrace_3310561
  have hstable : (prefixWord ++ tailWord_3310561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310561).length < 2 ^ (prefixWord ++ tailWord_3310561).sum := by decide
  have hdescent : baseEnd_3310561 < baseStart_3310561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310562 : List Nat := [3, 3, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3310562 : Nat := 118140960795 + 3310562 * 2 ^ 59
def prefixEnd_3310562 : Nat := 4983230072969 + 3 ^ 40 * 3310562 * 2
def baseEnd_3310562 : Nat := 566636514169993881550003

theorem tailTrace_3310562 : CollatzResearch.WordTrace tailWord_3310562 prefixEnd_3310562 566636514169993881550003 := by
  unfold tailWord_3310562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30186528958101686955249485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80497410554937831880665293 30186528958101686955249485)
  ·
    refine ⟨11319948359288132608218557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30186528958101686955249485 11319948359288132608218557)
    ·
      refine ⟨4244980634733049728081959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11319948359288132608218557 4244980634733049728081959)
      ·
        refine ⟨6367470952099574592122939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4244980634733049728081959 6367470952099574592122939)
        ·
          refine ⟨9551206428149361888184409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367470952099574592122939 9551206428149361888184409)
          ·
            refine ⟨7163404821112021416138307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9551206428149361888184409 7163404821112021416138307)
            ·
              refine ⟨10745107231668032124207461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163404821112021416138307 10745107231668032124207461)
              ·
                refine ⟨2014707605937756023288899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10745107231668032124207461 2014707605937756023288899)
                ·
                  refine ⟨3022061408906634034933349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014707605937756023288899 3022061408906634034933349)
                  ·
                    refine ⟨566636514169993881550003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3022061408906634034933349 566636514169993881550003)
                    ·
                      rfl

theorem cell23_3310562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3310562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310562 prefixEnd_3310562 := by exact prefixLift 3310562
  have htrace : WordTrace (prefixWord ++ tailWord_3310562) baseStart_3310562 baseEnd_3310562 := by
    simpa [prefixWord, tailWord_3310562, baseEnd_3310562] using wordTrace_append hprefix tailTrace_3310562
  have hstable : (prefixWord ++ tailWord_3310562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310562).length < 2 ^ (prefixWord ++ tailWord_3310562).sum := by decide
  have hdescent : baseEnd_3310562 < baseStart_3310562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310602 : List Nat := [3, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_3310602 : Nat := 118140960795 + 3310602 * 2 ^ 59
def prefixEnd_3310602 : Nat := 4983230072969 + 3 ^ 40 * 3310602 * 2
def baseEnd_3310602 : Nat := 1699930081736161488149825

theorem tailTrace_3310602 : CollatzResearch.WordTrace tailWord_3310602 prefixEnd_3310602 1699930081736161488149825 := by
  unfold tailWord_3310602
  simp only [CollatzResearch.WordTrace]
  refine ⟨30186893688065458663113515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80498383168174556434969373 30186893688065458663113515)
  ·
    refine ⟨45280340532098187994670273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30186893688065458663113515 45280340532098187994670273)
    ·
      refine ⟨33960255399073640996002705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45280340532098187994670273 33960255399073640996002705)
      ·
        refine ⟨25470191549305230747002029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33960255399073640996002705 25470191549305230747002029)
        ·
          refine ⟨9551321830989461530125761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25470191549305230747002029 9551321830989461530125761)
          ·
            refine ⟨7163491373242096147594321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9551321830989461530125761 7163491373242096147594321)
            ·
              refine ⟨5372618529931572110695741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7163491373242096147594321 5372618529931572110695741)
              ·
                refine ⟨2014731948724339541510903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5372618529931572110695741 2014731948724339541510903)
                ·
                  refine ⟨3022097923086509312266355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014731948724339541510903 3022097923086509312266355)
                  ·
                    refine ⟨4533146884629763968399533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3022097923086509312266355 4533146884629763968399533)
                    ·
                      refine ⟨1699930081736161488149825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4533146884629763968399533 1699930081736161488149825)
                      ·
                        rfl

theorem cell23_3310602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_3310602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310602 prefixEnd_3310602 := by exact prefixLift 3310602
  have htrace : WordTrace (prefixWord ++ tailWord_3310602) baseStart_3310602 baseEnd_3310602 := by
    simpa [prefixWord, tailWord_3310602, baseEnd_3310602] using wordTrace_append hprefix tailTrace_3310602
  have hstable : (prefixWord ++ tailWord_3310602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310602).length < 2 ^ (prefixWord ++ tailWord_3310602).sum := by decide
  have hdescent : baseEnd_3310602 < baseStart_3310602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310625 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_3310625 : Nat := 118140960795 + 3310625 * 2 ^ 59
def prefixEnd_3310625 : Nat := 4983230072969 + 3 ^ 40 * 3310625 * 2
def baseEnd_3310625 : Nat := 1699941891791214898162219

theorem tailTrace_3310625 : CollatzResearch.WordTrace tailWord_3310625 prefixEnd_3310625 1699941891791214898162219 := by
  unfold tailWord_3310625
  simp only [CollatzResearch.WordTrace]
  refine ⟨120748413631178509580541329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80498942420785673053694219 120748413631178509580541329)
  ·
    refine ⟨90561310223383882185405997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120748413631178509580541329 90561310223383882185405997)
    ·
      refine ⟨33960491333768955819527249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90561310223383882185405997 33960491333768955819527249)
      ·
        refine ⟨25470368500326716864645437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33960491333768955819527249 25470368500326716864645437)
        ·
          refine ⟨9551388187622518824242039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25470368500326716864645437 9551388187622518824242039)
          ·
            refine ⟨14327082281433778236363059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9551388187622518824242039 14327082281433778236363059)
            ·
              refine ⟨21490623422150667354544589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14327082281433778236363059 21490623422150667354544589)
              ·
                refine ⟨8058983783306500257954221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21490623422150667354544589 8058983783306500257954221)
                ·
                  refine ⟨3022118918739937596732833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8058983783306500257954221 3022118918739937596732833)
                  ·
                    refine ⟨2266589189054953197549625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3022118918739937596732833 2266589189054953197549625)
                    ·
                      refine ⟨1699941891791214898162219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2266589189054953197549625 1699941891791214898162219)
                      ·
                        rfl

theorem cell23_3310625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_3310625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310625 prefixEnd_3310625 := by exact prefixLift 3310625
  have htrace : WordTrace (prefixWord ++ tailWord_3310625) baseStart_3310625 baseEnd_3310625 := by
    simpa [prefixWord, tailWord_3310625, baseEnd_3310625] using wordTrace_append hprefix tailTrace_3310625
  have hstable : (prefixWord ++ tailWord_3310625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310625).length < 2 ^ (prefixWord ++ tailWord_3310625).sum := by decide
  have hdescent : baseEnd_3310625 < baseStart_3310625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310628 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3310628 : Nat := 118140960795 + 3310628 * 2 ^ 59
def prefixEnd_3310628 : Nat := 4983230072969 + 3 ^ 40 * 3310628 * 2
def baseEnd_3310628 : Nat := 1699943432233178386424705

theorem tailTrace_3310628 : CollatzResearch.WordTrace tailWord_3310628 prefixEnd_3310628 1699943432233178386424705 := by
  unfold tailWord_3310628
  simp only [CollatzResearch.WordTrace]
  refine ⟨60374261525083820546450269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80499015366778427395267025 60374261525083820546450269)
  ·
    refine ⟨22640348071906432704918851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60374261525083820546450269 22640348071906432704918851)
    ·
      refine ⟨33960522107859649057378277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22640348071906432704918851 33960522107859649057378277)
      ·
        refine ⟨6367597895223684198258427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33960522107859649057378277 6367597895223684198258427)
        ·
          refine ⟨9551396842835526297387641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367597895223684198258427 9551396842835526297387641)
          ·
            refine ⟨7163547632126644723040731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9551396842835526297387641 7163547632126644723040731)
            ·
              refine ⟨10745321448189967084561097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163547632126644723040731 10745321448189967084561097)
              ·
                refine ⟨8058991086142475313420823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10745321448189967084561097 8058991086142475313420823)
                ·
                  refine ⟨12088486629213712970131235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058991086142475313420823 12088486629213712970131235)
                  ·
                    refine ⟨18132729943820569455196853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12088486629213712970131235 18132729943820569455196853)
                    ·
                      refine ⟨1699943432233178386424705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18132729943820569455196853 1699943432233178386424705)
                      ·
                        rfl

theorem cell23_3310628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3310628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3310628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3310628 prefixEnd_3310628 := by exact prefixLift 3310628
  have htrace : WordTrace (prefixWord ++ tailWord_3310628) baseStart_3310628 baseEnd_3310628 := by
    simpa [prefixWord, tailWord_3310628, baseEnd_3310628] using wordTrace_append hprefix tailTrace_3310628
  have hstable : (prefixWord ++ tailWord_3310628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310628).length < 2 ^ (prefixWord ++ tailWord_3310628).sum := by decide
  have hdescent : baseEnd_3310628 < baseStart_3310628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
