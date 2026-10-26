import V185TrunkScan22Chunk386

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3451223 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 2, 3]
def baseStart_3451223 : Nat := 118140960795 + 3451223 * 2 ^ 59
def prefixEnd_3451223 : Nat := 4983230072969 + 3 ^ 40 * 3451223 * 2
def baseEnd_3451223 : Nat := 1181424163234703871893747

theorem tailTrace_3451223 : CollatzResearch.WordTrace tailWord_3451223 prefixEnd_3451223 1181424163234703871893747 := by
  unfold tailWord_3451223
  simp only [CollatzResearch.WordTrace]
  refine ⟨125876443975815967807230323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83917629317210645204820215 125876443975815967807230323)
  ·
    refine ⟨188814665963723951710845485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125876443975815967807230323 188814665963723951710845485)
    ·
      refine ⟨70805499736396481891567057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188814665963723951710845485 70805499736396481891567057)
      ·
        refine ⟨53104124802297361418675293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70805499736396481891567057 53104124802297361418675293)
        ·
          refine ⟨19914046800861510532003235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53104124802297361418675293 19914046800861510532003235)
          ·
            refine ⟨29871070201292265798004853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19914046800861510532003235 29871070201292265798004853)
            ·
              refine ⟨2800412831371149918562955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29871070201292265798004853 2800412831371149918562955)
              ·
                refine ⟨4200619247056724877844433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800412831371149918562955 4200619247056724877844433)
                ·
                  refine ⟨3150464435292543658383325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200619247056724877844433 3150464435292543658383325)
                  ·
                    refine ⟨1181424163234703871893747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3150464435292543658383325 1181424163234703871893747)
                    ·
                      rfl

theorem cell22_3451223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_3451223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451223 prefixEnd_3451223 := by exact prefixLift 3451223
  have htrace : WordTrace (prefixWord ++ tailWord_3451223) baseStart_3451223 baseEnd_3451223 := by
    simpa [prefixWord, tailWord_3451223, baseEnd_3451223] using wordTrace_append hprefix tailTrace_3451223
  have hstable : (prefixWord ++ tailWord_3451223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451223).length < 2 ^ (prefixWord ++ tailWord_3451223).sum := by decide
  have hdescent : baseEnd_3451223 < baseStart_3451223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451274 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_3451274 : Nat := 118140960795 + 3451274 * 2 ^ 59
def prefixEnd_3451274 : Nat := 4983230072969 + 3 ^ 40 * 3451274 * 2
def baseEnd_3451274 : Nat := 1181441621576956738868591

theorem tailTrace_3451274 : CollatzResearch.WordTrace tailWord_3451274 prefixEnd_3451274 1181441621576956738868591 := by
  unfold tailWord_3451274
  simp only [CollatzResearch.WordTrace]
  refine ⟨31469576024657800879334219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83918869399087469011557917 31469576024657800879334219)
  ·
    refine ⟨47204364036986701319001329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31469576024657800879334219 47204364036986701319001329)
    ·
      refine ⟨35403273027740025989250997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47204364036986701319001329 35403273027740025989250997)
      ·
        refine ⟨3319056846350627436492281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35403273027740025989250997 3319056846350627436492281)
        ·
          refine ⟨2489292634762970577369211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3319056846350627436492281 2489292634762970577369211)
          ·
            refine ⟨3733938952144455866053817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2489292634762970577369211 3733938952144455866053817)
            ·
              refine ⟨2800454214108341899540363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3733938952144455866053817 2800454214108341899540363)
              ·
                refine ⟨4200681321162512849310545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800454214108341899540363 4200681321162512849310545)
                ·
                  refine ⟨3150510990871884636982909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200681321162512849310545 3150510990871884636982909)
                  ·
                    refine ⟨1181441621576956738868591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3150510990871884636982909 1181441621576956738868591)
                    ·
                      rfl

theorem cell22_3451274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_3451274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451274 prefixEnd_3451274 := by exact prefixLift 3451274
  have htrace : WordTrace (prefixWord ++ tailWord_3451274) baseStart_3451274 baseEnd_3451274 := by
    simpa [prefixWord, tailWord_3451274, baseEnd_3451274] using wordTrace_append hprefix tailTrace_3451274
  have hstable : (prefixWord ++ tailWord_3451274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451274).length < 2 ^ (prefixWord ++ tailWord_3451274).sum := by decide
  have hdescent : baseEnd_3451274 < baseStart_3451274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451339 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 1, 6]
def baseStart_3451339 : Nat := 118140960795 + 3451339 * 2 ^ 59
def prefixEnd_3451339 : Nat := 4983230072969 + 3 ^ 40 * 3451339 * 2
def baseEnd_3451339 : Nat := 1181463872405318235993391

theorem tailTrace_3451339 : CollatzResearch.WordTrace tailWord_3451339 prefixEnd_3451339 1181463872405318235993391 := by
  unfold tailWord_3451339
  simp only [CollatzResearch.WordTrace]
  refine ⟨125880674843395719618453071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83920449895597146412302047 125880674843395719618453071)
  ·
    refine ⟨188821012265093579427679607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125880674843395719618453071 188821012265093579427679607)
    ·
      refine ⟨283231518397640369141519411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188821012265093579427679607 283231518397640369141519411)
      ·
        refine ⟨424847277596460553712279117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283231518397640369141519411 424847277596460553712279117)
        ·
          refine ⟨159317729098672707642104669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424847277596460553712279117 159317729098672707642104669)
          ·
            refine ⟨59744148412002265365789251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159317729098672707642104669 59744148412002265365789251)
            ·
              refine ⟨89616222618003398048683877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59744148412002265365789251 89616222618003398048683877)
              ·
                refine ⟨16803041740875637134128227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89616222618003398048683877 16803041740875637134128227)
                ·
                  refine ⟨25204562611313455701192341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16803041740875637134128227 25204562611313455701192341)
                  ·
                    refine ⟨1181463872405318235993391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25204562611313455701192341 1181463872405318235993391)
                    ·
                      rfl

theorem cell22_3451339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_3451339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451339 prefixEnd_3451339 := by exact prefixLift 3451339
  have htrace : WordTrace (prefixWord ++ tailWord_3451339) baseStart_3451339 baseEnd_3451339 := by
    simpa [prefixWord, tailWord_3451339, baseEnd_3451339] using wordTrace_append hprefix tailTrace_3451339
  have hstable : (prefixWord ++ tailWord_3451339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451339).length < 2 ^ (prefixWord ++ tailWord_3451339).sum := by decide
  have hdescent : baseEnd_3451339 < baseStart_3451339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451362 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3451362 : Nat := 118140960795 + 3451362 * 2 ^ 59
def prefixEnd_3451362 : Nat := 4983230072969 + 3 ^ 40 * 3451362 * 2
def baseEnd_3451362 : Nat := 1181471745775353842668321

theorem tailTrace_3451362 : CollatzResearch.WordTrace tailWord_3451362 prefixEnd_3451362 1181471745775353842668321 := by
  unfold tailWord_3451362
  simp only [CollatzResearch.WordTrace]
  refine ⟨31470378430578098636635085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83921009148208263031026893 31470378430578098636635085)
  ·
    refine ⟨11801391911466786988738157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31470378430578098636635085 11801391911466786988738157)
    ·
      refine ⟨4425521966800045120776809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11801391911466786988738157 4425521966800045120776809)
      ·
        refine ⟨3319141475100033840582607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4425521966800045120776809 3319141475100033840582607)
        ·
          refine ⟨4978712212650050760873911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319141475100033840582607 4978712212650050760873911)
          ·
            refine ⟨7468068318975076141310867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978712212650050760873911 7468068318975076141310867)
            ·
              refine ⟨11202102478462614211966301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468068318975076141310867 11202102478462614211966301)
              ·
                refine ⟨4200788429423480329487363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11202102478462614211966301 4200788429423480329487363)
                ·
                  refine ⟨6301182644135220494231045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200788429423480329487363 6301182644135220494231045)
                  ·
                    refine ⟨1181471745775353842668321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6301182644135220494231045 1181471745775353842668321)
                    ·
                      rfl

theorem cell22_3451362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3451362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451362 prefixEnd_3451362 := by exact prefixLift 3451362
  have htrace : WordTrace (prefixWord ++ tailWord_3451362) baseStart_3451362 baseEnd_3451362 := by
    simpa [prefixWord, tailWord_3451362, baseEnd_3451362] using wordTrace_append hprefix tailTrace_3451362
  have hstable : (prefixWord ++ tailWord_3451362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451362).length < 2 ^ (prefixWord ++ tailWord_3451362).sum := by decide
  have hdescent : baseEnd_3451362 < baseStart_3451362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451403 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 3, 3]
def baseStart_3451403 : Nat := 118140960795 + 3451403 * 2 ^ 59
def prefixEnd_3451403 : Nat := 4983230072969 + 3 ^ 40 * 3451403 * 2
def baseEnd_3451403 : Nat := 1181485780913243402393195

theorem tailTrace_3451403 : CollatzResearch.WordTrace tailWord_3451403 prefixEnd_3451403 1181485780913243402393195 := by
  unfold tailWord_3451403
  simp only [CollatzResearch.WordTrace]
  refine ⟨125883009115163858548782863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83922006076775905699188575 125883009115163858548782863)
  ·
    refine ⟨188824513672745787823174295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125883009115163858548782863 188824513672745787823174295)
    ·
      refine ⟨283236770509118681734761443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188824513672745787823174295 283236770509118681734761443)
      ·
        refine ⟨424855155763678022602142165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283236770509118681734761443 424855155763678022602142165)
        ·
          refine ⟨9957542713211203654737707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 424855155763678022602142165 9957542713211203654737707)
          ·
            refine ⟨14936314069816805482106561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9957542713211203654737707 14936314069816805482106561)
            ·
              refine ⟨11202235552362604111579921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14936314069816805482106561 11202235552362604111579921)
              ·
                refine ⟨8401676664271953083684941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11202235552362604111579921 8401676664271953083684941)
                ·
                  refine ⟨3150628749101982406381853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8401676664271953083684941 3150628749101982406381853)
                  ·
                    refine ⟨1181485780913243402393195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3150628749101982406381853 1181485780913243402393195)
                    ·
                      rfl

theorem cell22_3451403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 3].length) (baseStart_3451403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451403 prefixEnd_3451403 := by exact prefixLift 3451403
  have htrace : WordTrace (prefixWord ++ tailWord_3451403) baseStart_3451403 baseEnd_3451403 := by
    simpa [prefixWord, tailWord_3451403, baseEnd_3451403] using wordTrace_append hprefix tailTrace_3451403
  have hstable : (prefixWord ++ tailWord_3451403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451403).length < 2 ^ (prefixWord ++ tailWord_3451403).sum := by decide
  have hdescent : baseEnd_3451403 < baseStart_3451403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451405 : List Nat := [1, 7, 1, 1, 1, 2, 1, 8]
def baseStart_3451405 : Nat := 118140960795 + 3451405 * 2 ^ 59
def prefixEnd_3451405 : Nat := 4983230072969 + 3 ^ 40 * 3451405 * 2
def baseEnd_3451405 : Nat := 131276273950457340427021

theorem tailTrace_3451405 : CollatzResearch.WordTrace tailWord_3451405 prefixEnd_3451405 131276273950457340427021 := by
  unfold tailWord_3451405
  simp only [CollatzResearch.WordTrace]
  refine ⟨125883082061156612890355669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83922054707437741926903779 125883082061156612890355669)
  ·
    refine ⟨2950384735808358114617711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 125883082061156612890355669 2950384735808358114617711)
    ·
      refine ⟨4425577103712537171926567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950384735808358114617711 4425577103712537171926567)
      ·
        refine ⟨6638365655568805757889851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425577103712537171926567 6638365655568805757889851)
        ·
          refine ⟨9957548483353208636834777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638365655568805757889851 9957548483353208636834777)
          ·
            refine ⟨7468161362514906477626083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9957548483353208636834777 7468161362514906477626083)
            ·
              refine ⟨11202242043772359716439125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468161362514906477626083 11202242043772359716439125)
              ·
                refine ⟨131276273950457340427021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11202242043772359716439125 131276273950457340427021)
                ·
                  rfl

theorem cell22_3451405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 8].length) (baseStart_3451405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451405 prefixEnd_3451405 := by exact prefixLift 3451405
  have htrace : WordTrace (prefixWord ++ tailWord_3451405) baseStart_3451405 baseEnd_3451405 := by
    simpa [prefixWord, tailWord_3451405, baseEnd_3451405] using wordTrace_append hprefix tailTrace_3451405
  have hstable : (prefixWord ++ tailWord_3451405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451405).length < 2 ^ (prefixWord ++ tailWord_3451405).sum := by decide
  have hdescent : baseEnd_3451405 < baseStart_3451405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451416 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 7]
def baseStart_3451416 : Nat := 118140960795 + 3451416 * 2 ^ 59
def prefixEnd_3451416 : Nat := 4983230072969 + 3 ^ 40 * 3451416 * 2
def baseEnd_3451416 : Nat := 393830077026305233939385

theorem tailTrace_3451416 : CollatzResearch.WordTrace tailWord_3451416 prefixEnd_3451416 393830077026305233939385 := by
  unfold tailWord_3451416
  simp only [CollatzResearch.WordTrace]
  refine ⟨62941741632058380884503051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83922322176077841179337401 62941741632058380884503051)
  ·
    refine ⟨94412612448087571326754577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62941741632058380884503051 94412612448087571326754577)
    ·
      refine ⟨70809459336065678495065933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94412612448087571326754577 70809459336065678495065933)
      ·
        refine ⟨26553547251024629435649725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70809459336065678495065933 26553547251024629435649725)
        ·
          refine ⟨9957580219134236038368647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26553547251024629435649725 9957580219134236038368647)
          ·
            refine ⟨14936370328701354057552971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9957580219134236038368647 14936370328701354057552971)
            ·
              refine ⟨22404555493052031086329457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14936370328701354057552971 22404555493052031086329457)
              ·
                refine ⟨16803416619789023314747093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22404555493052031086329457 16803416619789023314747093)
                ·
                  refine ⟨393830077026305233939385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16803416619789023314747093 393830077026305233939385)
                  ·
                    rfl

theorem cell22_3451416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_3451416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451416 prefixEnd_3451416 := by exact prefixLift 3451416
  have htrace : WordTrace (prefixWord ++ tailWord_3451416) baseStart_3451416 baseEnd_3451416 := by
    simpa [prefixWord, tailWord_3451416, baseEnd_3451416] using wordTrace_append hprefix tailTrace_3451416
  have hstable : (prefixWord ++ tailWord_3451416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451416).length < 2 ^ (prefixWord ++ tailWord_3451416).sum := by decide
  have hdescent : baseEnd_3451416 < baseStart_3451416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451450 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_3451450 : Nat := 118140960795 + 3451450 * 2 ^ 59
def prefixEnd_3451450 : Nat := 4983230072969 + 3 ^ 40 * 3451450 * 2
def baseEnd_3451450 : Nat := 393833956657916982156017

theorem tailTrace_3451450 : CollatzResearch.WordTrace tailWord_3451450 prefixEnd_3451450 393833956657916982156017 := by
  unfold tailWord_3451450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31471180836498396393935951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83923148897329057050495869 31471180836498396393935951)
  ·
    refine ⟨47206771254747594590903927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31471180836498396393935951 47206771254747594590903927)
    ·
      refine ⟨70810156882121391886355891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47206771254747594590903927 70810156882121391886355891)
      ·
        refine ⟨106215235323182087829533837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70810156882121391886355891 106215235323182087829533837)
        ·
          refine ⟨39830713246193282936075189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106215235323182087829533837 39830713246193282936075189)
          ·
            refine ⟨3734129366830620275257049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39830713246193282936075189 3734129366830620275257049)
            ·
              refine ⟨2800597025122965206442787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3734129366830620275257049 2800597025122965206442787)
              ·
                refine ⟨4200895537684447809664181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800597025122965206442787 4200895537684447809664181)
                ·
                  refine ⟨393833956657916982156017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4200895537684447809664181 393833956657916982156017)
                  ·
                    rfl

theorem cell22_3451450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_3451450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451450 prefixEnd_3451450 := by exact prefixLift 3451450
  have htrace : WordTrace (prefixWord ++ tailWord_3451450) baseStart_3451450 baseEnd_3451450 := by
    simpa [prefixWord, tailWord_3451450, baseEnd_3451450] using wordTrace_append hprefix tailTrace_3451450
  have hstable : (prefixWord ++ tailWord_3451450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451450).length < 2 ^ (prefixWord ++ tailWord_3451450).sum := by decide
  have hdescent : baseEnd_3451450 < baseStart_3451450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451463 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3451463 : Nat := 118140960795 + 3451463 * 2 ^ 59
def prefixEnd_3451463 : Nat := 4983230072969 + 3 ^ 40 * 3451463 * 2
def baseEnd_3451463 : Nat := 1181506320139423245893011

theorem tailTrace_3451463 : CollatzResearch.WordTrace tailWord_3451463 prefixEnd_3451463 1181506320139423245893011 := by
  unfold tailWord_3451463
  simp only [CollatzResearch.WordTrace]
  refine ⟨125885197494946488795967043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83923464996630992530644695 125885197494946488795967043)
  ·
    refine ⟨188827796242419733193950565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125885197494946488795967043 188827796242419733193950565)
    ·
      refine ⟨35405211795453699973865731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188827796242419733193950565 35405211795453699973865731)
      ·
        refine ⟨53107817693180549960798597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35405211795453699973865731 53107817693180549960798597)
        ·
          refine ⟨9957715817471353117649737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53107817693180549960798597 9957715817471353117649737)
          ·
            refine ⟨7468286863103514838237303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9957715817471353117649737 7468286863103514838237303)
            ·
              refine ⟨11202430294655272257355955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468286863103514838237303 11202430294655272257355955)
              ·
                refine ⟨16803645441982908386033933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11202430294655272257355955 16803645441982908386033933)
                ·
                  refine ⟨6301367040743590644762725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16803645441982908386033933 6301367040743590644762725)
                  ·
                    refine ⟨1181506320139423245893011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6301367040743590644762725 1181506320139423245893011)
                    ·
                      rfl

theorem cell22_3451463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3451463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451463 prefixEnd_3451463 := by exact prefixLift 3451463
  have htrace : WordTrace (prefixWord ++ tailWord_3451463) baseStart_3451463 baseEnd_3451463 := by
    simpa [prefixWord, tailWord_3451463, baseEnd_3451463] using wordTrace_append hprefix tailTrace_3451463
  have hstable : (prefixWord ++ tailWord_3451463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451463).length < 2 ^ (prefixWord ++ tailWord_3451463).sum := by decide
  have hdescent : baseEnd_3451463 < baseStart_3451463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451525 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_3451525 : Nat := 118140960795 + 3451525 * 2 ^ 59
def prefixEnd_3451525 : Nat := 4983230072969 + 3 ^ 40 * 3451525 * 2
def baseEnd_3451525 : Nat := 1181527544006475750842821

theorem tailTrace_3451525 : CollatzResearch.WordTrace tailWord_3451525 prefixEnd_3451525 1181527544006475750842821 := by
  unfold tailWord_3451525
  simp only [CollatzResearch.WordTrace]
  refine ⟨125887458820721873384724029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83924972547147915589816019 125887458820721873384724029)
  ·
    refine ⟨47207797057770702519271511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125887458820721873384724029 47207797057770702519271511)
    ·
      refine ⟨70811695586656053778907267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47207797057770702519271511 70811695586656053778907267)
      ·
        refine ⟨106217543379984080668360901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70811695586656053778907267 106217543379984080668360901)
        ·
          refine ⟨19915789383747015125317669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106217543379984080668360901 19915789383747015125317669)
          ·
            refine ⟨3734210509452565335997063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19915789383747015125317669 3734210509452565335997063)
            ·
              refine ⟨5601315764178848003995595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734210509452565335997063 5601315764178848003995595)
              ·
                refine ⟨8401973646268272005993393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601315764178848003995595 8401973646268272005993393)
                ·
                  refine ⟨6301480234701204004495045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8401973646268272005993393 6301480234701204004495045)
                  ·
                    refine ⟨1181527544006475750842821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6301480234701204004495045 1181527544006475750842821)
                    ·
                      rfl

theorem cell22_3451525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_3451525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451525 prefixEnd_3451525 := by exact prefixLift 3451525
  have htrace : WordTrace (prefixWord ++ tailWord_3451525) baseStart_3451525 baseEnd_3451525 := by
    simpa [prefixWord, tailWord_3451525, baseEnd_3451525] using wordTrace_append hprefix tailTrace_3451525
  have hstable : (prefixWord ++ tailWord_3451525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451525).length < 2 ^ (prefixWord ++ tailWord_3451525).sum := by decide
  have hdescent : baseEnd_3451525 < baseStart_3451525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451574 : List Nat := [5, 1, 3, 1, 2, 2, 2, 6]
def baseStart_3451574 : Nat := 118140960795 + 3451574 * 2 ^ 59
def prefixEnd_3451574 : Nat := 4983230072969 + 3 ^ 40 * 3451574 * 2
def baseEnd_3451574 : Nat := 131282701967539550707519

theorem tailTrace_3451574 : CollatzResearch.WordTrace tailWord_3451574 prefixEnd_3451574 131282701967539550707519 := by
  unfold tailWord_3451574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7868077874846522172078611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83926163998362903168838517 7868077874846522172078611)
  ·
    refine ⟨11802116812269783258117917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7868077874846522172078611 11802116812269783258117917)
    ·
      refine ⟨4425793804601168721794219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11802116812269783258117917 4425793804601168721794219)
      ·
        refine ⟨6638690706901753082691329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425793804601168721794219 6638690706901753082691329)
        ·
          refine ⟨4979018030176314812018497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6638690706901753082691329 4979018030176314812018497)
          ·
            refine ⟨3734263522632236109013873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4979018030176314812018497 3734263522632236109013873)
            ·
              refine ⟨2800697641974177081760405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3734263522632236109013873 2800697641974177081760405)
              ·
                refine ⟨131282701967539550707519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2800697641974177081760405 131282701967539550707519)
                ·
                  rfl

theorem cell22_3451574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_3451574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451574 prefixEnd_3451574 := by exact prefixLift 3451574
  have htrace : WordTrace (prefixWord ++ tailWord_3451574) baseStart_3451574 baseEnd_3451574 := by
    simpa [prefixWord, tailWord_3451574, baseEnd_3451574] using wordTrace_append hprefix tailTrace_3451574
  have hstable : (prefixWord ++ tailWord_3451574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451574).length < 2 ^ (prefixWord ++ tailWord_3451574).sum := by decide
  have hdescent : baseEnd_3451574 < baseStart_3451574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451628 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_3451628 : Nat := 118140960795 + 3451628 * 2 ^ 59
def prefixEnd_3451628 : Nat := 4983230072969 + 3 ^ 40 * 3451628 * 2
def baseEnd_3451628 : Nat := 1181562803011417815517505

theorem tailTrace_3451628 : CollatzResearch.WordTrace tailWord_3451628 prefixEnd_3451628 1181562803011417815517505 := by
  unfold tailWord_3451628
  simp only [CollatzResearch.WordTrace]
  refine ⟨62945607769674360987861769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83927477026232481317149025 62945607769674360987861769)
  ·
    refine ⟨47209205827255770740896327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62945607769674360987861769 47209205827255770740896327)
    ·
      refine ⟨70813808740883656111344491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47209205827255770740896327 70813808740883656111344491)
      ·
        refine ⟨106220713111325484167016737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70813808740883656111344491 106220713111325484167016737)
        ·
          refine ⟨79665534833494113125262553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106220713111325484167016737 79665534833494113125262553)
          ·
            refine ⟨59749151125120584843946915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79665534833494113125262553 59749151125120584843946915)
            ·
              refine ⟨89623726687680877265920373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59749151125120584843946915 89623726687680877265920373)
              ·
                refine ⟨8402224376970082243680035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89623726687680877265920373 8402224376970082243680035)
                ·
                  refine ⟨12603336565455123365520053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8402224376970082243680035 12603336565455123365520053)
                  ·
                    refine ⟨1181562803011417815517505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12603336565455123365520053 1181562803011417815517505)
                    ·
                      rfl

theorem cell22_3451628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_3451628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451628 prefixEnd_3451628 := by exact prefixLift 3451628
  have htrace : WordTrace (prefixWord ++ tailWord_3451628) baseStart_3451628 baseEnd_3451628 := by
    simpa [prefixWord, tailWord_3451628, baseEnd_3451628] using wordTrace_append hprefix tailTrace_3451628
  have hstable : (prefixWord ++ tailWord_3451628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451628).length < 2 ^ (prefixWord ++ tailWord_3451628).sum := by decide
  have hdescent : baseEnd_3451628 < baseStart_3451628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451694 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3451694 : Nat := 118140960795 + 3451694 * 2 ^ 59
def prefixEnd_3451694 : Nat := 4983230072969 + 3 ^ 40 * 3451694 * 2
def baseEnd_3451694 : Nat := 1181585396160215643367303

theorem tailTrace_3451694 : CollatzResearch.WordTrace tailWord_3451694 prefixEnd_3451694 1181585396160215643367303 := by
  unfold tailWord_3451694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736702844638701905953267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83929081838073076831750757 15736702844638701905953267)
  ·
    refine ⟨23605054266958052858929901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15736702844638701905953267 23605054266958052858929901)
    ·
      refine ⟨8851895350109269822098713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23605054266958052858929901 8851895350109269822098713)
      ·
        refine ⟨6638921512581952366574035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8851895350109269822098713 6638921512581952366574035)
        ·
          refine ⟨9958382268872928549861053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638921512581952366574035 9958382268872928549861053)
          ·
            refine ⟨3734393350827348206197895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9958382268872928549861053 3734393350827348206197895)
            ·
              refine ⟨5601590026241022309296843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734393350827348206197895 5601590026241022309296843)
              ·
                refine ⟨8402385039361533463945265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601590026241022309296843 8402385039361533463945265)
                ·
                  refine ⟨6301788779521150097958949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8402385039361533463945265 6301788779521150097958949)
                  ·
                    refine ⟨1181585396160215643367303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6301788779521150097958949 1181585396160215643367303)
                    ·
                      rfl

theorem cell22_3451694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3451694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451694 prefixEnd_3451694 := by exact prefixLift 3451694
  have htrace : WordTrace (prefixWord ++ tailWord_3451694) baseStart_3451694 baseEnd_3451694 := by
    simpa [prefixWord, tailWord_3451694, baseEnd_3451694] using wordTrace_append hprefix tailTrace_3451694
  have hstable : (prefixWord ++ tailWord_3451694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451694).length < 2 ^ (prefixWord ++ tailWord_3451694).sum := by decide
  have hdescent : baseEnd_3451694 < baseStart_3451694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451703 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 7]
def baseStart_3451703 : Nat := 118140960795 + 3451703 * 2 ^ 59
def prefixEnd_3451703 : Nat := 4983230072969 + 3 ^ 40 * 3451703 * 2
def baseEnd_3451703 : Nat := 393862825681380873297425

theorem tailTrace_3451703 : CollatzResearch.WordTrace tailWord_3451703 prefixEnd_3451703 393862825681380873297425 := by
  unfold tailWord_3451703
  simp only [CollatzResearch.WordTrace]
  refine ⟨125893951014077009784703763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83929300676051339856469175 125893951014077009784703763)
  ·
    refine ⟨188840926521115514677055645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125893951014077009784703763 188840926521115514677055645)
    ·
      refine ⟨70815347445418318003895867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188840926521115514677055645 70815347445418318003895867)
      ·
        refine ⟨106223021168127477005843801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70815347445418318003895867 106223021168127477005843801)
        ·
          refine ⟨79667265876095607754382851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106223021168127477005843801 79667265876095607754382851)
          ·
            refine ⟨119500898814143411631574277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79667265876095607754382851 119500898814143411631574277)
            ·
              refine ⟨22406418527651889680920177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119500898814143411631574277 22406418527651889680920177)
              ·
                refine ⟨16804813895738917260690133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22406418527651889680920177 16804813895738917260690133)
                ·
                  refine ⟨393862825681380873297425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16804813895738917260690133 393862825681380873297425)
                  ·
                    rfl

theorem cell22_3451703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 7].length) (baseStart_3451703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451703 prefixEnd_3451703 := by exact prefixLift 3451703
  have htrace : WordTrace (prefixWord ++ tailWord_3451703) baseStart_3451703 baseEnd_3451703 := by
    simpa [prefixWord, tailWord_3451703, baseEnd_3451703] using wordTrace_append hprefix tailTrace_3451703
  have hstable : (prefixWord ++ tailWord_3451703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451703).length < 2 ^ (prefixWord ++ tailWord_3451703).sum := by decide
  have hdescent : baseEnd_3451703 < baseStart_3451703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451713 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3451713 : Nat := 118140960795 + 3451713 * 2 ^ 59
def prefixEnd_3451713 : Nat := 4983230072969 + 3 ^ 40 * 3451713 * 2
def baseEnd_3451713 : Nat := 1181591900248505927142245

theorem tailTrace_3451713 : CollatzResearch.WordTrace tailWord_3451713 prefixEnd_3451713 1181591900248505927142245 := by
  unfold tailWord_3451713
  simp only [CollatzResearch.WordTrace]
  refine ⟨125894315744040781492567793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83929543829360520995045195 125894315744040781492567793)
  ·
    refine ⟨94420736808030586119425845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125894315744040781492567793 94420736808030586119425845)
    ·
      refine ⟨8851944075752867448696173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94420736808030586119425845 8851944075752867448696173)
      ·
        refine ⟨3319479028407325293261065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8851944075752867448696173 3319479028407325293261065)
        ·
          refine ⟨2489609271305493969945799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3319479028407325293261065 2489609271305493969945799)
          ·
            refine ⟨3734413906958240954918699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2489609271305493969945799 3734413906958240954918699)
            ·
              refine ⟨5601620860437361432378049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734413906958240954918699 5601620860437361432378049)
              ·
                refine ⟨4201215645328021074283537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5601620860437361432378049 4201215645328021074283537)
                ·
                  refine ⟨3150911733996015805712653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4201215645328021074283537 3150911733996015805712653)
                  ·
                    refine ⟨1181591900248505927142245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3150911733996015805712653 1181591900248505927142245)
                    ·
                      rfl

theorem cell22_3451713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3451713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451713 prefixEnd_3451713 := by exact prefixLift 3451713
  have htrace : WordTrace (prefixWord ++ tailWord_3451713) baseStart_3451713 baseEnd_3451713 := by
    simpa [prefixWord, tailWord_3451713, baseEnd_3451713] using wordTrace_append hprefix tailTrace_3451713
  have hstable : (prefixWord ++ tailWord_3451713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451713).length < 2 ^ (prefixWord ++ tailWord_3451713).sum := by decide
  have hdescent : baseEnd_3451713 < baseStart_3451713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451724 : List Nat := [2, 2, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_3451724 : Nat := 118140960795 + 3451724 * 2 ^ 59
def prefixEnd_3451724 : Nat := 4983230072969 + 3 ^ 40 * 3451724 * 2
def baseEnd_3451724 : Nat := 1181595665773305565117211

theorem tailTrace_3451724 : CollatzResearch.WordTrace tailWord_3451724 prefixEnd_3451724 1181595665773305565117211 := by
  unfold tailWord_3451724
  simp only [CollatzResearch.WordTrace]
  refine ⟨62947358473500465185609113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83929811298000620247478817 62947358473500465185609113)
  ·
    refine ⟨47210518855125348889206835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62947358473500465185609113 47210518855125348889206835)
    ·
      refine ⟨70815778282688023333810253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47210518855125348889206835 70815778282688023333810253)
      ·
        refine ⟨26555916856008008750178845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70815778282688023333810253 26555916856008008750178845)
        ·
          refine ⟨9958468821003003281317067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26555916856008008750178845 9958468821003003281317067)
          ·
            refine ⟨14937703231504504921975601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958468821003003281317067 14937703231504504921975601)
            ·
              refine ⟨11203277423628378691481701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14937703231504504921975601 11203277423628378691481701)
              ·
                refine ⟨2100614516930321004652819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11203277423628378691481701 2100614516930321004652819)
                ·
                  refine ⟨3150921775395481506979229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100614516930321004652819 3150921775395481506979229)
                  ·
                    refine ⟨1181595665773305565117211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3150921775395481506979229 1181595665773305565117211)
                    ·
                      rfl

theorem cell22_3451724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_3451724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451724 prefixEnd_3451724 := by exact prefixLift 3451724
  have htrace : WordTrace (prefixWord ++ tailWord_3451724) baseStart_3451724 baseEnd_3451724 := by
    simpa [prefixWord, tailWord_3451724, baseEnd_3451724] using wordTrace_append hprefix tailTrace_3451724
  have hstable : (prefixWord ++ tailWord_3451724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451724).length < 2 ^ (prefixWord ++ tailWord_3451724).sum := by decide
  have hdescent : baseEnd_3451724 < baseStart_3451724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451735 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3451735 : Nat := 118140960795 + 3451735 * 2 ^ 59
def prefixEnd_3451735 : Nat := 4983230072969 + 3 ^ 40 * 3451735 * 2
def baseEnd_3451735 : Nat := 1181599431298105203092177

theorem tailTrace_3451735 : CollatzResearch.WordTrace tailWord_3451735 prefixEnd_3451735 1181599431298105203092177 := by
  unfold tailWord_3451735
  simp only [CollatzResearch.WordTrace]
  refine ⟨125895118149961079249868659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83930078766640719499912439 125895118149961079249868659)
  ·
    refine ⟨188842677224941618874802989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125895118149961079249868659 188842677224941618874802989)
    ·
      refine ⟨70816003959353107078051121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188842677224941618874802989 70816003959353107078051121)
      ·
        refine ⟨53112002969514830308538341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70816003959353107078051121 53112002969514830308538341)
        ·
          refine ⟨9958500556784030682850939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53112002969514830308538341 9958500556784030682850939)
          ·
            refine ⟨14937750835176046024276409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958500556784030682850939 14937750835176046024276409)
            ·
              refine ⟨11203313126382034518207307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14937750835176046024276409 11203313126382034518207307)
              ·
                refine ⟨16804969689573051777310961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11203313126382034518207307 16804969689573051777310961)
                ·
                  refine ⟨12603727267179788832983221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16804969689573051777310961 12603727267179788832983221)
                  ·
                    refine ⟨1181599431298105203092177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12603727267179788832983221 1181599431298105203092177)
                    ·
                      rfl

theorem cell22_3451735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3451735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451735 prefixEnd_3451735 := by exact prefixLift 3451735
  have htrace : WordTrace (prefixWord ++ tailWord_3451735) baseStart_3451735 baseEnd_3451735 := by
    simpa [prefixWord, tailWord_3451735, baseEnd_3451735] using wordTrace_append hprefix tailTrace_3451735
  have hstable : (prefixWord ++ tailWord_3451735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451735).length < 2 ^ (prefixWord ++ tailWord_3451735).sum := by decide
  have hdescent : baseEnd_3451735 < baseStart_3451735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451737 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 5]
def baseStart_3451737 : Nat := 118140960795 + 3451737 * 2 ^ 59
def prefixEnd_3451737 : Nat := 4983230072969 + 3 ^ 40 * 3451737 * 2
def baseEnd_3451737 : Nat := 393866705312992621514057

theorem tailTrace_3451737 : CollatzResearch.WordTrace tailWord_3451737 prefixEnd_3451737 393866705312992621514057 := by
  unfold tailWord_3451737
  simp only [CollatzResearch.WordTrace]
  refine ⟨125895191095953833591441465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83930127397302555727627643 125895191095953833591441465)
  ·
    refine ⟨94421393321965375193581099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125895191095953833591441465 94421393321965375193581099)
    ·
      refine ⟨141632089982948062790371649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94421393321965375193581099 141632089982948062790371649)
      ·
        refine ⟨106224067487211047092778737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141632089982948062790371649 106224067487211047092778737)
        ·
          refine ⟨79668050615408285319584053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106224067487211047092778737 79668050615408285319584053)
          ·
            refine ⟨7468879745194526748711005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79668050615408285319584053 7468879745194526748711005)
            ·
              refine ⟨2800829904447947530766627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7468879745194526748711005 2800829904447947530766627)
              ·
                refine ⟨4201244856671921296149941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800829904447947530766627 4201244856671921296149941)
                ·
                  refine ⟨393866705312992621514057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4201244856671921296149941 393866705312992621514057)
                  ·
                    rfl

theorem cell22_3451737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_3451737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451737 prefixEnd_3451737 := by exact prefixLift 3451737
  have htrace : WordTrace (prefixWord ++ tailWord_3451737) baseStart_3451737 baseEnd_3451737 := by
    simpa [prefixWord, tailWord_3451737, baseEnd_3451737] using wordTrace_append hprefix tailTrace_3451737
  have hstable : (prefixWord ++ tailWord_3451737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451737).length < 2 ^ (prefixWord ++ tailWord_3451737).sum := by decide
  have hdescent : baseEnd_3451737 < baseStart_3451737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451758 : List Nat := [4, 1, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3451758 : Nat := 118140960795 + 3451758 * 2 ^ 59
def prefixEnd_3451758 : Nat := 4983230072969 + 3 ^ 40 * 3451758 * 2
def baseEnd_3451758 : Nat := 1181607304668140809767107

theorem tailTrace_3451758 : CollatzResearch.WordTrace tailWord_3451758 prefixEnd_3451758 1181607304668140809767107 := by
  unfold tailWord_3451758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736994628609719272244491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83930638019251836118637285 15736994628609719272244491)
  ·
    refine ⟨23605491942914578908366737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15736994628609719272244491 23605491942914578908366737)
    ·
      refine ⟨17704118957185934181275053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23605491942914578908366737 17704118957185934181275053)
      ·
        refine ⟨6639044608944725317978145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17704118957185934181275053 6639044608944725317978145)
        ·
          refine ⟨4979283456708543988483609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6639044608944725317978145 4979283456708543988483609)
          ·
            refine ⟨3734462592531407991362707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4979283456708543988483609 3734462592531407991362707)
            ·
              refine ⟨5601693888797111987044061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734462592531407991362707 5601693888797111987044061)
              ·
                refine ⟨2100635208298916995141523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5601693888797111987044061 2100635208298916995141523)
                ·
                  refine ⟨3150952812448375492712285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100635208298916995141523 3150952812448375492712285)
                  ·
                    refine ⟨1181607304668140809767107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3150952812448375492712285 1181607304668140809767107)
                    ·
                      rfl

theorem cell22_3451758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3451758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451758 prefixEnd_3451758 := by exact prefixLift 3451758
  have htrace : WordTrace (prefixWord ++ tailWord_3451758) baseStart_3451758 baseEnd_3451758 := by
    simpa [prefixWord, tailWord_3451758, baseEnd_3451758] using wordTrace_append hprefix tailTrace_3451758
  have hstable : (prefixWord ++ tailWord_3451758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451758).length < 2 ^ (prefixWord ++ tailWord_3451758).sum := by decide
  have hdescent : baseEnd_3451758 < baseStart_3451758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451812 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_3451812 : Nat := 118140960795 + 3451812 * 2 ^ 59
def prefixEnd_3451812 : Nat := 4983230072969 + 3 ^ 40 * 3451812 * 2
def baseEnd_3451812 : Nat := 1181625789971702668916941

theorem tailTrace_3451812 : CollatzResearch.WordTrace tailWord_3451812 prefixEnd_3451812 1181625789971702668916941 := by
  unfold tailWord_3451812
  simp only [CollatzResearch.WordTrace]
  refine ⟨62948963285341060700210845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83931951047121414266947793 62948963285341060700210845)
  ·
    refine ⟨23605861232002897762579067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62948963285341060700210845 23605861232002897762579067)
    ·
      refine ⟨35408791848004346643868601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23605861232002897762579067 35408791848004346643868601)
      ·
        refine ⟨26556593886003259982901451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35408791848004346643868601 26556593886003259982901451)
        ·
          refine ⟨39834890829004889974352177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26556593886003259982901451 39834890829004889974352177)
          ·
            refine ⟨29876168121753667480764133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39834890829004889974352177 29876168121753667480764133)
            ·
              refine ⟨5601781522828812652643275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29876168121753667480764133 5601781522828812652643275)
              ·
                refine ⟨8402672284243218978964913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601781522828812652643275 8402672284243218978964913)
                ·
                  refine ⟨6302004213182414234223685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8402672284243218978964913 6302004213182414234223685)
                  ·
                    refine ⟨1181625789971702668916941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302004213182414234223685 1181625789971702668916941)
                    ·
                      rfl

theorem cell22_3451812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_3451812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451812 prefixEnd_3451812 := by exact prefixLift 3451812
  have htrace : WordTrace (prefixWord ++ tailWord_3451812) baseStart_3451812 baseEnd_3451812 := by
    simpa [prefixWord, tailWord_3451812, baseEnd_3451812] using wordTrace_append hprefix tailTrace_3451812
  have hstable : (prefixWord ++ tailWord_3451812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451812).length < 2 ^ (prefixWord ++ tailWord_3451812).sum := by decide
  have hdescent : baseEnd_3451812 < baseStart_3451812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451840 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_3451840 : Nat := 118140960795 + 3451840 * 2 ^ 59
def prefixEnd_3451840 : Nat := 4983230072969 + 3 ^ 40 * 3451840 * 2
def baseEnd_3451840 : Nat := 1181635374943919929216855

theorem tailTrace_3451840 : CollatzResearch.WordTrace tailWord_3451840 prefixEnd_3451840 1181635374943919929216855 := by
  unfold tailWord_3451840
  simp only [CollatzResearch.WordTrace]
  refine ⟨62949473907290341091220487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83932631876387121454960649 62949473907290341091220487)
  ·
    refine ⟨94424210860935511636830731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62949473907290341091220487 94424210860935511636830731)
    ·
      refine ⟨141636316291403267455246097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94424210860935511636830731 141636316291403267455246097)
      ·
        refine ⟨106227237218552450591434573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141636316291403267455246097 106227237218552450591434573)
        ·
          refine ⟨39835213956957168971787965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106227237218552450591434573 39835213956957168971787965)
          ·
            refine ⟨14938205233858938364420487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39835213956957168971787965 14938205233858938364420487)
            ·
              refine ⟨22407307850788407546630731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14938205233858938364420487 22407307850788407546630731)
              ·
                refine ⟨33610961776182611319946097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22407307850788407546630731 33610961776182611319946097)
                ·
                  refine ⟨25208221332136958489959573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33610961776182611319946097 25208221332136958489959573)
                  ·
                    refine ⟨1181635374943919929216855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25208221332136958489959573 1181635374943919929216855)
                    ·
                      rfl

theorem cell22_3451840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_3451840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451840 prefixEnd_3451840 := by exact prefixLift 3451840
  have htrace : WordTrace (prefixWord ++ tailWord_3451840) baseStart_3451840 baseEnd_3451840 := by
    simpa [prefixWord, tailWord_3451840, baseEnd_3451840] using wordTrace_append hprefix tailTrace_3451840
  have hstable : (prefixWord ++ tailWord_3451840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451840).length < 2 ^ (prefixWord ++ tailWord_3451840).sum := by decide
  have hdescent : baseEnd_3451840 < baseStart_3451840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451889 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 5]
def baseStart_3451889 : Nat := 118140960795 + 3451889 * 2 ^ 59
def prefixEnd_3451889 : Nat := 4983230072969 + 3 ^ 40 * 3451889 * 2
def baseEnd_3451889 : Nat := 393884049548433378247235

theorem tailTrace_3451889 : CollatzResearch.WordTrace tailWord_3451889 prefixEnd_3451889 393884049548433378247235 := by
  unfold tailWord_3451889
  simp only [CollatzResearch.WordTrace]
  refine ⟨125900734991403163550974721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83933823327602109033983147 125900734991403163550974721)
  ·
    refine ⟨94425551243552372663231041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125900734991403163550974721 94425551243552372663231041)
    ·
      refine ⟨70819163432664279497423281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94425551243552372663231041 70819163432664279497423281)
      ·
        refine ⟨53114372574498209623067461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70819163432664279497423281 53114372574498209623067461)
        ·
          refine ⟨9958944857718414304325149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53114372574498209623067461 9958944857718414304325149)
          ·
            refine ⟨3734604321644405364121931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9958944857718414304325149 3734604321644405364121931)
            ·
              refine ⟨5601906482466608046182897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734604321644405364121931 5601906482466608046182897)
              ·
                refine ⟨4201429861849956034637173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5601906482466608046182897 4201429861849956034637173)
                ·
                  refine ⟨393884049548433378247235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4201429861849956034637173 393884049548433378247235)
                  ·
                    rfl

theorem cell22_3451889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_3451889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451889 prefixEnd_3451889 := by exact prefixLift 3451889
  have htrace : WordTrace (prefixWord ++ tailWord_3451889) baseStart_3451889 baseEnd_3451889 := by
    simpa [prefixWord, tailWord_3451889, baseEnd_3451889] using wordTrace_append hprefix tailTrace_3451889
  have hstable : (prefixWord ++ tailWord_3451889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451889).length < 2 ^ (prefixWord ++ tailWord_3451889).sum := by decide
  have hdescent : baseEnd_3451889 < baseStart_3451889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451893 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3451893 : Nat := 118140960795 + 3451893 * 2 ^ 59
def prefixEnd_3451893 : Nat := 4983230072969 + 3 ^ 40 * 3451893 * 2
def baseEnd_3451893 : Nat := 1181653517927045457641693

theorem tailTrace_3451893 : CollatzResearch.WordTrace tailWord_3451893 prefixEnd_3451893 1181653517927045457641693 := by
  unfold tailWord_3451893
  simp only [CollatzResearch.WordTrace]
  refine ⟨125900880883388672234120333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83933920588925781489413555 125900880883388672234120333)
  ·
    refine ⟨47212830331270752087795125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125900880883388672234120333 47212830331270752087795125)
    ·
      refine ⟨4426202843556633008230793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47212830331270752087795125 4426202843556633008230793)
      ·
        refine ⟨3319652132667474756173095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4426202843556633008230793 3319652132667474756173095)
        ·
          refine ⟨4979478199001212134259643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319652132667474756173095 4979478199001212134259643)
          ·
            refine ⟨7469217298501818201389465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979478199001212134259643 7469217298501818201389465)
            ·
              refine ⟨5601912973876363651042099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469217298501818201389465 5601912973876363651042099)
              ·
                refine ⟨8402869460814545476563149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601912973876363651042099 8402869460814545476563149)
                ·
                  refine ⟨3151076047805454553711181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8402869460814545476563149 3151076047805454553711181)
                  ·
                    refine ⟨1181653517927045457641693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151076047805454553711181 1181653517927045457641693)
                    ·
                      rfl

theorem cell22_3451893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3451893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451893 prefixEnd_3451893 := by exact prefixLift 3451893
  have htrace : WordTrace (prefixWord ++ tailWord_3451893) baseStart_3451893 baseEnd_3451893 := by
    simpa [prefixWord, tailWord_3451893, baseEnd_3451893] using wordTrace_append hprefix tailTrace_3451893
  have hstable : (prefixWord ++ tailWord_3451893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451893).length < 2 ^ (prefixWord ++ tailWord_3451893).sum := by decide
  have hdescent : baseEnd_3451893 < baseStart_3451893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451947 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 2, 4]
def baseStart_3451947 : Nat := 118140960795 + 3451947 * 2 ^ 59
def prefixEnd_3451947 : Nat := 4983230072969 + 3 ^ 40 * 3451947 * 2
def baseEnd_3451947 : Nat := 1181672003230607316791527

theorem tailTrace_3451947 : CollatzResearch.WordTrace tailWord_3451947 prefixEnd_3451947 1181672003230607316791527 := by
  unfold tailWord_3451947
  simp only [CollatzResearch.WordTrace]
  refine ⟨125902850425193039456586095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83935233616795359637724063 125902850425193039456586095)
  ·
    refine ⟨188854275637789559184879143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125902850425193039456586095 188854275637789559184879143)
    ·
      refine ⟨283281413456684338777318715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188854275637789559184879143 283281413456684338777318715)
      ·
        refine ⟨424922120185026508165978073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283281413456684338777318715 424922120185026508165978073)
        ·
          refine ⟨318691590138769881124483555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424922120185026508165978073 318691590138769881124483555)
          ·
            refine ⟨478037385208154821686725333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318691590138769881124483555 478037385208154821686725333)
            ·
              refine ⟨11204001215816128633282625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 478037385208154821686725333 11204001215816128633282625)
              ·
                refine ⟨8403000911862096474961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11204001215816128633282625 8403000911862096474961969)
                ·
                  refine ⟨6302250683896572356221477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8403000911862096474961969 6302250683896572356221477)
                  ·
                    refine ⟨1181672003230607316791527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302250683896572356221477 1181672003230607316791527)
                    ·
                      rfl

theorem cell22_3451947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_3451947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451947 prefixEnd_3451947 := by exact prefixLift 3451947
  have htrace : WordTrace (prefixWord ++ tailWord_3451947) baseStart_3451947 baseEnd_3451947 := by
    simpa [prefixWord, tailWord_3451947, baseEnd_3451947] using wordTrace_append hprefix tailTrace_3451947
  have hstable : (prefixWord ++ tailWord_3451947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451947).length < 2 ^ (prefixWord ++ tailWord_3451947).sum := by decide
  have hdescent : baseEnd_3451947 < baseStart_3451947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451981 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3451981 : Nat := 118140960795 + 3451981 * 2 ^ 59
def prefixEnd_3451981 : Nat := 4983230072969 + 3 ^ 40 * 3451981 * 2
def baseEnd_3451981 : Nat := 1181683642125442561441423

theorem tailTrace_3451981 : CollatzResearch.WordTrace tailWord_3451981 prefixEnd_3451981 1181683642125442561441423 := by
  unfold tailWord_3451981
  simp only [CollatzResearch.WordTrace]
  refine ⟨125904090507069863263323797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83936060338046575508882531 125904090507069863263323797)
  ·
    refine ⟨5901754242518899840468303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125904090507069863263323797 5901754242518899840468303)
    ·
      refine ⟨8852631363778349760702455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5901754242518899840468303 8852631363778349760702455)
      ·
        refine ⟨13278947045667524641053683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8852631363778349760702455 13278947045667524641053683)
        ·
          refine ⟨19918420568501286961580525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13278947045667524641053683 19918420568501286961580525)
          ·
            refine ⟨7469407713187982610592697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19918420568501286961580525 7469407713187982610592697)
            ·
              refine ⟨5602055784890986957944523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469407713187982610592697 5602055784890986957944523)
              ·
                refine ⟨8403083677336480436916785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602055784890986957944523 8403083677336480436916785)
                ·
                  refine ⟨6302312758002360327687589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8403083677336480436916785 6302312758002360327687589)
                  ·
                    refine ⟨1181683642125442561441423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302312758002360327687589 1181683642125442561441423)
                    ·
                      rfl

theorem cell22_3451981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3451981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451981 prefixEnd_3451981 := by exact prefixLift 3451981
  have htrace : WordTrace (prefixWord ++ tailWord_3451981) baseStart_3451981 baseEnd_3451981 := by
    simpa [prefixWord, tailWord_3451981, baseEnd_3451981] using wordTrace_append hprefix tailTrace_3451981
  have hstable : (prefixWord ++ tailWord_3451981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451981).length < 2 ^ (prefixWord ++ tailWord_3451981).sum := by decide
  have hdescent : baseEnd_3451981 < baseStart_3451981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451998 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3451998 : Nat := 118140960795 + 3451998 * 2 ^ 59
def prefixEnd_3451998 : Nat := 4983230072969 + 3 ^ 40 * 3451998 * 2
def baseEnd_3451998 : Nat := 1181689461572860183766371

theorem tailTrace_3451998 : CollatzResearch.WordTrace tailWord_3451998 prefixEnd_3451998 1181689461572860183766371 := by
  unfold tailWord_3451998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15738088818501034395836581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83936473698672183444461765 15738088818501034395836581)
  ·
    refine ⟨2950891653468943949219359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15738088818501034395836581 2950891653468943949219359)
    ·
      refine ⟨4426337480203415923829039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950891653468943949219359 4426337480203415923829039)
      ·
        refine ⟨6639506220305123885743559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426337480203415923829039 6639506220305123885743559)
        ·
          refine ⟨9959259330457685828615339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6639506220305123885743559 9959259330457685828615339)
          ·
            refine ⟨14938888995686528742923009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9959259330457685828615339 14938888995686528742923009)
            ·
              refine ⟨11204166746764896557192257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14938888995686528742923009 11204166746764896557192257)
              ·
                refine ⟨8403125060073672417894193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11204166746764896557192257 8403125060073672417894193)
                ·
                  refine ⟨6302343795055254313420645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8403125060073672417894193 6302343795055254313420645)
                  ·
                    refine ⟨1181689461572860183766371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302343795055254313420645 1181689461572860183766371)
                    ·
                      rfl

theorem cell22_3451998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3451998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451998 prefixEnd_3451998 := by exact prefixLift 3451998
  have htrace : WordTrace (prefixWord ++ tailWord_3451998) baseStart_3451998 baseEnd_3451998 := by
    simpa [prefixWord, tailWord_3451998, baseEnd_3451998] using wordTrace_append hprefix tailTrace_3451998
  have hstable : (prefixWord ++ tailWord_3451998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451998).length < 2 ^ (prefixWord ++ tailWord_3451998).sum := by decide
  have hdescent : baseEnd_3451998 < baseStart_3451998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452030 : List Nat := [4, 2, 4, 1, 1, 1, 3, 6]
def baseStart_3452030 : Nat := 118140960795 + 3452030 * 2 ^ 59
def prefixEnd_3452030 : Nat := 4983230072969 + 3 ^ 40 * 3452030 * 2
def baseEnd_3452030 : Nat := 131300046202980307440697

theorem tailTrace_3452030 : CollatzResearch.WordTrace tailWord_3452030 prefixEnd_3452030 131300046202980307440697 := by
  unfold tailWord_3452030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15738234710486543078982193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83937251789261563087905029 15738234710486543078982193)
  ·
    refine ⟨11803676032864907309236645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15738234710486543078982193 11803676032864907309236645)
    ·
      refine ⟨2213189256162170120481871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11803676032864907309236645 2213189256162170120481871)
      ·
        refine ⟨3319783884243255180722807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213189256162170120481871 3319783884243255180722807)
        ·
          refine ⟨4979675826364882771084211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319783884243255180722807 4979675826364882771084211)
          ·
            refine ⟨7469513739547324156626317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979675826364882771084211 7469513739547324156626317)
            ·
              refine ⟨2801067652330246558734869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7469513739547324156626317 2801067652330246558734869)
              ·
                refine ⟨131300046202980307440697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2801067652330246558734869 131300046202980307440697)
                ·
                  rfl

theorem cell22_3452030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_3452030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452030 prefixEnd_3452030 := by exact prefixLift 3452030
  have htrace : WordTrace (prefixWord ++ tailWord_3452030) baseStart_3452030 baseEnd_3452030 := by
    simpa [prefixWord, tailWord_3452030, baseEnd_3452030] using wordTrace_append hprefix tailTrace_3452030
  have hstable : (prefixWord ++ tailWord_3452030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452030).length < 2 ^ (prefixWord ++ tailWord_3452030).sum := by decide
  have hdescent : baseEnd_3452030 < baseStart_3452030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452067 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 3, 5]
def baseStart_3452067 : Nat := 118140960795 + 3452067 * 2 ^ 59
def prefixEnd_3452067 : Nat := 4983230072969 + 3 ^ 40 * 3452067 * 2
def baseEnd_3452067 : Nat := 1181713081682967003791159

theorem tailTrace_3452067 : CollatzResearch.WordTrace tailWord_3452067 prefixEnd_3452067 1181713081682967003791159 := by
  unfold tailWord_3452067
  simp only [CollatzResearch.WordTrace]
  refine ⟨125907227184758299950954455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83938151456505533300636303 125907227184758299950954455)
  ·
    refine ⟨188860840777137449926431683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125907227184758299950954455 188860840777137449926431683)
    ·
      refine ⟨283291261165706174889647525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188860840777137449926431683 283291261165706174889647525)
      ·
        refine ⟨53117111468569907791808911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283291261165706174889647525 53117111468569907791808911)
        ·
          refine ⟨79675667202854861687713367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53117111468569907791808911 79675667202854861687713367)
          ·
            refine ⟨119513500804282292531570051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79675667202854861687713367 119513500804282292531570051)
            ·
              refine ⟨179270251206423438797355077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119513500804282292531570051 179270251206423438797355077)
              ·
                refine ⟨33613172101204394774504077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179270251206423438797355077 33613172101204394774504077)
                ·
                  refine ⟨12604939537951648040439029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33613172101204394774504077 12604939537951648040439029)
                  ·
                    refine ⟨1181713081682967003791159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12604939537951648040439029 1181713081682967003791159)
                    ·
                      rfl

theorem cell22_3452067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_3452067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452067 prefixEnd_3452067 := by exact prefixLift 3452067
  have htrace : WordTrace (prefixWord ++ tailWord_3452067) baseStart_3452067 baseEnd_3452067 := by
    simpa [prefixWord, tailWord_3452067, baseEnd_3452067] using wordTrace_append hprefix tailTrace_3452067
  have hstable : (prefixWord ++ tailWord_3452067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452067).length < 2 ^ (prefixWord ++ tailWord_3452067).sum := by decide
  have hdescent : baseEnd_3452067 < baseStart_3452067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452069 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 6]
def baseStart_3452069 : Nat := 118140960795 + 3452069 * 2 ^ 59
def prefixEnd_3452069 : Nat := 4983230072969 + 3 ^ 40 * 3452069 * 2
def baseEnd_3452069 : Nat := 393904588774613221747051

theorem tailTrace_3452069 : CollatzResearch.WordTrace tailWord_3452069 prefixEnd_3452069 393904588774613221747051 := by
  unfold tailWord_3452069
  simp only [CollatzResearch.WordTrace]
  refine ⟨125907300130751054292527261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83938200087167369528351507 125907300130751054292527261)
  ·
    refine ⟨47215237549031645359697723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125907300130751054292527261 47215237549031645359697723)
    ·
      refine ⟨70822856323547468039546585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47215237549031645359697723 70822856323547468039546585)
      ·
        refine ⟨53117142242660601029659939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70822856323547468039546585 53117142242660601029659939)
        ·
          refine ⟨79675713363990901544489909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53117142242660601029659939 79675713363990901544489909)
          ·
            refine ⟨7469598127874147019795929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79675713363990901544489909 7469598127874147019795929)
            ·
              refine ⟨5602198595905610264846947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469598127874147019795929 5602198595905610264846947)
              ·
                refine ⟨8403297893858415397270421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602198595905610264846947 8403297893858415397270421)
                ·
                  refine ⟨393904588774613221747051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8403297893858415397270421 393904588774613221747051)
                  ·
                    rfl

theorem cell22_3452069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_3452069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452069 prefixEnd_3452069 := by exact prefixLift 3452069
  have htrace : WordTrace (prefixWord ++ tailWord_3452069) baseStart_3452069 baseEnd_3452069 := by
    simpa [prefixWord, tailWord_3452069, baseEnd_3452069] using wordTrace_append hprefix tailTrace_3452069
  have hstable : (prefixWord ++ tailWord_3452069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452069).length < 2 ^ (prefixWord ++ tailWord_3452069).sum := by decide
  have hdescent : baseEnd_3452069 < baseStart_3452069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452191 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 2, 5]
def baseStart_3452191 : Nat := 118140960795 + 3452191 * 2 ^ 59
def prefixEnd_3452191 : Nat := 4983230072969 + 3 ^ 40 * 3452191 * 2
def baseEnd_3452191 : Nat := 1181755529417072013690779

theorem tailTrace_3452191 : CollatzResearch.WordTrace tailWord_3452191 prefixEnd_3452191 1181755529417072013690779 := by
  unfold tailWord_3452191
  simp only [CollatzResearch.WordTrace]
  refine ⟨125911749836309069128468427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83941166557539379418978951 125911749836309069128468427)
  ·
    refine ⟨188867624754463603692702641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125911749836309069128468427 188867624754463603692702641)
    ·
      refine ⟨141650718565847702769526981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188867624754463603692702641 141650718565847702769526981)
      ·
        refine ⟨26559509731096444269286309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141650718565847702769526981 26559509731096444269286309)
        ·
          refine ⟨4979908074580583300491183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26559509731096444269286309 4979908074580583300491183)
          ·
            refine ⟨7469862111870874950736775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979908074580583300491183 7469862111870874950736775)
            ·
              refine ⟨11204793167806312426105163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469862111870874950736775 11204793167806312426105163)
              ·
                refine ⟨16807189751709468639157745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11204793167806312426105163 16807189751709468639157745)
                ·
                  refine ⟨12605392313782101479368309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16807189751709468639157745 12605392313782101479368309)
                  ·
                    refine ⟨1181755529417072013690779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12605392313782101479368309 1181755529417072013690779)
                    ·
                      rfl

theorem cell22_3452191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_3452191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452191 prefixEnd_3452191 := by exact prefixLift 3452191
  have htrace : WordTrace (prefixWord ++ tailWord_3452191) baseStart_3452191 baseEnd_3452191 := by
    simpa [prefixWord, tailWord_3452191, baseEnd_3452191] using wordTrace_append hprefix tailTrace_3452191
  have hstable : (prefixWord ++ tailWord_3452191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452191).length < 2 ^ (prefixWord ++ tailWord_3452191).sum := by decide
  have hdescent : baseEnd_3452191 < baseStart_3452191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452214 : List Nat := [5, 1, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3452214 : Nat := 118140960795 + 3452214 * 2 ^ 59
def prefixEnd_3452214 : Nat := 4983230072969 + 3 ^ 40 * 3452214 * 2
def baseEnd_3452214 : Nat := 1181763402787107620365709

theorem tailTrace_3452214 : CollatzResearch.WordTrace tailWord_3452214 prefixEnd_3452214 1181763402787107620365709 := by
  unfold tailWord_3452214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869536794701609003534731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83941725810150496037703797 7869536794701609003534731)
  ·
    refine ⟨11804305192052413505302097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7869536794701609003534731 11804305192052413505302097)
    ·
      refine ⟨8853228894039310128976573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11804305192052413505302097 8853228894039310128976573)
      ·
        refine ⟨3319960835264741298366215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8853228894039310128976573 3319960835264741298366215)
        ·
          refine ⟨4979941252897111947549323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319960835264741298366215 4979941252897111947549323)
          ·
            refine ⟨7469911879345667921323985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979941252897111947549323 7469911879345667921323985)
            ·
              refine ⟨5602433909509250940992989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469911879345667921323985 5602433909509250940992989)
              ·
                refine ⟨2100912716065969102872371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5602433909509250940992989 2100912716065969102872371)
                ·
                  refine ⟨3151369074098953654308557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100912716065969102872371 3151369074098953654308557)
                  ·
                    refine ⟨1181763402787107620365709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151369074098953654308557 1181763402787107620365709)
                    ·
                      rfl

theorem cell22_3452214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3452214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452214 prefixEnd_3452214 := by exact prefixLift 3452214
  have htrace : WordTrace (prefixWord ++ tailWord_3452214) baseStart_3452214 baseEnd_3452214 := by
    simpa [prefixWord, tailWord_3452214, baseEnd_3452214] using wordTrace_append hprefix tailTrace_3452214
  have hstable : (prefixWord ++ tailWord_3452214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452214).length < 2 ^ (prefixWord ++ tailWord_3452214).sum := by decide
  have hdescent : baseEnd_3452214 < baseStart_3452214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452223 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 1, 4]
def baseStart_3452223 : Nat := 118140960795 + 3452223 * 2 ^ 59
def prefixEnd_3452223 : Nat := 4983230072969 + 3 ^ 40 * 3452223 * 2
def baseEnd_3452223 : Nat := 1181766483671034596890681

theorem tailTrace_3452223 : CollatzResearch.WordTrace tailWord_3452223 prefixEnd_3452223 1181766483671034596890681 := by
  unfold tailWord_3452223
  simp only [CollatzResearch.WordTrace]
  refine ⟨125912916972193138593633323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83941944648128759062422215 125912916972193138593633323)
  ·
    refine ⟨188869375458289707890449985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125912916972193138593633323 188869375458289707890449985)
    ·
      refine ⟨141652031593717280917837489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188869375458289707890449985 141652031593717280917837489)
      ·
        refine ⟨106239023695287960688378117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141652031593717280917837489 106239023695287960688378117)
        ·
          refine ⟨19919816942866492629070897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106239023695287960688378117 19919816942866492629070897)
          ·
            refine ⟨14939862707149869471803173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19919816942866492629070897 14939862707149869471803173)
            ·
              refine ⟨2801224257590600525963095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14939862707149869471803173 2801224257590600525963095)
              ·
                refine ⟨4201836386385900788944643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801224257590600525963095 4201836386385900788944643)
                ·
                  refine ⟨6302754579578851183416965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201836386385900788944643 6302754579578851183416965)
                  ·
                    refine ⟨1181766483671034596890681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302754579578851183416965 1181766483671034596890681)
                    ·
                      rfl

theorem cell22_3452223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_3452223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452223 prefixEnd_3452223 := by exact prefixLift 3452223
  have htrace : WordTrace (prefixWord ++ tailWord_3452223) baseStart_3452223 baseEnd_3452223 := by
    simpa [prefixWord, tailWord_3452223, baseEnd_3452223] using wordTrace_append hprefix tailTrace_3452223
  have hstable : (prefixWord ++ tailWord_3452223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452223).length < 2 ^ (prefixWord ++ tailWord_3452223).sum := by decide
  have hdescent : baseEnd_3452223 < baseStart_3452223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452281 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 5, 3]
def baseStart_3452281 : Nat := 118140960795 + 3452281 * 2 ^ 59
def prefixEnd_3452281 : Nat := 4983230072969 + 3 ^ 40 * 3452281 * 2
def baseEnd_3452281 : Nat := 1181786338256341778940503

theorem tailTrace_3452281 : CollatzResearch.WordTrace tailWord_3452281 prefixEnd_3452281 1181786338256341778940503 := by
  unfold tailWord_3452281
  simp only [CollatzResearch.WordTrace]
  refine ⟨125915032405983014499244697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83943354937322009666163131 125915032405983014499244697)
  ·
    refine ⟨94436274304487260874433523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125915032405983014499244697 94436274304487260874433523)
    ·
      refine ⟨141654411456730891311650285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94436274304487260874433523 141654411456730891311650285)
      ·
        refine ⟨53120404296274084241868857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141654411456730891311650285 53120404296274084241868857)
        ·
          refine ⟨39840303222205563181401643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53120404296274084241868857 39840303222205563181401643)
          ·
            refine ⟨59760454833308344772102465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39840303222205563181401643 59760454833308344772102465)
            ·
              refine ⟨44820341124981258579076849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59760454833308344772102465 44820341124981258579076849)
              ·
                refine ⟨33615255843735943934307637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44820341124981258579076849 33615255843735943934307637)
                ·
                  refine ⟨3151430235350244743841341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33615255843735943934307637 3151430235350244743841341)
                  ·
                    refine ⟨1181786338256341778940503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151430235350244743841341 1181786338256341778940503)
                    ·
                      rfl

theorem cell22_3452281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_3452281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452281 prefixEnd_3452281 := by exact prefixLift 3452281
  have htrace : WordTrace (prefixWord ++ tailWord_3452281) baseStart_3452281 baseEnd_3452281 := by
    simpa [prefixWord, tailWord_3452281, baseEnd_3452281] using wordTrace_append hprefix tailTrace_3452281
  have hstable : (prefixWord ++ tailWord_3452281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452281).length < 2 ^ (prefixWord ++ tailWord_3452281).sum := by decide
  have hdescent : baseEnd_3452281 < baseStart_3452281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452401 : List Nat := [1, 2, 2, 2, 3, 3, 9]
def baseStart_3452401 : Nat := 118140960795 + 3452401 * 2 ^ 59
def prefixEnd_3452401 : Nat := 4983230072969 + 3 ^ 40 * 3452401 * 2
def baseEnd_3452401 : Nat := 43771385804025980220005

theorem tailTrace_3452401 : CollatzResearch.WordTrace tailWord_3452401 prefixEnd_3452401 43771385804025980220005 := by
  unfold tailWord_3452401
  simp only [CollatzResearch.WordTrace]
  refine ⟨125919409165548274993613057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83946272777032183329075371 125919409165548274993613057)
  ·
    refine ⟨94439556874161206245209793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125919409165548274993613057 94439556874161206245209793)
    ·
      refine ⟨70829667655620904683907345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94439556874161206245209793 70829667655620904683907345)
      ·
        refine ⟨53122250741715678512930509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70829667655620904683907345 53122250741715678512930509)
        ·
          refine ⟨19920844028143379442348941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53122250741715678512930509 19920844028143379442348941)
          ·
            refine ⟨7470316510553767290880853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19920844028143379442348941 7470316510553767290880853)
            ·
              refine ⟨43771385804025980220005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7470316510553767290880853 43771385804025980220005)
              ·
                rfl

theorem cell22_3452401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 9].length) (baseStart_3452401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452401 prefixEnd_3452401 := by exact prefixLift 3452401
  have htrace : WordTrace (prefixWord ++ tailWord_3452401) baseStart_3452401 baseEnd_3452401 := by
    simpa [prefixWord, tailWord_3452401, baseEnd_3452401] using wordTrace_append hprefix tailTrace_3452401
  have hstable : (prefixWord ++ tailWord_3452401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452401).length < 2 ^ (prefixWord ++ tailWord_3452401).sum := by decide
  have hdescent : baseEnd_3452401 < baseStart_3452401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452433 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 3, 3]
def baseStart_3452433 : Nat := 118140960795 + 3452433 * 2 ^ 59
def prefixEnd_3452433 : Nat := 4983230072969 + 3 ^ 40 * 3452433 * 2
def baseEnd_3452433 : Nat := 1181838370962664049140037

theorem tailTrace_3452433 : CollatzResearch.WordTrace tailWord_3452433 prefixEnd_3452433 1181838370962664049140037 := by
  unfold tailWord_3452433
  simp only [CollatzResearch.WordTrace]
  refine ⟨125920576301432344458777953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83947050867621562972518635 125920576301432344458777953)
  ·
    refine ⟨94440432226074258344083465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125920576301432344458777953 94440432226074258344083465)
    ·
      refine ⟨70830324169555693758062599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94440432226074258344083465 70830324169555693758062599)
      ·
        refine ⟨106245486254333540637093899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70830324169555693758062599 106245486254333540637093899)
        ·
          refine ⟨159368229381500310955640849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106245486254333540637093899 159368229381500310955640849)
          ·
            refine ⟨119526172036125233216730637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159368229381500310955640849 119526172036125233216730637)
            ·
              refine ⟨44822314513546962456273989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119526172036125233216730637 44822314513546962456273989)
              ·
                refine ⟨8404183971290055460551373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44822314513546962456273989 8404183971290055460551373)
                ·
                  refine ⟨3151568989233770797706765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8404183971290055460551373 3151568989233770797706765)
                  ·
                    refine ⟨1181838370962664049140037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151568989233770797706765 1181838370962664049140037)
                    ·
                      rfl

theorem cell22_3452433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_3452433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452433 prefixEnd_3452433 := by exact prefixLift 3452433
  have htrace : WordTrace (prefixWord ++ tailWord_3452433) baseStart_3452433 baseEnd_3452433 := by
    simpa [prefixWord, tailWord_3452433, baseEnd_3452433] using wordTrace_append hprefix tailTrace_3452433
  have hstable : (prefixWord ++ tailWord_3452433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452433).length < 2 ^ (prefixWord ++ tailWord_3452433).sum := by decide
  have hdescent : baseEnd_3452433 < baseStart_3452433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452491 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 8]
def baseStart_3452491 : Nat := 118140960795 + 3452491 * 2 ^ 59
def prefixEnd_3452491 : Nat := 4983230072969 + 3 ^ 40 * 3452491 * 2
def baseEnd_3452491 : Nat := 393952741849323743729953

theorem tailTrace_3452491 : CollatzResearch.WordTrace tailWord_3452491 prefixEnd_3452491 393952741849323743729953 := by
  unfold tailWord_3452491
  simp only [CollatzResearch.WordTrace]
  refine ⟨125922691735222220364389327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83948461156814813576259551 125922691735222220364389327)
  ·
    refine ⟨188884037602833330546583991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125922691735222220364389327 188884037602833330546583991)
    ·
      refine ⟨283326056404249995819875987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188884037602833330546583991 283326056404249995819875987)
      ·
        refine ⟨424989084606374993729813981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283326056404249995819875987 424989084606374993729813981)
        ·
          refine ⟨159370906727390622648680243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424989084606374993729813981 159370906727390622648680243)
          ·
            refine ⟨239056360091085933973020365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159370906727390622648680243 239056360091085933973020365)
            ·
              refine ⟨89646135034157225239882637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239056360091085933973020365 89646135034157225239882637)
              ·
                refine ⟨33617300637808959464955989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89646135034157225239882637 33617300637808959464955989)
                ·
                  refine ⟨393952741849323743729953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33617300637808959464955989 393952741849323743729953)
                  ·
                    rfl

theorem cell22_3452491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_3452491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452491 prefixEnd_3452491 := by exact prefixLift 3452491
  have htrace : WordTrace (prefixWord ++ tailWord_3452491) baseStart_3452491 baseEnd_3452491 := by
    simpa [prefixWord, tailWord_3452491, baseEnd_3452491] using wordTrace_append hprefix tailTrace_3452491
  have hstable : (prefixWord ++ tailWord_3452491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452491).length < 2 ^ (prefixWord ++ tailWord_3452491).sum := by decide
  have hdescent : baseEnd_3452491 < baseStart_3452491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452523 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 8, 3]
def baseStart_3452523 : Nat := 118140960795 + 3452523 * 2 ^ 59
def prefixEnd_3452523 : Nat := 4983230072969 + 3 ^ 40 * 3452523 * 2
def baseEnd_3452523 : Nat := 1181869179801933814389761

theorem tailTrace_3452523 : CollatzResearch.WordTrace tailWord_3452523 prefixEnd_3452523 1181869179801933814389761 := by
  unfold tailWord_3452523
  simp only [CollatzResearch.WordTrace]
  refine ⟨125923858871106289829554223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83949239247404193219702815 125923858871106289829554223)
  ·
    refine ⟨188885788306659434744331335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125923858871106289829554223 188885788306659434744331335)
    ·
      refine ⟨283328682459989152116497003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188885788306659434744331335 283328682459989152116497003)
      ·
        refine ⟨424993023689983728174745505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283328682459989152116497003 424993023689983728174745505)
        ·
          refine ⟨318744767767487796131059129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424993023689983728174745505 318744767767487796131059129)
          ·
            refine ⟨239058575825615847098294347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318744767767487796131059129 239058575825615847098294347)
            ·
              refine ⟨358587863738423770647441521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239058575825615847098294347 358587863738423770647441521)
              ·
                refine ⟨268940897803817827985581141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358587863738423770647441521 268940897803817827985581141)
                ·
                  refine ⟨3151651146138490171706029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 268940897803817827985581141 3151651146138490171706029)
                  ·
                    refine ⟨1181869179801933814389761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151651146138490171706029 1181869179801933814389761)
                    ·
                      rfl

theorem cell22_3452523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 3].length) (baseStart_3452523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452523 prefixEnd_3452523 := by exact prefixLift 3452523
  have htrace : WordTrace (prefixWord ++ tailWord_3452523) baseStart_3452523 baseEnd_3452523 := by
    simpa [prefixWord, tailWord_3452523, baseEnd_3452523] using wordTrace_append hprefix tailTrace_3452523
  have hstable : (prefixWord ++ tailWord_3452523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452523).length < 2 ^ (prefixWord ++ tailWord_3452523).sum := by decide
  have hdescent : baseEnd_3452523 < baseStart_3452523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452574 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3452574 : Nat := 118140960795 + 3452574 * 2 ^ 59
def prefixEnd_3452574 : Nat := 4983230072969 + 3 ^ 40 * 3452574 * 2
def baseEnd_3452574 : Nat := 1181886638144186681364605

theorem tailTrace_3452574 : CollatzResearch.WordTrace tailWord_3452574 prefixEnd_3452574 1181886638144186681364605 := by
  unfold tailWord_3452574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15740714874240190692457597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83950479329281017026440517 15740714874240190692457597)
  ·
    refine ⟨5902768077840071509671599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15740714874240190692457597 5902768077840071509671599)
    ·
      refine ⟨8854152116760107264507399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902768077840071509671599 8854152116760107264507399)
      ·
        refine ⟨13281228175140160896761099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8854152116760107264507399 13281228175140160896761099)
        ·
          refine ⟨19921842262710241345141649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13281228175140160896761099 19921842262710241345141649)
          ·
            refine ⟨14941381697032681008856237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19921842262710241345141649 14941381697032681008856237)
            ·
              refine ⟨5603018136387255378321089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14941381697032681008856237 5603018136387255378321089)
              ·
                refine ⟨4202263602290441533740817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603018136387255378321089 4202263602290441533740817)
                ·
                  refine ⟨3151697701717831150305613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202263602290441533740817 3151697701717831150305613)
                  ·
                    refine ⟨1181886638144186681364605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151697701717831150305613 1181886638144186681364605)
                    ·
                      rfl

theorem cell22_3452574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3452574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452574 prefixEnd_3452574 := by exact prefixLift 3452574
  have htrace : WordTrace (prefixWord ++ tailWord_3452574) baseStart_3452574 baseEnd_3452574 := by
    simpa [prefixWord, tailWord_3452574, baseEnd_3452574] using wordTrace_append hprefix tailTrace_3452574
  have hstable : (prefixWord ++ tailWord_3452574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452574).length < 2 ^ (prefixWord ++ tailWord_3452574).sum := by decide
  have hdescent : baseEnd_3452574 < baseStart_3452574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452610 : List Nat := [3, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3452610 : Nat := 118140960795 + 3452610 * 2 ^ 59
def prefixEnd_3452610 : Nat := 4983230072969 + 3 ^ 40 * 3452610 * 2
def baseEnd_3452610 : Nat := 393966320559964862488165

theorem tailTrace_3452610 : CollatzResearch.WordTrace tailWord_3452610 prefixEnd_3452610 393966320559964862488165 := by
  unfold tailWord_3452610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31481758005447775921992821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83951354681194069125314189 31481758005447775921992821)
  ·
    refine ⟨2951414813010728992686827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31481758005447775921992821 2951414813010728992686827)
    ·
      refine ⟨4427122219516093489030241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951414813010728992686827 4427122219516093489030241)
      ·
        refine ⟨3320341664637070116772681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4427122219516093489030241 3320341664637070116772681)
        ·
          refine ⟨2490256248477802587579511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320341664637070116772681 2490256248477802587579511)
          ·
            refine ⟨3735384372716703881369267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490256248477802587579511 3735384372716703881369267)
            ·
              refine ⟨5603076559075055822053901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735384372716703881369267 5603076559075055822053901)
              ·
                refine ⟨2101153709653145933270213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5603076559075055822053901 2101153709653145933270213)
                ·
                  refine ⟨393966320559964862488165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101153709653145933270213 393966320559964862488165)
                  ·
                    rfl

theorem cell22_3452610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3452610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452610 prefixEnd_3452610 := by exact prefixLift 3452610
  have htrace : WordTrace (prefixWord ++ tailWord_3452610) baseStart_3452610 baseEnd_3452610 := by
    simpa [prefixWord, tailWord_3452610, baseEnd_3452610] using wordTrace_append hprefix tailTrace_3452610
  have hstable : (prefixWord ++ tailWord_3452610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452610).length < 2 ^ (prefixWord ++ tailWord_3452610).sum := by decide
  have hdescent : baseEnd_3452610 < baseStart_3452610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452636 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3452636 : Nat := 118140960795 + 3452636 * 2 ^ 59
def prefixEnd_3452636 : Nat := 4983230072969 + 3 ^ 40 * 3452636 * 2
def baseEnd_3452636 : Nat := 1181907862011239186314415

theorem tailTrace_3452636 : CollatzResearch.WordTrace tailWord_3452636 prefixEnd_3452636 1181907862011239186314415 := by
  unfold tailWord_3452636
  simp only [CollatzResearch.WordTrace]
  refine ⟨62963990159848455064208881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83951986879797940085611841 62963990159848455064208881)
  ·
    refine ⟨47222992619886341298156661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62963990159848455064208881 47222992619886341298156661)
    ·
      refine ⟨4427155558114344496702187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47222992619886341298156661 4427155558114344496702187)
      ·
        refine ⟨6640733337171516745053281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427155558114344496702187 6640733337171516745053281)
        ·
          refine ⟨4980550002878637558789961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6640733337171516745053281 4980550002878637558789961)
          ·
            refine ⟨3735412502158978169092471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4980550002878637558789961 3735412502158978169092471)
            ·
              refine ⟨5603118753238467253638707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735412502158978169092471 5603118753238467253638707)
              ·
                refine ⟨8404678129857700880458061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603118753238467253638707 8404678129857700880458061)
                ·
                  refine ⟨3151754298696637830171773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8404678129857700880458061 3151754298696637830171773)
                  ·
                    refine ⟨1181907862011239186314415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151754298696637830171773 1181907862011239186314415)
                    ·
                      rfl

theorem cell22_3452636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3452636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452636 prefixEnd_3452636 := by exact prefixLift 3452636
  have htrace : WordTrace (prefixWord ++ tailWord_3452636) baseStart_3452636 baseEnd_3452636 := by
    simpa [prefixWord, tailWord_3452636, baseEnd_3452636] using wordTrace_append hprefix tailTrace_3452636
  have hstable : (prefixWord ++ tailWord_3452636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452636).length < 2 ^ (prefixWord ++ tailWord_3452636).sum := by decide
  have hdescent : baseEnd_3452636 < baseStart_3452636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452645 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_3452645 : Nat := 118140960795 + 3452645 * 2 ^ 59
def prefixEnd_3452645 : Nat := 4983230072969 + 3 ^ 40 * 3452645 * 2
def baseEnd_3452645 : Nat := 1181910942895166162839387

theorem tailTrace_3452645 : CollatzResearch.WordTrace tailWord_3452645 prefixEnd_3452645 1181910942895166162839387 := by
  unfold tailWord_3452645
  simp only [CollatzResearch.WordTrace]
  refine ⟨125928308576664304665495389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83952205717776203110330259 125928308576664304665495389)
  ·
    refine ⟨47223115716249114249560771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125928308576664304665495389 47223115716249114249560771)
    ·
      refine ⟨70834673574373671374341157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47223115716249114249560771 70834673574373671374341157)
      ·
        refine ⟨13281501295195063382688967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70834673574373671374341157 13281501295195063382688967)
        ·
          refine ⟨19922251942792595074033451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13281501295195063382688967 19922251942792595074033451)
          ·
            refine ⟨29883377914188892611050177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19922251942792595074033451 29883377914188892611050177)
            ·
              refine ⟨22412533435641669458287633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29883377914188892611050177 22412533435641669458287633)
              ·
                refine ⟨16809400076731252093715725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22412533435641669458287633 16809400076731252093715725)
                ·
                  refine ⟨6303525028774219535143397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16809400076731252093715725 6303525028774219535143397)
                  ·
                    refine ⟨1181910942895166162839387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303525028774219535143397 1181910942895166162839387)
                    ·
                      rfl

theorem cell22_3452645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_3452645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452645 prefixEnd_3452645 := by exact prefixLift 3452645
  have htrace : WordTrace (prefixWord ++ tailWord_3452645) baseStart_3452645 baseEnd_3452645 := by
    simpa [prefixWord, tailWord_3452645, baseEnd_3452645] using wordTrace_append hprefix tailTrace_3452645
  have hstable : (prefixWord ++ tailWord_3452645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452645).length < 2 ^ (prefixWord ++ tailWord_3452645).sum := by decide
  have hdescent : baseEnd_3452645 < baseStart_3452645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452662 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3452662 : Nat := 118140960795 + 3452662 * 2 ^ 59
def prefixEnd_3452662 : Nat := 4983230072969 + 3 ^ 40 * 3452662 * 2
def baseEnd_3452662 : Nat := 1181916762342583785164335

theorem tailTrace_3452662 : CollatzResearch.WordTrace tailWord_3452662 prefixEnd_3452662 1181916762342583785164335 := by
  unfold tailWord_3452662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870558038600169785554015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83952619078401811045909493 7870558038600169785554015)
  ·
    refine ⟨11805837057900254678331023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7870558038600169785554015 11805837057900254678331023)
    ·
      refine ⟨17708755586850382017496535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11805837057900254678331023 17708755586850382017496535)
      ·
        refine ⟨26563133380275573026244803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17708755586850382017496535 26563133380275573026244803)
        ·
          refine ⟨39844700070413359539367205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26563133380275573026244803 39844700070413359539367205)
          ·
            refine ⟨7470881263202504913631351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39844700070413359539367205 7470881263202504913631351)
            ·
              refine ⟨11206321894803757370447027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7470881263202504913631351 11206321894803757370447027)
              ·
                refine ⟨16809482842205636055670541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11206321894803757370447027 16809482842205636055670541)
                ·
                  refine ⟨6303556065827113520876453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16809482842205636055670541 6303556065827113520876453)
                  ·
                    refine ⟨1181916762342583785164335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303556065827113520876453 1181916762342583785164335)
                    ·
                      rfl

theorem cell22_3452662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3452662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452662 prefixEnd_3452662 := by exact prefixLift 3452662
  have htrace : WordTrace (prefixWord ++ tailWord_3452662) baseStart_3452662 baseEnd_3452662 := by
    simpa [prefixWord, tailWord_3452662, baseEnd_3452662] using wordTrace_append hprefix tailTrace_3452662
  have hstable : (prefixWord ++ tailWord_3452662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452662).length < 2 ^ (prefixWord ++ tailWord_3452662).sum := by decide
  have hdescent : baseEnd_3452662 < baseStart_3452662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452675 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 6, 3]
def baseStart_3452675 : Nat := 118140960795 + 3452675 * 2 ^ 59
def prefixEnd_3452675 : Nat := 4983230072969 + 3 ^ 40 * 3452675 * 2
def baseEnd_3452675 : Nat := 1181921212508256084589295

theorem tailTrace_3452675 : CollatzResearch.WordTrace tailWord_3452675 prefixEnd_3452675 1181921212508256084589295 := by
  unfold tailWord_3452675
  simp only [CollatzResearch.WordTrace]
  refine ⟨125929402766555619789087479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83952935177703746526058319 125929402766555619789087479)
  ·
    refine ⟨188894104149833429683631219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125929402766555619789087479 188894104149833429683631219)
    ·
      refine ⟨283341156224750144525446829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188894104149833429683631219 283341156224750144525446829)
      ·
        refine ⟨106252933584281304197042561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283341156224750144525446829 106252933584281304197042561)
        ·
          refine ⟨79689700188210978147781921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106252933584281304197042561 79689700188210978147781921)
          ·
            refine ⟨59767275141158233610836441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79689700188210978147781921 59767275141158233610836441)
            ·
              refine ⟨44825456355868675208127331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59767275141158233610836441 44825456355868675208127331)
              ·
                refine ⟨67238184533803012812190997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44825456355868675208127331 67238184533803012812190997)
                ·
                  refine ⟨3151789900022016225571453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67238184533803012812190997 3151789900022016225571453)
                  ·
                    refine ⟨1181921212508256084589295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151789900022016225571453 1181921212508256084589295)
                    ·
                      rfl

theorem cell22_3452675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 3].length) (baseStart_3452675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452675 prefixEnd_3452675 := by exact prefixLift 3452675
  have htrace : WordTrace (prefixWord ++ tailWord_3452675) baseStart_3452675 baseEnd_3452675 := by
    simpa [prefixWord, tailWord_3452675, baseEnd_3452675] using wordTrace_append hprefix tailTrace_3452675
  have hstable : (prefixWord ++ tailWord_3452675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452675).length < 2 ^ (prefixWord ++ tailWord_3452675).sum := by decide
  have hdescent : baseEnd_3452675 < baseStart_3452675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452705 : List Nat := [1, 2, 3, 2, 1, 3, 3, 7]
def baseStart_3452705 : Nat := 118140960795 + 3452705 * 2 ^ 59
def prefixEnd_3452705 : Nat := 4983230072969 + 3 ^ 40 * 3452705 * 2
def baseEnd_3452705 : Nat := 131325720235705111815467

theorem tailTrace_3452705 : CollatzResearch.WordTrace tailWord_3452705 prefixEnd_3452705 131325720235705111815467 := by
  unfold tailWord_3452705
  simp only [CollatzResearch.WordTrace]
  refine ⟨125930496956446934912679569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83953664637631289941786379 125930496956446934912679569)
  ·
    refine ⟨94447872717335201184509677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125930496956446934912679569 94447872717335201184509677)
    ·
      refine ⟨35417952269000700444191129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94447872717335201184509677 35417952269000700444191129)
      ·
        refine ⟨26563464201750525333143347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35417952269000700444191129 26563464201750525333143347)
        ·
          refine ⟨39845196302625787999715021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26563464201750525333143347 39845196302625787999715021)
          ·
            refine ⟨14941948613484670499893133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39845196302625787999715021 14941948613484670499893133)
            ·
              refine ⟨5603230730056751437459925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14941948613484670499893133 5603230730056751437459925)
              ·
                refine ⟨131325720235705111815467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5603230730056751437459925 131325720235705111815467)
                ·
                  rfl

theorem cell22_3452705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 7].length) (baseStart_3452705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452705 prefixEnd_3452705 := by exact prefixLift 3452705
  have htrace : WordTrace (prefixWord ++ tailWord_3452705) baseStart_3452705 baseEnd_3452705 := by
    simpa [prefixWord, tailWord_3452705, baseEnd_3452705] using wordTrace_append hprefix tailTrace_3452705
  have hstable : (prefixWord ++ tailWord_3452705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452705).length < 2 ^ (prefixWord ++ tailWord_3452705).sum := by decide
  have hdescent : baseEnd_3452705 < baseStart_3452705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452722 : List Nat := [3, 2, 1, 1, 3, 3, 3, 6]
def baseStart_3452722 : Nat := 118140960795 + 3452722 * 2 ^ 59
def prefixEnd_3452722 : Nat := 4983230072969 + 3 ^ 40 * 3452722 * 2
def baseEnd_3452722 : Nat := 131326366840973736518239

theorem tailTrace_3452722 : CollatzResearch.WordTrace tailWord_3452722 prefixEnd_3452722 131326366840973736518239 := by
  unfold tailWord_3452722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31482779249346336704012105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83954077998256897877365613 31482779249346336704012105)
  ·
    refine ⟨23612084437009752528009079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31482779249346336704012105 23612084437009752528009079)
    ·
      refine ⟨35418126655514628792013619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23612084437009752528009079 35418126655514628792013619)
      ·
        refine ⟨53127189983271943188020429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35418126655514628792013619 53127189983271943188020429)
        ·
          refine ⟨19922696243726978695507661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53127189983271943188020429 19922696243726978695507661)
          ·
            refine ⟨7471011091397617010815373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19922696243726978695507661 7471011091397617010815373)
            ·
              refine ⟨2801629159274106379055765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7471011091397617010815373 2801629159274106379055765)
              ·
                refine ⟨131326366840973736518239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2801629159274106379055765 131326366840973736518239)
                ·
                  rfl

theorem cell22_3452722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_3452722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452722 prefixEnd_3452722 := by exact prefixLift 3452722
  have htrace : WordTrace (prefixWord ++ tailWord_3452722) baseStart_3452722 baseEnd_3452722 := by
    simpa [prefixWord, tailWord_3452722, baseEnd_3452722] using wordTrace_append hprefix tailTrace_3452722
  have hstable : (prefixWord ++ tailWord_3452722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452722).length < 2 ^ (prefixWord ++ tailWord_3452722).sum := by decide
  have hdescent : baseEnd_3452722 < baseStart_3452722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452724 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3452724 : Nat := 118140960795 + 3452724 * 2 ^ 59
def prefixEnd_3452724 : Nat := 4983230072969 + 3 ^ 40 * 3452724 * 2
def baseEnd_3452724 : Nat := 1181937986209636290114145

theorem tailTrace_3452724 : CollatzResearch.WordTrace tailWord_3452724 prefixEnd_3452724 1181937986209636290114145 := by
  unfold tailWord_3452724
  simp only [CollatzResearch.WordTrace]
  refine ⟨62965594971689050578810613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83954126628918734105080817 62965594971689050578810613)
  ·
    refine ⟨5903024528595848491763495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62965594971689050578810613 5903024528595848491763495)
    ·
      refine ⟨8854536792893772737645243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903024528595848491763495 8854536792893772737645243)
      ·
        refine ⟨13281805189340659106467865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8854536792893772737645243 13281805189340659106467865)
        ·
          refine ⟨9961353892005494329850899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13281805189340659106467865 9961353892005494329850899)
          ·
            refine ⟨14942030838008241494776349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961353892005494329850899 14942030838008241494776349)
            ·
              refine ⟨5603261564253090560541131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14942030838008241494776349 5603261564253090560541131)
              ·
                refine ⟨8404892346379635840811697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603261564253090560541131 8404892346379635840811697)
                ·
                  refine ⟨6303669259784726880608773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8404892346379635840811697 6303669259784726880608773)
                  ·
                    refine ⟨1181937986209636290114145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303669259784726880608773 1181937986209636290114145)
                    ·
                      rfl

theorem cell22_3452724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3452724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452724 prefixEnd_3452724 := by exact prefixLift 3452724
  have htrace : WordTrace (prefixWord ++ tailWord_3452724) baseStart_3452724 baseEnd_3452724 := by
    simpa [prefixWord, tailWord_3452724, baseEnd_3452724] using wordTrace_append hprefix tailTrace_3452724
  have hstable : (prefixWord ++ tailWord_3452724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452724).length < 2 ^ (prefixWord ++ tailWord_3452724).sum := by decide
  have hdescent : baseEnd_3452724 < baseStart_3452724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452754 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_3452754 : Nat := 118140960795 + 3452754 * 2 ^ 59
def prefixEnd_3452754 : Nat := 4983230072969 + 3 ^ 40 * 3452754 * 2
def baseEnd_3452754 : Nat := 1181948255822726211864053

theorem tailTrace_3452754 : CollatzResearch.WordTrace tailWord_3452754 prefixEnd_3452754 1181948255822726211864053 := by
  unfold tailWord_3452754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31483071033317354070303329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83954856088846277520808877 31483071033317354070303329)
  ·
    refine ⟨23612303274988015552727497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31483071033317354070303329 23612303274988015552727497)
    ·
      refine ⟨17709227456241011664545623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23612303274988015552727497 17709227456241011664545623)
      ·
        refine ⟨26563841184361517496818435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17709227456241011664545623 26563841184361517496818435)
        ·
          refine ⟨39845761776542276245227653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26563841184361517496818435 39845761776542276245227653)
          ·
            refine ⟨7471080333101676795980185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39845761776542276245227653 7471080333101676795980185)
            ·
              refine ⟨5603310249826257596985139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7471080333101676795980185 5603310249826257596985139)
              ·
                refine ⟨8404965374739386395477709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603310249826257596985139 8404965374739386395477709)
                ·
                  refine ⟨3151862015527269898304141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8404965374739386395477709 3151862015527269898304141)
                  ·
                    refine ⟨1181948255822726211864053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151862015527269898304141 1181948255822726211864053)
                    ·
                      rfl

theorem cell22_3452754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_3452754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452754 prefixEnd_3452754 := by exact prefixLift 3452754
  have htrace : WordTrace (prefixWord ++ tailWord_3452754) baseStart_3452754 baseEnd_3452754 := by
    simpa [prefixWord, tailWord_3452754, baseEnd_3452754] using wordTrace_append hprefix tailTrace_3452754
  have hstable : (prefixWord ++ tailWord_3452754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452754).length < 2 ^ (prefixWord ++ tailWord_3452754).sum := by decide
  have hdescent : baseEnd_3452754 < baseStart_3452754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452825 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_3452825 : Nat := 118140960795 + 3452825 * 2 ^ 59
def prefixEnd_3452825 : Nat := 4983230072969 + 3 ^ 40 * 3452825 * 2
def baseEnd_3452825 : Nat := 1181972560573705693338835

theorem tailTrace_3452825 : CollatzResearch.WordTrace tailWord_3452825 prefixEnd_3452825 1181972560573705693338835 := by
  unfold tailWord_3452825
  simp only [CollatzResearch.WordTrace]
  refine ⟨125934873716012195407047929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83956582477341463604698619 125934873716012195407047929)
  ·
    refine ⟨94451155287009146555285947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125934873716012195407047929 94451155287009146555285947)
    ·
      refine ⟨141676732930513719832928921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94451155287009146555285947 141676732930513719832928921)
      ·
        refine ⟨106257549697885289874696691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141676732930513719832928921 106257549697885289874696691)
        ·
          refine ⟨159386324546827934812045037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106257549697885289874696691 159386324546827934812045037)
          ·
            refine ⟨59769871705060475554516889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159386324546827934812045037 59769871705060475554516889)
            ·
              refine ⟨44827403778795356665887667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59769871705060475554516889 44827403778795356665887667)
              ·
                refine ⟨67241105668193034998831501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44827403778795356665887667 67241105668193034998831501)
                ·
                  refine ⟨25215414625572388124561813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67241105668193034998831501 25215414625572388124561813)
                  ·
                    refine ⟨1181972560573705693338835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25215414625572388124561813 1181972560573705693338835)
                    ·
                      rfl

theorem cell22_3452825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_3452825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452825 prefixEnd_3452825 := by exact prefixLift 3452825
  have htrace : WordTrace (prefixWord ++ tailWord_3452825) baseStart_3452825 baseEnd_3452825 := by
    simpa [prefixWord, tailWord_3452825, baseEnd_3452825] using wordTrace_append hprefix tailTrace_3452825
  have hstable : (prefixWord ++ tailWord_3452825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452825).length < 2 ^ (prefixWord ++ tailWord_3452825).sum := by decide
  have hdescent : baseEnd_3452825 < baseStart_3452825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452831 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 1, 4]
def baseStart_3452831 : Nat := 118140960795 + 3452831 * 2 ^ 59
def prefixEnd_3452831 : Nat := 4983230072969 + 3 ^ 40 * 3452831 * 2
def baseEnd_3452831 : Nat := 1181974614496323677688817

theorem tailTrace_3452831 : CollatzResearch.WordTrace tailWord_3452831 prefixEnd_3452831 1181974614496323677688817 := by
  unfold tailWord_3452831
  simp only [CollatzResearch.WordTrace]
  refine ⟨125935092553990458431766347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83956728369326972287844231 125935092553990458431766347)
  ·
    refine ⟨188902638830985687647649521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125935092553990458431766347 188902638830985687647649521)
    ·
      refine ⟨141676979123239265735737141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188902638830985687647649521 141676979123239265735737141)
      ·
        refine ⟨13282216792803681162725357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141676979123239265735737141 13282216792803681162725357)
        ·
          refine ⟨4980831297301380436022009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13282216792803681162725357 4980831297301380436022009)
          ·
            refine ⟨3735623472976035327016507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4980831297301380436022009 3735623472976035327016507)
            ·
              refine ⟨5603435209464052990524761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735623472976035327016507 5603435209464052990524761)
              ·
                refine ⟨4202576407098039742893571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603435209464052990524761 4202576407098039742893571)
                ·
                  refine ⟨6303864610647059614340357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202576407098039742893571 6303864610647059614340357)
                  ·
                    refine ⟨1181974614496323677688817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303864610647059614340357 1181974614496323677688817)
                    ·
                      rfl

theorem cell22_3452831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_3452831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452831 prefixEnd_3452831 := by exact prefixLift 3452831
  have htrace : WordTrace (prefixWord ++ tailWord_3452831) baseStart_3452831 baseEnd_3452831 := by
    simpa [prefixWord, tailWord_3452831, baseEnd_3452831] using wordTrace_append hprefix tailTrace_3452831
  have hstable : (prefixWord ++ tailWord_3452831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452831).length < 2 ^ (prefixWord ++ tailWord_3452831).sum := by decide
  have hdescent : baseEnd_3452831 < baseStart_3452831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452861 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_3452861 : Nat := 118140960795 + 3452861 * 2 ^ 59
def prefixEnd_3452861 : Nat := 4983230072969 + 3 ^ 40 * 3452861 * 2
def baseEnd_3452861 : Nat := 1181984884109413599438725

theorem tailTrace_3452861 : CollatzResearch.WordTrace tailWord_3452861 prefixEnd_3452861 1181984884109413599438725 := by
  unfold tailWord_3452861
  simp only [CollatzResearch.WordTrace]
  refine ⟨125936186743881773555358437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83957457829254515703572291 125936186743881773555358437)
  ·
    refine ⟨23613035014477832541629707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125936186743881773555358437 23613035014477832541629707)
    ·
      refine ⟨35419552521716748812444561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23613035014477832541629707 35419552521716748812444561)
      ·
        refine ⟨26564664391287561609333421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35419552521716748812444561 26564664391287561609333421)
        ·
          refine ⟨9961749146732835603500033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26564664391287561609333421 9961749146732835603500033)
          ·
            refine ⟨7471311860049626702625025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9961749146732835603500033 7471311860049626702625025)
            ·
              refine ⟨5603483895037220026968769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7471311860049626702625025 5603483895037220026968769)
              ·
                refine ⟨4202612921277915020226577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603483895037220026968769 4202612921277915020226577)
                ·
                  refine ⟨3151959690958436265169933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202612921277915020226577 3151959690958436265169933)
                  ·
                    refine ⟨1181984884109413599438725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151959690958436265169933 1181984884109413599438725)
                    ·
                      rfl

theorem cell22_3452861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_3452861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452861 prefixEnd_3452861 := by exact prefixLift 3452861
  have htrace : WordTrace (prefixWord ++ tailWord_3452861) baseStart_3452861 baseEnd_3452861 := by
    simpa [prefixWord, tailWord_3452861, baseEnd_3452861] using wordTrace_append hprefix tailTrace_3452861
  have hstable : (prefixWord ++ tailWord_3452861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452861).length < 2 ^ (prefixWord ++ tailWord_3452861).sum := by decide
  have hdescent : baseEnd_3452861 < baseStart_3452861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452893 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_3452893 : Nat := 118140960795 + 3452893 * 2 ^ 59
def prefixEnd_3452893 : Nat := 4983230072969 + 3 ^ 40 * 3452893 * 2
def baseEnd_3452893 : Nat := 1181995838363376182638627

theorem tailTrace_3452893 : CollatzResearch.WordTrace tailWord_3452893 prefixEnd_3452893 1181995838363376182638627 := by
  unfold tailWord_3452893
  simp only [CollatzResearch.WordTrace]
  refine ⟨125937353879765843020523333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83958235919843895347015555 125937353879765843020523333)
  ·
    refine ⟨23613253852456095566348125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125937353879765843020523333 23613253852456095566348125)
    ·
      refine ⟨8854970194671035837380547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23613253852456095566348125 8854970194671035837380547)
      ·
        refine ⟨13282455292006553756070821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8854970194671035837380547 13282455292006553756070821)
        ·
          refine ⟨2490460367251228829263279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13282455292006553756070821 2490460367251228829263279)
          ·
            refine ⟨3735690550876843243894919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490460367251228829263279 3735690550876843243894919)
            ·
              refine ⟨5603535826315264865842379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735690550876843243894919 5603535826315264865842379)
              ·
                refine ⟨8405303739472897298763569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603535826315264865842379 8405303739472897298763569)
                ·
                  refine ⟨6303977804604672974072677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8405303739472897298763569 6303977804604672974072677)
                  ·
                    refine ⟨1181995838363376182638627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303977804604672974072677 1181995838363376182638627)
                    ·
                      rfl

theorem cell22_3452893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_3452893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452893 prefixEnd_3452893 := by exact prefixLift 3452893
  have htrace : WordTrace (prefixWord ++ tailWord_3452893) baseStart_3452893 baseEnd_3452893 := by
    simpa [prefixWord, tailWord_3452893, baseEnd_3452893] using wordTrace_append hprefix tailTrace_3452893
  have hstable : (prefixWord ++ tailWord_3452893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452893).length < 2 ^ (prefixWord ++ tailWord_3452893).sum := by decide
  have hdescent : baseEnd_3452893 < baseStart_3452893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452947 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 6]
def baseStart_3452947 : Nat := 118140960795 + 3452947 * 2 ^ 59
def prefixEnd_3452947 : Nat := 4983230072969 + 3 ^ 40 * 3452947 * 2
def baseEnd_3452947 : Nat := 394004774555646013929487

theorem tailTrace_3452947 : CollatzResearch.WordTrace tailWord_3452947 prefixEnd_3452947 394004774555646013929487 := by
  unfold tailWord_3452947
  simp only [CollatzResearch.WordTrace]
  refine ⟨125939323421570210242989095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83959548947713473495326063 125939323421570210242989095)
  ·
    refine ⟨188908985132355315364483643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125939323421570210242989095 188908985132355315364483643)
    ·
      refine ⟨283363477698532973046725465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188908985132355315364483643 283363477698532973046725465)
      ·
        refine ⟨212522608273899729785044099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283363477698532973046725465 212522608273899729785044099)
        ·
          refine ⟨318783912410849594677566149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212522608273899729785044099 318783912410849594677566149)
          ·
            refine ⟨59771983577034299002043653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318783912410849594677566149 59771983577034299002043653)
            ·
              refine ⟨11207246920693931062883185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59771983577034299002043653 11207246920693931062883185)
              ·
                refine ⟨8405435190520448297162389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11207246920693931062883185 8405435190520448297162389)
                ·
                  refine ⟨394004774555646013929487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8405435190520448297162389 394004774555646013929487)
                  ·
                    rfl

theorem cell22_3452947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 6].length) (baseStart_3452947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452947 prefixEnd_3452947 := by exact prefixLift 3452947
  have htrace : WordTrace (prefixWord ++ tailWord_3452947) baseStart_3452947 baseEnd_3452947 := by
    simpa [prefixWord, tailWord_3452947, baseEnd_3452947] using wordTrace_append hprefix tailTrace_3452947
  have hstable : (prefixWord ++ tailWord_3452947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452947).length < 2 ^ (prefixWord ++ tailWord_3452947).sum := by decide
  have hdescent : baseEnd_3452947 < baseStart_3452947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452979 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 4, 3]
def baseStart_3452979 : Nat := 118140960795 + 3452979 * 2 ^ 59
def prefixEnd_3452979 : Nat := 4983230072969 + 3 ^ 40 * 3452979 * 2
def baseEnd_3452979 : Nat := 1182025277920900624988363

theorem tailTrace_3452979 : CollatzResearch.WordTrace tailWord_3452979 prefixEnd_3452979 1182025277920900624988363 := by
  unfold tailWord_3452979
  simp only [CollatzResearch.WordTrace]
  refine ⟨125940490557454279708153991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83960327038302853138769327 125940490557454279708153991)
  ·
    refine ⟨188910735836181419562230987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125940490557454279708153991 188910735836181419562230987)
    ·
      refine ⟨283366103754272129343346481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188910735836181419562230987 283366103754272129343346481)
      ·
        refine ⟨212524577815704097007509861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283366103754272129343346481 212524577815704097007509861)
        ·
          refine ⟨39848358340444518188908099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212524577815704097007509861 39848358340444518188908099)
          ·
            refine ⟨59772537510666777283362149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39848358340444518188908099 59772537510666777283362149)
            ·
              refine ⟨11207350783250020740630403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59772537510666777283362149 11207350783250020740630403)
              ·
                refine ⟨16811026174875031110945605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11207350783250020740630403 16811026174875031110945605)
                ·
                  refine ⟨3152067407789068333302301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16811026174875031110945605 3152067407789068333302301)
                  ·
                    refine ⟨1182025277920900624988363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152067407789068333302301 1182025277920900624988363)
                    ·
                      rfl

theorem cell22_3452979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 3].length) (baseStart_3452979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452979 prefixEnd_3452979 := by exact prefixLift 3452979
  have htrace : WordTrace (prefixWord ++ tailWord_3452979) baseStart_3452979 baseEnd_3452979 := by
    simpa [prefixWord, tailWord_3452979, baseEnd_3452979] using wordTrace_append hprefix tailTrace_3452979
  have hstable : (prefixWord ++ tailWord_3452979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452979).length < 2 ^ (prefixWord ++ tailWord_3452979).sum := by decide
  have hdescent : baseEnd_3452979 < baseStart_3452979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452992 : List Nat := [2, 1, 1, 2, 2, 4, 1, 9]
def baseStart_3452992 : Nat := 118140960795 + 3452992 * 2 ^ 59
def prefixEnd_3452992 : Nat := 4983230072969 + 3 ^ 40 * 3452992 * 2
def baseEnd_3452992 : Nat := 131336636454063658268147

theorem tailTrace_3452992 : CollatzResearch.WordTrace tailWord_3452992 prefixEnd_3452992 131336636454063658268147 := by
  unfold tailWord_3452992
  simp only [CollatzResearch.WordTrace]
  refine ⟨62970482353203591464188615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83960643137604788618918153 62970482353203591464188615)
  ·
    refine ⟨94455723529805387196282923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62970482353203591464188615 94455723529805387196282923)
    ·
      refine ⟨141683585294708080794424385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94455723529805387196282923 141683585294708080794424385)
      ·
        refine ⟨106262688971031060595818289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141683585294708080794424385 106262688971031060595818289)
        ·
          refine ⟨79697016728273295446863717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106262688971031060595818289 79697016728273295446863717)
          ·
            refine ⟨14943190636551242896286947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79697016728273295446863717 14943190636551242896286947)
            ·
              refine ⟨22414785954826864344430421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14943190636551242896286947 22414785954826864344430421)
              ·
                refine ⟨131336636454063658268147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22414785954826864344430421 131336636454063658268147)
                ·
                  rfl

theorem cell22_3452992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_3452992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3452992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3452992 prefixEnd_3452992 := by exact prefixLift 3452992
  have htrace : WordTrace (prefixWord ++ tailWord_3452992) baseStart_3452992 baseEnd_3452992 := by
    simpa [prefixWord, tailWord_3452992, baseEnd_3452992] using wordTrace_append hprefix tailTrace_3452992
  have hstable : (prefixWord ++ tailWord_3452992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452992).length < 2 ^ (prefixWord ++ tailWord_3452992).sum := by decide
  have hdescent : baseEnd_3452992 < baseStart_3452992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453026 : List Nat := [3, 3, 2, 2, 3, 9]
def baseStart_3453026 : Nat := 118140960795 + 3453026 * 2 ^ 59
def prefixEnd_3453026 : Nat := 4983230072969 + 3 ^ 40 * 3453026 * 2
def baseEnd_3453026 : Nat := 14593103296066767519299

theorem tailTrace_3453026 : CollatzResearch.WordTrace tailWord_3453026 prefixEnd_3453026 14593103296066767519299 := by
  unfold tailWord_3453026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31485551197071001683778733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83961469858856004490076621 31485551197071001683778733)
  ·
    refine ⟨11807081698901625631417025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31485551197071001683778733 11807081698901625631417025)
    ·
      refine ⟨8855311274176219223562769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11807081698901625631417025 8855311274176219223562769)
      ·
        refine ⟨6641483455632164417672077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8855311274176219223562769 6641483455632164417672077)
        ·
          refine ⟨2490556295862061656627029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6641483455632164417672077 2490556295862061656627029)
          ·
            refine ⟨14593103296066767519299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2490556295862061656627029 14593103296066767519299)
            ·
              rfl

theorem cell22_3453026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 9].length) (baseStart_3453026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453026 prefixEnd_3453026 := by exact prefixLift 3453026
  have htrace : WordTrace (prefixWord ++ tailWord_3453026) baseStart_3453026 baseEnd_3453026 := by
    simpa [prefixWord, tailWord_3453026, baseEnd_3453026] using wordTrace_append hprefix tailTrace_3453026
  have hstable : (prefixWord ++ tailWord_3453026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453026).length < 2 ^ (prefixWord ++ tailWord_3453026).sum := by decide
  have hdescent : baseEnd_3453026 < baseStart_3453026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453144 : List Nat := [2, 1, 2, 2, 4, 1, 10]
def baseStart_3453144 : Nat := 118140960795 + 3453144 * 2 ^ 59
def prefixEnd_3453144 : Nat := 4983230072969 + 3 ^ 40 * 3453144 * 2
def baseEnd_3453144 : Nat := 43780805955292414615291

theorem tailTrace_3453144 : CollatzResearch.WordTrace tailWord_3453144 prefixEnd_3453144 43780805955292414615291 := by
  unfold tailWord_3453144
  simp only [CollatzResearch.WordTrace]
  refine ⟨62973254300928256443955243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83964339067904341925273657 62973254300928256443955243)
  ·
    refine ⟨94459881451392384665932865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62973254300928256443955243 94459881451392384665932865)
    ·
      refine ⟨70844911088544288499449649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94459881451392384665932865 70844911088544288499449649)
      ·
        refine ⟨53133683316408216374587237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70844911088544288499449649 53133683316408216374587237)
        ·
          refine ⟨9962565621826540570235107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53133683316408216374587237 9962565621826540570235107)
          ·
            refine ⟨14943848432739810855352661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9962565621826540570235107 14943848432739810855352661)
            ·
              refine ⟨43780805955292414615291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14943848432739810855352661 43780805955292414615291)
              ·
                rfl

theorem cell22_3453144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 10].length) (baseStart_3453144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453144 prefixEnd_3453144 := by exact prefixLift 3453144
  have htrace : WordTrace (prefixWord ++ tailWord_3453144) baseStart_3453144 baseEnd_3453144 := by
    simpa [prefixWord, tailWord_3453144, baseEnd_3453144] using wordTrace_append hprefix tailTrace_3453144
  have hstable : (prefixWord ++ tailWord_3453144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453144).length < 2 ^ (prefixWord ++ tailWord_3453144).sum := by decide
  have hdescent : baseEnd_3453144 < baseStart_3453144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453165 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_3453165 : Nat := 118140960795 + 3453165 * 2 ^ 59
def prefixEnd_3453165 : Nat := 4983230072969 + 3 ^ 40 * 3453165 * 2
def baseEnd_3453165 : Nat := 1182088949522058139837793

theorem tailTrace_3453165 : CollatzResearch.WordTrace tailWord_3453165 prefixEnd_3453165 1182088949522058139837793 := by
  unfold tailWord_3453165
  simp only [CollatzResearch.WordTrace]
  refine ⟨125947274534780433474424949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83964849689853622316283299 125947274534780433474424949)
  ·
    refine ⟨11807556987635665638227339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125947274534780433474424949 11807556987635665638227339)
    ·
      refine ⟨17711335481453498457341009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807556987635665638227339 17711335481453498457341009)
      ·
        refine ⟨13283501611090123843005757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17711335481453498457341009 13283501611090123843005757)
        ·
          refine ⟨4981313104158796441127159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13283501611090123843005757 4981313104158796441127159)
          ·
            refine ⟨7471969656238194661690739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981313104158796441127159 7471969656238194661690739)
            ·
              refine ⟨11207954484357291992536109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471969656238194661690739 11207954484357291992536109)
              ·
                refine ⟨4202982931633984497201041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11207954484357291992536109 4202982931633984497201041)
                ·
                  refine ⟨3152237198725488372900781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202982931633984497201041 3152237198725488372900781)
                  ·
                    refine ⟨1182088949522058139837793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152237198725488372900781 1182088949522058139837793)
                    ·
                      rfl

theorem cell22_3453165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_3453165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453165 prefixEnd_3453165 := by exact prefixLift 3453165
  have htrace : WordTrace (prefixWord ++ tailWord_3453165) baseStart_3453165 baseEnd_3453165 := by
    simpa [prefixWord, tailWord_3453165, baseEnd_3453165] using wordTrace_append hprefix tailTrace_3453165
  have hstable : (prefixWord ++ tailWord_3453165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453165).length < 2 ^ (prefixWord ++ tailWord_3453165).sum := by decide
  have hdescent : baseEnd_3453165 < baseStart_3453165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453176 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 3, 3]
def baseStart_3453176 : Nat := 118140960795 + 3453176 * 2 ^ 59
def prefixEnd_3453176 : Nat := 4983230072969 + 3 ^ 40 * 3453176 * 2
def baseEnd_3453176 : Nat := 1182092715046857777812759

theorem tailTrace_3453176 : CollatzResearch.WordTrace tailWord_3453176 prefixEnd_3453176 1182092715046857777812759 := by
  unfold tailWord_3453176
  simp only [CollatzResearch.WordTrace]
  refine ⟨62973837868870291176537691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83965117158493721568716921 62973837868870291176537691)
  ·
    refine ⟨94460756803305436764806537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62973837868870291176537691 94460756803305436764806537)
    ·
      refine ⟨70845567602479077573604903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94460756803305436764806537 70845567602479077573604903)
      ·
        refine ⟨106268351403718616360407355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70845567602479077573604903 106268351403718616360407355)
        ·
          refine ⟨159402527105577924540611033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106268351403718616360407355 159402527105577924540611033)
          ·
            refine ⟨119551895329183443405458275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159402527105577924540611033 119551895329183443405458275)
            ·
              refine ⟨179327842993775165108187413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119551895329183443405458275 179327842993775165108187413)
              ·
                refine ⟨8405992640333210864446285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179327842993775165108187413 8405992640333210864446285)
                ·
                  refine ⟨3152247240124954074167357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8405992640333210864446285 3152247240124954074167357)
                  ·
                    refine ⟨1182092715046857777812759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152247240124954074167357 1182092715046857777812759)
                    ·
                      rfl

theorem cell22_3453176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_3453176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453176 prefixEnd_3453176 := by exact prefixLift 3453176
  have htrace : WordTrace (prefixWord ++ tailWord_3453176) baseStart_3453176 baseEnd_3453176 := by
    simpa [prefixWord, tailWord_3453176, baseEnd_3453176] using wordTrace_append hprefix tailTrace_3453176
  have hstable : (prefixWord ++ tailWord_3453176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453176).length < 2 ^ (prefixWord ++ tailWord_3453176).sum := by decide
  have hdescent : baseEnd_3453176 < baseStart_3453176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453189 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 7]
def baseStart_3453189 : Nat := 118140960795 + 3453189 * 2 ^ 59
def prefixEnd_3453189 : Nat := 4983230072969 + 3 ^ 40 * 3453189 * 2
def baseEnd_3453189 : Nat := 394032388404176692412573

theorem tailTrace_3453189 : CollatzResearch.WordTrace tailWord_3453189 prefixEnd_3453189 394032388404176692412573 := by
  unfold tailWord_3453189
  simp only [CollatzResearch.WordTrace]
  refine ⟨125948149886693485573298621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83965433257795657048865747 125948149886693485573298621)
  ·
    refine ⟨47230556207510057089986983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125948149886693485573298621 47230556207510057089986983)
    ·
      refine ⟨70845834311265085634980475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47230556207510057089986983 70845834311265085634980475)
      ·
        refine ⟨106268751466897628452470713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70845834311265085634980475 106268751466897628452470713)
        ·
          refine ⟨79701563600173221339353035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106268751466897628452470713 79701563600173221339353035)
          ·
            refine ⟨119552345400259832009029553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79701563600173221339353035 119552345400259832009029553)
            ·
              refine ⟨89664259050194874006772165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119552345400259832009029553 89664259050194874006772165)
              ·
                refine ⟨16812048571911538876269781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89664259050194874006772165 16812048571911538876269781)
                ·
                  refine ⟨394032388404176692412573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16812048571911538876269781 394032388404176692412573)
                  ·
                    rfl

theorem cell22_3453189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_3453189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453189 prefixEnd_3453189 := by exact prefixLift 3453189
  have htrace : WordTrace (prefixWord ++ tailWord_3453189) baseStart_3453189 baseEnd_3453189 := by
    simpa [prefixWord, tailWord_3453189, baseEnd_3453189] using wordTrace_append hprefix tailTrace_3453189
  have hstable : (prefixWord ++ tailWord_3453189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453189).length < 2 ^ (prefixWord ++ tailWord_3453189).sum := by decide
  have hdescent : baseEnd_3453189 < baseStart_3453189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453266 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3453266 : Nat := 118140960795 + 3453266 * 2 ^ 59
def prefixEnd_3453266 : Nat := 4983230072969 + 3 ^ 40 * 3453266 * 2
def baseEnd_3453266 : Nat := 1182123523886127543062483

theorem tailTrace_3453266 : CollatzResearch.WordTrace tailWord_3453266 prefixEnd_3453266 1182123523886127543062483 := by
  unfold tailWord_3453266
  simp only [CollatzResearch.WordTrace]
  refine ⟨31487739576853631930962913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83967305538276351815901101 31487739576853631930962913)
  ·
    refine ⟨23615804682640223948222185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31487739576853631930962913 23615804682640223948222185)
    ·
      refine ⟨17711853511980167961166639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23615804682640223948222185 17711853511980167961166639)
      ·
        refine ⟨26567780267970251941749959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17711853511980167961166639 26567780267970251941749959)
        ·
          refine ⟨39851670401955377912624939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26567780267970251941749959 39851670401955377912624939)
          ·
            refine ⟨59777505602933066868937409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39851670401955377912624939 59777505602933066868937409)
            ·
              refine ⟨44833129202199800151703057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59777505602933066868937409 44833129202199800151703057)
              ·
                refine ⟨33624846901649850113777293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44833129202199800151703057 33624846901649850113777293)
                ·
                  refine ⟨12609317588118693792666485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33624846901649850113777293 12609317588118693792666485)
                  ·
                    refine ⟨1182123523886127543062483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12609317588118693792666485 1182123523886127543062483)
                    ·
                      rfl

theorem cell22_3453266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3453266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453266 prefixEnd_3453266 := by exact prefixLift 3453266
  have htrace : WordTrace (prefixWord ++ tailWord_3453266) baseStart_3453266 baseEnd_3453266 := by
    simpa [prefixWord, tailWord_3453266, baseEnd_3453266] using wordTrace_append hprefix tailTrace_3453266
  have hstable : (prefixWord ++ tailWord_3453266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453266).length < 2 ^ (prefixWord ++ tailWord_3453266).sum := by decide
  have hdescent : baseEnd_3453266 < baseStart_3453266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453268 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3453268 : Nat := 118140960795 + 3453268 * 2 ^ 59
def prefixEnd_3453268 : Nat := 4983230072969 + 3 ^ 40 * 3453268 * 2
def baseEnd_3453268 : Nat := 394041402842333401504159

theorem tailTrace_3453268 : CollatzResearch.WordTrace tailWord_3453268 prefixEnd_3453268 394041402842333401504159 := by
  unfold tailWord_3453268
  simp only [CollatzResearch.WordTrace]
  refine ⟨62975515626703641032712229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83967354168938188043616305 62975515626703641032712229)
  ·
    refine ⟨11807909180006932693633543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62975515626703641032712229 11807909180006932693633543)
    ·
      refine ⟨17711863770010399040450315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807909180006932693633543 17711863770010399040450315)
      ·
        refine ⟨26567795655015598560675473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17711863770010399040450315 26567795655015598560675473)
        ·
          refine ⟨19925846741261698920506605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26567795655015598560675473 19925846741261698920506605)
          ·
            refine ⟨7472192527973137095189977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19925846741261698920506605 7472192527973137095189977)
            ·
              refine ⟨5604144395979852821392483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7472192527973137095189977 5604144395979852821392483)
              ·
                refine ⟨8406216593969779232088725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604144395979852821392483 8406216593969779232088725)
                ·
                  refine ⟨394041402842333401504159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8406216593969779232088725 394041402842333401504159)
                  ·
                    rfl

theorem cell22_3453268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3453268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453268 prefixEnd_3453268 := by exact prefixLift 3453268
  have htrace : WordTrace (prefixWord ++ tailWord_3453268) baseStart_3453268 baseEnd_3453268 := by
    simpa [prefixWord, tailWord_3453268, baseEnd_3453268] using wordTrace_append hprefix tailTrace_3453268
  have hstable : (prefixWord ++ tailWord_3453268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453268).length < 2 ^ (prefixWord ++ tailWord_3453268).sum := by decide
  have hdescent : baseEnd_3453268 < baseStart_3453268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453296 : List Nat := [2, 1, 1, 1, 4, 4, 1, 8]
def baseStart_3453296 : Nat := 118140960795 + 3453296 * 2 ^ 59
def prefixEnd_3453296 : Nat := 4983230072969 + 3 ^ 40 * 3453296 * 2
def baseEnd_3453296 : Nat := 131348199277690829423599

theorem tailTrace_3453296 : CollatzResearch.WordTrace tailWord_3453296 prefixEnd_3453296 131348199277690829423599 := by
  unfold tailWord_3453296
  simp only [CollatzResearch.WordTrace]
  refine ⟨62976026248652921423721871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83968034998203895231629161 62976026248652921423721871)
  ·
    refine ⟨94464039372979382135582807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62976026248652921423721871 94464039372979382135582807)
    ·
      refine ⟨141696059059469073203374211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94464039372979382135582807 141696059059469073203374211)
      ·
        refine ⟨212544088589203609805061317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141696059059469073203374211 212544088589203609805061317)
        ·
          refine ⟨39852016610475676838448997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212544088589203609805061317 39852016610475676838448997)
          ·
            refine ⟨7472253114464189407209187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39852016610475676838448997 7472253114464189407209187)
            ·
              refine ⟨11208379671696284110813781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472253114464189407209187 11208379671696284110813781)
              ·
                refine ⟨131348199277690829423599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11208379671696284110813781 131348199277690829423599)
                ·
                  rfl

theorem cell22_3453296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_3453296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453296 prefixEnd_3453296 := by exact prefixLift 3453296
  have htrace : WordTrace (prefixWord ++ tailWord_3453296) baseStart_3453296 baseEnd_3453296 := by
    simpa [prefixWord, tailWord_3453296, baseEnd_3453296] using wordTrace_append hprefix tailTrace_3453296
  have hstable : (prefixWord ++ tailWord_3453296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453296).length < 2 ^ (prefixWord ++ tailWord_3453296).sum := by decide
  have hdescent : baseEnd_3453296 < baseStart_3453296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453313 : List Nat := [1, 2, 4, 3, 1, 3, 8]
def baseStart_3453313 : Nat := 118140960795 + 3453313 * 2 ^ 59
def prefixEnd_3453313 : Nat := 4983230072969 + 3 ^ 40 * 3453313 * 2
def baseEnd_3453313 : Nat := 43782948627653151375457

theorem tailTrace_3453313 : CollatzResearch.WordTrace tailWord_3453313 prefixEnd_3453313 43782948627653151375457 := by
  unfold tailWord_3453313
  simp only [CollatzResearch.WordTrace]
  refine ⟨125952672538244254750812593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83968448358829503167208395 125952672538244254750812593)
  ·
    refine ⟨94464504403683191063109445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125952672538244254750812593 94464504403683191063109445)
    ·
      refine ⟨17712094575690598324333021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94464504403683191063109445 17712094575690598324333021)
      ·
        refine ⟨6642035465883974371624883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17712094575690598324333021 6642035465883974371624883)
        ·
          refine ⟨9963053198825961557437325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6642035465883974371624883 9963053198825961557437325)
          ·
            refine ⟨3736144949559735584038997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9963053198825961557437325 3736144949559735584038997)
            ·
              refine ⟨43782948627653151375457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3736144949559735584038997 43782948627653151375457)
              ·
                rfl

theorem cell22_3453313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 8].length) (baseStart_3453313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453313 prefixEnd_3453313 := by exact prefixLift 3453313
  have htrace : WordTrace (prefixWord ++ tailWord_3453313) baseStart_3453313 baseEnd_3453313 := by
    simpa [prefixWord, tailWord_3453313, baseEnd_3453313] using wordTrace_append hprefix tailTrace_3453313
  have hstable : (prefixWord ++ tailWord_3453313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453313).length < 2 ^ (prefixWord ++ tailWord_3453313).sum := by decide
  have hdescent : baseEnd_3453313 < baseStart_3453313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453356 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_3453356 : Nat := 118140960795 + 3453356 * 2 ^ 59
def prefixEnd_3453356 : Nat := 4983230072969 + 3 ^ 40 * 3453356 * 2
def baseEnd_3453356 : Nat := 1182154332725397308312207

theorem tailTrace_3453356 : CollatzResearch.WordTrace tailWord_3453356 prefixEnd_3453356 1182154332725397308312207 := by
  unfold tailWord_3453356
  simp only [CollatzResearch.WordTrace]
  refine ⟨62977120438544236547313961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83969493918058982063085281 62977120438544236547313961)
  ·
    refine ⟨47232840328908177410485471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62977120438544236547313961 47232840328908177410485471)
    ·
      refine ⟨70849260493362266115728207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47232840328908177410485471 70849260493362266115728207)
      ·
        refine ⟨106273890740043399173592311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70849260493362266115728207 106273890740043399173592311)
        ·
          refine ⟨159410836110065098760388467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106273890740043399173592311 159410836110065098760388467)
          ·
            refine ⟨239116254165097648140582701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159410836110065098760388467 239116254165097648140582701)
            ·
              refine ⟨89668595311911618052718513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239116254165097648140582701 89668595311911618052718513)
              ·
                refine ⟨67251446483933713539538885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89668595311911618052718513 67251446483933713539538885)
                ·
                  refine ⟨12609646215737571288663541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67251446483933713539538885 12609646215737571288663541)
                  ·
                    refine ⟨1182154332725397308312207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12609646215737571288663541 1182154332725397308312207)
                    ·
                      rfl

theorem cell22_3453356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_3453356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453356 prefixEnd_3453356 := by exact prefixLift 3453356
  have htrace : WordTrace (prefixWord ++ tailWord_3453356) baseStart_3453356 baseEnd_3453356 := by
    simpa [prefixWord, tailWord_3453356, baseEnd_3453356] using wordTrace_append hprefix tailTrace_3453356
  have hstable : (prefixWord ++ tailWord_3453356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453356).length < 2 ^ (prefixWord ++ tailWord_3453356).sum := by decide
  have hdescent : baseEnd_3453356 < baseStart_3453356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453405 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3453405 : Nat := 118140960795 + 3453405 * 2 ^ 59
def prefixEnd_3453405 : Nat := 4983230072969 + 3 ^ 40 * 3453405 * 2
def baseEnd_3453405 : Nat := 1182171106426777513837057

theorem tailTrace_3453405 : CollatzResearch.WordTrace tailWord_3453405 prefixEnd_3453405 1182171106426777513837057 := by
  unfold tailWord_3453405
  simp only [CollatzResearch.WordTrace]
  refine ⟨125956028053910954463161669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83970685369273969642107779 125956028053910954463161669)
  ·
    refine ⟨23616755260108303961842813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125956028053910954463161669 23616755260108303961842813)
    ·
      refine ⟨8856283222540613985691055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23616755260108303961842813 8856283222540613985691055)
      ·
        refine ⟨13284424833810920978536583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8856283222540613985691055 13284424833810920978536583)
        ·
          refine ⟨19926637250716381467804875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13284424833810920978536583 19926637250716381467804875)
          ·
            refine ⟨29889955876074572201707313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19926637250716381467804875 29889955876074572201707313)
            ·
              refine ⟨22417466907055929151280485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29889955876074572201707313 22417466907055929151280485)
              ·
                refine ⟨4203275045072986715865091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22417466907055929151280485 4203275045072986715865091)
                ·
                  refine ⟨6304912567609480073797637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203275045072986715865091 6304912567609480073797637)
                  ·
                    refine ⟨1182171106426777513837057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6304912567609480073797637 1182171106426777513837057)
                    ·
                      rfl

theorem cell22_3453405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3453405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453405 prefixEnd_3453405 := by exact prefixLift 3453405
  have htrace : WordTrace (prefixWord ++ tailWord_3453405) baseStart_3453405 baseEnd_3453405 := by
    simpa [prefixWord, tailWord_3453405, baseEnd_3453405] using wordTrace_append hprefix tailTrace_3453405
  have hstable : (prefixWord ++ tailWord_3453405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453405).length < 2 ^ (prefixWord ++ tailWord_3453405).sum := by decide
  have hdescent : baseEnd_3453405 < baseStart_3453405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453420 : List Nat := [2, 2, 1, 1, 2, 1, 6, 3, 4]
def baseStart_3453420 : Nat := 118140960795 + 3453420 * 2 ^ 59
def prefixEnd_3453420 : Nat := 4983230072969 + 3 ^ 40 * 3453420 * 2
def baseEnd_3453420 : Nat := 394058747077774158237337

theorem tailTrace_3453420 : CollatzResearch.WordTrace tailWord_3453420 prefixEnd_3453420 394058747077774158237337 := by
  unfold tailWord_3453420
  simp only [CollatzResearch.WordTrace]
  refine ⟨62978287574428306012478857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83971050099237741349971809 62978287574428306012478857)
  ·
    refine ⟨47233715680821229509359143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62978287574428306012478857 47233715680821229509359143)
    ·
      refine ⟨70850573521231844264038715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47233715680821229509359143 70850573521231844264038715)
      ·
        refine ⟨106275860281847766396058073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70850573521231844264038715 106275860281847766396058073)
        ·
          refine ⟨79706895211385824797043555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106275860281847766396058073 79706895211385824797043555)
          ·
            refine ⟨119560342817078737195565333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79706895211385824797043555 119560342817078737195565333)
            ·
              refine ⟨5604391069550565806042125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119560342817078737195565333 5604391069550565806042125)
              ·
                refine ⟨2101646651081462177265797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5604391069550565806042125 2101646651081462177265797)
                ·
                  refine ⟨394058747077774158237337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101646651081462177265797 394058747077774158237337)
                  ·
                    rfl

theorem cell22_3453420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_3453420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453420 prefixEnd_3453420 := by exact prefixLift 3453420
  have htrace : WordTrace (prefixWord ++ tailWord_3453420) baseStart_3453420 baseEnd_3453420 := by
    simpa [prefixWord, tailWord_3453420, baseEnd_3453420] using wordTrace_append hprefix tailTrace_3453420
  have hstable : (prefixWord ++ tailWord_3453420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453420).length < 2 ^ (prefixWord ++ tailWord_3453420).sum := by decide
  have hdescent : baseEnd_3453420 < baseStart_3453420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453422 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3453422 : Nat := 118140960795 + 3453422 * 2 ^ 59
def prefixEnd_3453422 : Nat := 4983230072969 + 3 ^ 40 * 3453422 * 2
def baseEnd_3453422 : Nat := 1182176925874195136162005

theorem tailTrace_3453422 : CollatzResearch.WordTrace tailWord_3453422 prefixEnd_3453422 1182176925874195136162005 := by
  unfold tailWord_3453422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15744581011856170795816315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83971098729899577577687013 15744581011856170795816315)
  ·
    refine ⟨23616871517784256193724473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15744581011856170795816315 23616871517784256193724473)
    ·
      refine ⟨17712653638338192145293355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23616871517784256193724473 17712653638338192145293355)
      ·
        refine ⟨26568980457507288217940033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17712653638338192145293355 26568980457507288217940033)
        ·
          refine ⟨19926735343130466163455025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26568980457507288217940033 19926735343130466163455025)
          ·
            refine ⟨14945051507347849622591269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19926735343130466163455025 14945051507347849622591269)
            ·
              refine ⟨2802197157627721804235863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14945051507347849622591269 2802197157627721804235863)
              ·
                refine ⟨4203295736441582706353795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802197157627721804235863 4203295736441582706353795)
                ·
                  refine ⟨6304943604662374059530693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203295736441582706353795 6304943604662374059530693)
                  ·
                    refine ⟨1182176925874195136162005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6304943604662374059530693 1182176925874195136162005)
                    ·
                      rfl

theorem cell22_3453422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3453422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453422 prefixEnd_3453422 := by exact prefixLift 3453422
  have htrace : WordTrace (prefixWord ++ tailWord_3453422) baseStart_3453422 baseEnd_3453422 := by
    simpa [prefixWord, tailWord_3453422, baseEnd_3453422] using wordTrace_append hprefix tailTrace_3453422
  have hstable : (prefixWord ++ tailWord_3453422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453422).length < 2 ^ (prefixWord ++ tailWord_3453422).sum := by decide
  have hdescent : baseEnd_3453422 < baseStart_3453422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453433 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_3453433 : Nat := 118140960795 + 3453433 * 2 ^ 59
def prefixEnd_3453433 : Nat := 4983230072969 + 3 ^ 40 * 3453433 * 2
def baseEnd_3453433 : Nat := 1182180691398994774136971

theorem tailTrace_3453433 : CollatzResearch.WordTrace tailWord_3453433 prefixEnd_3453433 1182180691398994774136971 := by
  unfold tailWord_3453433
  simp only [CollatzResearch.WordTrace]
  refine ⟨125957049297809515245180953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83971366198539676830120635 125957049297809515245180953)
  ·
    refine ⟨94467786973357136433885715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125957049297809515245180953 94467786973357136433885715)
    ·
      refine ⟨141701680460035704650828573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94467786973357136433885715 141701680460035704650828573)
      ·
        refine ⟨53138130172513389244060715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141701680460035704650828573 53138130172513389244060715)
        ·
          refine ⟨79707195258770083866091073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53138130172513389244060715 79707195258770083866091073)
          ·
            refine ⟨59780396444077562899568305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79707195258770083866091073 59780396444077562899568305)
            ·
              refine ⟨44835297333058172174676229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59780396444077562899568305 44835297333058172174676229)
              ·
                refine ⟨8406618249948407282751793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44835297333058172174676229 8406618249948407282751793)
                ·
                  refine ⟨6304963687461305462063845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8406618249948407282751793 6304963687461305462063845)
                  ·
                    refine ⟨1182180691398994774136971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6304963687461305462063845 1182180691398994774136971)
                    ·
                      rfl

theorem cell22_3453433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_3453433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453433 prefixEnd_3453433 := by exact prefixLift 3453433
  have htrace : WordTrace (prefixWord ++ tailWord_3453433) baseStart_3453433 baseEnd_3453433 := by
    simpa [prefixWord, tailWord_3453433, baseEnd_3453433] using wordTrace_append hprefix tailTrace_3453433
  have hstable : (prefixWord ++ tailWord_3453433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453433).length < 2 ^ (prefixWord ++ tailWord_3453433).sum := by decide
  have hdescent : baseEnd_3453433 < baseStart_3453433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453493 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 7]
def baseStart_3453493 : Nat := 118140960795 + 3453493 * 2 ^ 59
def prefixEnd_3453493 : Nat := 4983230072969 + 3 ^ 40 * 3453493 * 2
def baseEnd_3453493 : Nat := 394067076875058205878929

theorem tailTrace_3453493 : CollatzResearch.WordTrace tailWord_3453493 prefixEnd_3453493 394067076875058205878929 := by
  unfold tailWord_3453493
  simp only [CollatzResearch.WordTrace]
  refine ⟨125959237677592145492365133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83972825118394763661576755 125959237677592145492365133)
  ·
    refine ⟨47234714129097054559636925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125959237677592145492365133 47234714129097054559636925)
    ·
      refine ⟨17713017798411395459863847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47234714129097054559636925 17713017798411395459863847)
      ·
        refine ⟨26569526697617093189795771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17713017798411395459863847 26569526697617093189795771)
        ·
          refine ⟨39854290046425639784693657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26569526697617093189795771 39854290046425639784693657)
          ·
            refine ⟨29890717534819229838520243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39854290046425639784693657 29890717534819229838520243)
            ·
              refine ⟨44836076302228844757780365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29890717534819229838520243 44836076302228844757780365)
              ·
                refine ⟨16813528613335816784167637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44836076302228844757780365 16813528613335816784167637)
                ·
                  refine ⟨394067076875058205878929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16813528613335816784167637 394067076875058205878929)
                  ·
                    rfl

theorem cell22_3453493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_3453493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453493 prefixEnd_3453493 := by exact prefixLift 3453493
  have htrace : WordTrace (prefixWord ++ tailWord_3453493) baseStart_3453493 baseEnd_3453493 := by
    simpa [prefixWord, tailWord_3453493, baseEnd_3453493] using wordTrace_append hprefix tailTrace_3453493
  have hstable : (prefixWord ++ tailWord_3453493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453493).length < 2 ^ (prefixWord ++ tailWord_3453493).sum := by decide
  have hdescent : baseEnd_3453493 < baseStart_3453493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453600 : List Nat := [2, 1, 1, 4, 4, 1, 9]
def baseStart_3453600 : Nat := 118140960795 + 3453600 * 2 ^ 59
def prefixEnd_3453600 : Nat := 4983230072969 + 3 ^ 40 * 3453600 * 2
def baseEnd_3453600 : Nat := 43786587367106000193017

theorem tailTrace_3453600 : CollatzResearch.WordTrace tailWord_3453600 prefixEnd_3453600 43786587367106000193017 := by
  unfold tailWord_3453600
  simp only [CollatzResearch.WordTrace]
  refine ⟨62981570144102251383255127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83975426858803001844340169 62981570144102251383255127)
  ·
    refine ⟨94472355216153377074882691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62981570144102251383255127 94472355216153377074882691)
    ·
      refine ⟨141708532824230065612324037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94472355216153377074882691 141708532824230065612324037)
      ·
        refine ⟨26570349904543137302310757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141708532824230065612324037 26570349904543137302310757)
        ·
          refine ⟨4981940607101838244183267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26570349904543137302310757 4981940607101838244183267)
          ·
            refine ⟨7472910910652757366274901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981940607101838244183267 7472910910652757366274901)
            ·
              refine ⟨43786587367106000193017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7472910910652757366274901 43786587367106000193017)
              ·
                rfl

theorem cell22_3453600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 9].length) (baseStart_3453600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453600 prefixEnd_3453600 := by exact prefixLift 3453600
  have htrace : WordTrace (prefixWord ++ tailWord_3453600) baseStart_3453600 baseEnd_3453600 := by
    simpa [prefixWord, tailWord_3453600, baseEnd_3453600] using wordTrace_append hprefix tailTrace_3453600
  have hstable : (prefixWord ++ tailWord_3453600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453600).length < 2 ^ (prefixWord ++ tailWord_3453600).sum := by decide
  have hdescent : baseEnd_3453600 < baseStart_3453600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453621 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3453621 : Nat := 118140960795 + 3453621 * 2 ^ 59
def prefixEnd_3453621 : Nat := 4983230072969 + 3 ^ 40 * 3453621 * 2
def baseEnd_3453621 : Nat := 1182245047641024950436395

theorem tailTrace_3453621 : CollatzResearch.WordTrace tailWord_3453621 prefixEnd_3453621 1182245047641024950436395 := by
  unfold tailWord_3453621
  simp only [CollatzResearch.WordTrace]
  refine ⟨125963906221128423353024717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83975937480752282235349811 125963906221128423353024717)
  ·
    refine ⟨47236464832923158757384269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125963906221128423353024717 47236464832923158757384269)
    ·
      refine ⟨17713674312346184534019101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47236464832923158757384269 17713674312346184534019101)
      ·
        refine ⟨6642627867129819200257163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17713674312346184534019101 6642627867129819200257163)
        ·
          refine ⟨9963941800694728800385745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6642627867129819200257163 9963941800694728800385745)
          ·
            refine ⟨7472956350521046600289309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9963941800694728800385745 7472956350521046600289309)
            ·
              refine ⟨2802358631445392475108491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7472956350521046600289309 2802358631445392475108491)
              ·
                refine ⟨4203537947168088712662737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802358631445392475108491 4203537947168088712662737)
                ·
                  refine ⟨3152653460376066534497053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4203537947168088712662737 3152653460376066534497053)
                  ·
                    refine ⟨1182245047641024950436395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152653460376066534497053 1182245047641024950436395)
                    ·
                      rfl

theorem cell22_3453621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3453621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453621 prefixEnd_3453621 := by exact prefixLift 3453621
  have htrace : WordTrace (prefixWord ++ tailWord_3453621) baseStart_3453621 baseEnd_3453621 := by
    simpa [prefixWord, tailWord_3453621, baseEnd_3453621] using wordTrace_append hprefix tailTrace_3453621
  have hstable : (prefixWord ++ tailWord_3453621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453621).length < 2 ^ (prefixWord ++ tailWord_3453621).sum := by decide
  have hdescent : baseEnd_3453621 < baseStart_3453621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453632 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 3, 3]
def baseStart_3453632 : Nat := 118140960795 + 3453632 * 2 ^ 59
def prefixEnd_3453632 : Nat := 4983230072969 + 3 ^ 40 * 3453632 * 2
def baseEnd_3453632 : Nat := 1182248813165824588411361

theorem tailTrace_3453632 : CollatzResearch.WordTrace tailWord_3453632 prefixEnd_3453632 1182248813165824588411361 := by
  unfold tailWord_3453632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62982153712044286115837575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83976204949392381487783433 62982153712044286115837575)
  ·
    refine ⟨94473230568066429173756363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62982153712044286115837575 94473230568066429173756363)
    ·
      refine ⟨141709845852099643760634545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94473230568066429173756363 141709845852099643760634545)
      ·
        refine ⟨106282384389074732820475909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141709845852099643760634545 106282384389074732820475909)
        ·
          refine ⟨19927947072951512403839233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106282384389074732820475909 19927947072951512403839233)
          ·
            refine ⟨14945960304713634302879425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19927947072951512403839233 14945960304713634302879425)
            ·
              refine ⟨11209470228535225727159569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14945960304713634302879425 11209470228535225727159569)
              ·
                refine ⟨8407102671401419295369677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11209470228535225727159569 8407102671401419295369677)
                ·
                  refine ⟨3152663501775532235763629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8407102671401419295369677 3152663501775532235763629)
                  ·
                    refine ⟨1182248813165824588411361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152663501775532235763629 1182248813165824588411361)
                    ·
                      rfl

theorem cell22_3453632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_3453632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453632 prefixEnd_3453632 := by exact prefixLift 3453632
  have htrace : WordTrace (prefixWord ++ tailWord_3453632) baseStart_3453632 baseEnd_3453632 := by
    simpa [prefixWord, tailWord_3453632, baseEnd_3453632] using wordTrace_append hprefix tailTrace_3453632
  have hstable : (prefixWord ++ tailWord_3453632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453632).length < 2 ^ (prefixWord ++ tailWord_3453632).sum := by decide
  have hdescent : baseEnd_3453632 < baseStart_3453632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453675 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 3, 4]
def baseStart_3453675 : Nat := 118140960795 + 3453675 * 2 ^ 59
def prefixEnd_3453675 : Nat := 4983230072969 + 3 ^ 40 * 3453675 * 2
def baseEnd_3453675 : Nat := 1182263532944586809586229

theorem tailTrace_3453675 : CollatzResearch.WordTrace tailWord_3453675 prefixEnd_3453675 1182263532944586809586229 := by
  unfold tailWord_3453675
  simp only [CollatzResearch.WordTrace]
  refine ⟨125965875762932790575490479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83977250508621860383660319 125965875762932790575490479)
  ·
    refine ⟨188948813644399185863235719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125965875762932790575490479 188948813644399185863235719)
    ·
      refine ⟨283423220466598778794853579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188948813644399185863235719 283423220466598778794853579)
      ·
        refine ⟨425134830699898168192280369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283423220466598778794853579 425134830699898168192280369)
        ·
          refine ⟨318851123024923626144210277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425134830699898168192280369 318851123024923626144210277)
          ·
            refine ⟨59784585567173179902039427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318851123024923626144210277 59784585567173179902039427)
            ·
              refine ⟨89676878350759769853059141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59784585567173179902039427 89676878350759769853059141)
              ·
                refine ⟨16814414690767456847448589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89676878350759769853059141 16814414690767456847448589)
                ·
                  refine ⟨6305405509037796317793221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16814414690767456847448589 6305405509037796317793221)
                  ·
                    refine ⟨1182263532944586809586229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6305405509037796317793221 1182263532944586809586229)
                    ·
                      rfl

theorem cell22_3453675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_3453675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453675 prefixEnd_3453675 := by exact prefixLift 3453675
  have htrace : WordTrace (prefixWord ++ tailWord_3453675) baseStart_3453675 baseEnd_3453675 := by
    simpa [prefixWord, tailWord_3453675, baseEnd_3453675] using wordTrace_append hprefix tailTrace_3453675
  have hstable : (prefixWord ++ tailWord_3453675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453675).length < 2 ^ (prefixWord ++ tailWord_3453675).sum := by decide
  have hdescent : baseEnd_3453675 < baseStart_3453675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453679 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 5]
def baseStart_3453679 : Nat := 118140960795 + 3453679 * 2 ^ 59
def prefixEnd_3453679 : Nat := 4983230072969 + 3 ^ 40 * 3453679 * 2
def baseEnd_3453679 : Nat := 394088300742110710828739

theorem tailTrace_3453679 : CollatzResearch.WordTrace tailWord_3453679 prefixEnd_3453679 394088300742110710828739 := by
  unfold tailWord_3453679
  simp only [CollatzResearch.WordTrace]
  refine ⟨125966021654918299258636091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83977347769945532839090727 125966021654918299258636091)
  ·
    refine ⟨188949032482377448887954137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125966021654918299258636091 188949032482377448887954137)
    ·
      refine ⟨141711774361783086665965603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188949032482377448887954137 141711774361783086665965603)
      ·
        refine ⟨212567661542674629998948405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141711774361783086665965603 212567661542674629998948405)
        ·
          refine ⟨19928218269625746562401413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212567661542674629998948405 19928218269625746562401413)
          ·
            refine ⟨3736540925554827480450265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19928218269625746562401413 3736540925554827480450265)
            ·
              refine ⟨2802405694166120610337699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3736540925554827480450265 2802405694166120610337699)
              ·
                refine ⟨4203608541249180915506549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802405694166120610337699 4203608541249180915506549)
                ·
                  refine ⟨394088300742110710828739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4203608541249180915506549 394088300742110710828739)
                  ·
                    rfl

theorem cell22_3453679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 5].length) (baseStart_3453679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453679 prefixEnd_3453679 := by exact prefixLift 3453679
  have htrace : WordTrace (prefixWord ++ tailWord_3453679) baseStart_3453679 baseEnd_3453679 := by
    simpa [prefixWord, tailWord_3453679, baseEnd_3453679] using wordTrace_append hprefix tailTrace_3453679
  have hstable : (prefixWord ++ tailWord_3453679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453679).length < 2 ^ (prefixWord ++ tailWord_3453679).sum := by decide
  have hdescent : baseEnd_3453679 < baseStart_3453679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453690 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_3453690 : Nat := 118140960795 + 3453690 * 2 ^ 59
def prefixEnd_3453690 : Nat := 4983230072969 + 3 ^ 40 * 3453690 * 2
def baseEnd_3453690 : Nat := 394089555917043923487061

theorem tailTrace_3453690 : CollatzResearch.WordTrace tailWord_3453690 prefixEnd_3453690 394089555917043923487061 := by
  unfold tailWord_3453690
  simp only [CollatzResearch.WordTrace]
  refine ⟨31491605714469612034321631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83977615238585632091524349 31491605714469612034321631)
  ·
    refine ⟨47237408571704418051482447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31491605714469612034321631 47237408571704418051482447)
    ·
      refine ⟨70856112857556627077223671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47237408571704418051482447 70856112857556627077223671)
      ·
        refine ⟨106284169286334940615835507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70856112857556627077223671 106284169286334940615835507)
        ·
          refine ⟨159426253929502410923753261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106284169286334940615835507 159426253929502410923753261)
          ·
            refine ⟨59784845223563404096407473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159426253929502410923753261 59784845223563404096407473)
            ·
              refine ⟨44838633917672553072305605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59784845223563404096407473 44838633917672553072305605)
              ·
                refine ⟨8407243859563603701057301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44838633917672553072305605 8407243859563603701057301)
                ·
                  refine ⟨394089555917043923487061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8407243859563603701057301 394089555917043923487061)
                  ·
                    rfl

theorem cell22_3453690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_3453690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453690 prefixEnd_3453690 := by exact prefixLift 3453690
  have htrace : WordTrace (prefixWord ++ tailWord_3453690) baseStart_3453690 baseEnd_3453690 := by
    simpa [prefixWord, tailWord_3453690, baseEnd_3453690] using wordTrace_append hprefix tailTrace_3453690
  have hstable : (prefixWord ++ tailWord_3453690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453690).length < 2 ^ (prefixWord ++ tailWord_3453690).sum := by decide
  have hdescent : baseEnd_3453690 < baseStart_3453690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453692 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_3453692 : Nat := 118140960795 + 3453692 * 2 ^ 59
def prefixEnd_3453692 : Nat := 4983230072969 + 3 ^ 40 * 3453692 * 2
def baseEnd_3453692 : Nat := 1182269352392004431911177

theorem tailTrace_3453692 : CollatzResearch.WordTrace tailWord_3453692 prefixEnd_3453692 1182269352392004431911177 := by
  unfold tailWord_3453692
  simp only [CollatzResearch.WordTrace]
  refine ⟨62983247901935601239429665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83977663869247468319239553 62983247901935601239429665)
  ·
    refine ⟨47237435926451700929572249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62983247901935601239429665 47237435926451700929572249)
    ·
      refine ⟨35428076944838775697179187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47237435926451700929572249 35428076944838775697179187)
      ·
        refine ⟨53142115417258163545768781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35428076944838775697179187 53142115417258163545768781)
        ·
          refine ⟨19928293281471811329663293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53142115417258163545768781 19928293281471811329663293)
          ·
            refine ⟨7473109980551929248623735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19928293281471811329663293 7473109980551929248623735)
            ·
              refine ⟨11209664970827893872935603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473109980551929248623735 11209664970827893872935603)
              ·
                refine ⟨16814497456241840809403405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11209664970827893872935603 16814497456241840809403405)
                ·
                  refine ⟨6305436546090690303526277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16814497456241840809403405 6305436546090690303526277)
                  ·
                    refine ⟨1182269352392004431911177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6305436546090690303526277 1182269352392004431911177)
                    ·
                      rfl

theorem cell22_3453692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_3453692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453692 prefixEnd_3453692 := by exact prefixLift 3453692
  have htrace : WordTrace (prefixWord ++ tailWord_3453692) baseStart_3453692 baseEnd_3453692 := by
    simpa [prefixWord, tailWord_3453692, baseEnd_3453692] using wordTrace_append hprefix tailTrace_3453692
  have hstable : (prefixWord ++ tailWord_3453692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453692).length < 2 ^ (prefixWord ++ tailWord_3453692).sum := by decide
  have hdescent : baseEnd_3453692 < baseStart_3453692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453705 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_3453705 : Nat := 118140960795 + 3453705 * 2 ^ 59
def prefixEnd_3453705 : Nat := 4983230072969 + 3 ^ 40 * 3453705 * 2
def baseEnd_3453705 : Nat := 1182273802557676731336137

theorem tailTrace_3453705 : CollatzResearch.WordTrace tailWord_3453705 prefixEnd_3453705 1182273802557676731336137 := by
  unfold tailWord_3453705
  simp only [CollatzResearch.WordTrace]
  refine ⟨125966969952824105699082569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83977979968549403799388379 125966969952824105699082569)
  ·
    refine ⟨94475227464618079274311927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125966969952824105699082569 94475227464618079274311927)
    ·
      refine ⟨141712841196927118911467891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94475227464618079274311927 141712841196927118911467891)
      ·
        refine ⟨212569261795390678367201837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141712841196927118911467891 212569261795390678367201837)
        ·
          refine ⟨79713473173271504387700689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212569261795390678367201837 79713473173271504387700689)
          ·
            refine ⟨59785104879953628290775517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79713473173271504387700689 59785104879953628290775517)
            ·
              refine ⟨22419414329982610609040819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59785104879953628290775517 22419414329982610609040819)
              ·
                refine ⟨33629121494973915913561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22419414329982610609040819 33629121494973915913561229)
                ·
                  refine ⟨12610920560615218467585461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33629121494973915913561229 12610920560615218467585461)
                  ·
                    refine ⟨1182273802557676731336137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12610920560615218467585461 1182273802557676731336137)
                    ·
                      rfl

theorem cell22_3453705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_3453705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453705 prefixEnd_3453705 := by exact prefixLift 3453705
  have htrace : WordTrace (prefixWord ++ tailWord_3453705) baseStart_3453705 baseEnd_3453705 := by
    simpa [prefixWord, tailWord_3453705, baseEnd_3453705] using wordTrace_append hprefix tailTrace_3453705
  have hstable : (prefixWord ++ tailWord_3453705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453705).length < 2 ^ (prefixWord ++ tailWord_3453705).sum := by decide
  have hdescent : baseEnd_3453705 < baseStart_3453705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453707 : List Nat := [1, 1, 1, 1, 5, 1, 1, 7, 4]
def baseStart_3453707 : Nat := 118140960795 + 3453707 * 2 ^ 59
def prefixEnd_3453707 : Nat := 4983230072969 + 3 ^ 40 * 3453707 * 2
def baseEnd_3453707 : Nat := 394091495732849797595377

theorem tailTrace_3453707 : CollatzResearch.WordTrace tailWord_3453707 prefixEnd_3453707 394091495732849797595377 := by
  unfold tailWord_3453707
  simp only [CollatzResearch.WordTrace]
  refine ⟨125967042898816860040655375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83978028599211240027103583 125967042898816860040655375)
  ·
    refine ⟨188950564348225290060983063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125967042898816860040655375 188950564348225290060983063)
    ·
      refine ⟨283425846522337935091474595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188950564348225290060983063 283425846522337935091474595)
      ·
        refine ⟨425138769783506902637211893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283425846522337935091474595 425138769783506902637211893)
        ·
          refine ⟨39856759667203772122238615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 425138769783506902637211893 39856759667203772122238615)
          ·
            refine ⟨59785139500805658183357923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39856759667203772122238615 59785139500805658183357923)
            ·
              refine ⟨89677709251208487275036885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59785139500805658183357923 89677709251208487275036885)
              ·
                refine ⟨2101821310575198920508677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89677709251208487275036885 2101821310575198920508677)
                ·
                  refine ⟨394091495732849797595377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101821310575198920508677 394091495732849797595377)
                  ·
                    rfl

theorem cell22_3453707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 4].length) (baseStart_3453707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453707 prefixEnd_3453707 := by exact prefixLift 3453707
  have htrace : WordTrace (prefixWord ++ tailWord_3453707) baseStart_3453707 baseEnd_3453707 := by
    simpa [prefixWord, tailWord_3453707, baseEnd_3453707] using wordTrace_append hprefix tailTrace_3453707
  have hstable : (prefixWord ++ tailWord_3453707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453707).length < 2 ^ (prefixWord ++ tailWord_3453707).sum := by decide
  have hdescent : baseEnd_3453707 < baseStart_3453707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453720 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_3453720 : Nat := 118140960795 + 3453720 * 2 ^ 59
def prefixEnd_3453720 : Nat := 4983230072969 + 3 ^ 40 * 3453720 * 2
def baseEnd_3453720 : Nat := 1182278937364221692211091

theorem tailTrace_3453720 : CollatzResearch.WordTrace tailWord_3453720 prefixEnd_3453720 1182278937364221692211091 := by
  unfold tailWord_3453720
  simp only [CollatzResearch.WordTrace]
  refine ⟨62983758523884881630439307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83978344698513175507252409 62983758523884881630439307)
  ·
    refine ⟨94475637785827322445658961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62983758523884881630439307 94475637785827322445658961)
    ·
      refine ⟨70856728339370491834244221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94475637785827322445658961 70856728339370491834244221)
      ·
        refine ⟨26571273127263934437841583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70856728339370491834244221 26571273127263934437841583)
        ·
          refine ⟨39856909690895901656762375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26571273127263934437841583 39856909690895901656762375)
          ·
            refine ⟨59785364536343852485143563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39856909690895901656762375 59785364536343852485143563)
            ·
              refine ⟨89678046804515778727715345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59785364536343852485143563 89678046804515778727715345)
              ·
                refine ⟨67258535103386834045786509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89678046804515778727715345 67258535103386834045786509)
                ·
                  refine ⟨25221950663770062767169941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67258535103386834045786509 25221950663770062767169941)
                  ·
                    refine ⟨1182278937364221692211091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25221950663770062767169941 1182278937364221692211091)
                    ·
                      rfl

theorem cell22_3453720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_3453720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453720 prefixEnd_3453720 := by exact prefixLift 3453720
  have htrace : WordTrace (prefixWord ++ tailWord_3453720) baseStart_3453720 baseEnd_3453720 := by
    simpa [prefixWord, tailWord_3453720, baseEnd_3453720] using wordTrace_append hprefix tailTrace_3453720
  have hstable : (prefixWord ++ tailWord_3453720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453720).length < 2 ^ (prefixWord ++ tailWord_3453720).sum := by decide
  have hdescent : baseEnd_3453720 < baseStart_3453720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453724 : List Nat := [2, 2, 3, 1, 1, 4, 1, 4, 4]
def baseStart_3453724 : Nat := 118140960795 + 3453724 * 2 ^ 59
def prefixEnd_3453724 : Nat := 4983230072969 + 3 ^ 40 * 3453724 * 2
def baseEnd_3453724 : Nat := 394093435548655671703693

theorem tailTrace_3453724 : CollatzResearch.WordTrace tailWord_3453724 prefixEnd_3453724 394093435548655671703693 := by
  unfold tailWord_3453724
  simp only [CollatzResearch.WordTrace]
  refine ⟨62983831469877635972012113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83978441959836847962682817 62983831469877635972012113)
  ·
    refine ⟨47237873602408226979009085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62983831469877635972012113 47237873602408226979009085)
    ·
      refine ⟨17714202600903085117128407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47237873602408226979009085 17714202600903085117128407)
      ·
        refine ⟨26571303901354627675692611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17714202600903085117128407 26571303901354627675692611)
        ·
          refine ⟨39856955852031941513538917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26571303901354627675692611 39856955852031941513538917)
          ·
            refine ⟨7473179222255989033788547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39856955852031941513538917 7473179222255989033788547)
            ·
              refine ⟨11209768833383983550682821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473179222255989033788547 11209768833383983550682821)
              ·
                refine ⟨2101831656259496915753029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11209768833383983550682821 2101831656259496915753029)
                ·
                  refine ⟨394093435548655671703693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101831656259496915753029 394093435548655671703693)
                  ·
                    rfl

theorem cell22_3453724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_3453724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453724 prefixEnd_3453724 := by exact prefixLift 3453724
  have htrace : WordTrace (prefixWord ++ tailWord_3453724) baseStart_3453724 baseEnd_3453724 := by
    simpa [prefixWord, tailWord_3453724, baseEnd_3453724] using wordTrace_append hprefix tailTrace_3453724
  have hstable : (prefixWord ++ tailWord_3453724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453724).length < 2 ^ (prefixWord ++ tailWord_3453724).sum := by decide
  have hdescent : baseEnd_3453724 < baseStart_3453724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453741 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3453741 : Nat := 118140960795 + 3453741 * 2 ^ 59
def prefixEnd_3453741 : Nat := 4983230072969 + 3 ^ 40 * 3453741 * 2
def baseEnd_3453741 : Nat := 394095375364461545812009

theorem tailTrace_3453741 : CollatzResearch.WordTrace tailWord_3453741 prefixEnd_3453741 394095375364461545812009 := by
  unfold tailWord_3453741
  simp only [CollatzResearch.WordTrace]
  refine ⟨125968282980693683847393077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83978855320462455898262051 125968282980693683847393077)
  ·
    refine ⟨11809526529440032860693101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125968282980693683847393077 11809526529440032860693101)
    ·
      refine ⟨4428572448540012322759913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11809526529440032860693101 4428572448540012322759913)
      ·
        refine ⟨3321429336405009242069935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4428572448540012322759913 3321429336405009242069935)
        ·
          refine ⟨4982144004607513863104903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321429336405009242069935 4982144004607513863104903)
          ·
            refine ⟨7473216006911270794657355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982144004607513863104903 7473216006911270794657355)
            ·
              refine ⟨11209824010366906191986033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473216006911270794657355 11209824010366906191986033)
              ·
                refine ⟨8407368007775179643989525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11209824010366906191986033 8407368007775179643989525)
                ·
                  refine ⟨394095375364461545812009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8407368007775179643989525 394095375364461545812009)
                  ·
                    rfl

theorem cell22_3453741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3453741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453741 prefixEnd_3453741 := by exact prefixLift 3453741
  have htrace : WordTrace (prefixWord ++ tailWord_3453741) baseStart_3453741 baseEnd_3453741 := by
    simpa [prefixWord, tailWord_3453741, baseEnd_3453741] using wordTrace_append hprefix tailTrace_3453741
  have hstable : (prefixWord ++ tailWord_3453741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453741).length < 2 ^ (prefixWord ++ tailWord_3453741).sum := by decide
  have hdescent : baseEnd_3453741 < baseStart_3453741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453752 : List Nat := [2, 1, 2, 1, 3, 2, 5, 6]
def baseStart_3453752 : Nat := 118140960795 + 3453752 * 2 ^ 59
def prefixEnd_3453752 : Nat := 4983230072969 + 3 ^ 40 * 3453752 * 2
def baseEnd_3453752 : Nat := 131365543513131586156777

theorem tailTrace_3453752 : CollatzResearch.WordTrace tailWord_3453752 prefixEnd_3453752 131365543513131586156777 := by
  unfold tailWord_3453752
  simp only [CollatzResearch.WordTrace]
  refine ⟨62984342091826916363021755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83979122789102555150695673 62984342091826916363021755)
  ·
    refine ⟨94476513137740374544532633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62984342091826916363021755 94476513137740374544532633)
    ·
      refine ⟨70857384853305280908399475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94476513137740374544532633 70857384853305280908399475)
      ·
        refine ⟨106286077279957921362599213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70857384853305280908399475 106286077279957921362599213)
        ·
          refine ⟨39857278979984220510974705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106286077279957921362599213 39857278979984220510974705)
          ·
            refine ⟨29892959234988165383231029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39857278979984220510974705 29892959234988165383231029)
            ·
              refine ⟨2802464928280140504677909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29892959234988165383231029 2802464928280140504677909)
              ·
                refine ⟨131365543513131586156777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2802464928280140504677909 131365543513131586156777)
                ·
                  rfl

theorem cell22_3453752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 6].length) (baseStart_3453752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453752 prefixEnd_3453752 := by exact prefixLift 3453752
  have htrace : WordTrace (prefixWord ++ tailWord_3453752) baseStart_3453752 baseEnd_3453752 := by
    simpa [prefixWord, tailWord_3453752, baseEnd_3453752] using wordTrace_append hprefix tailTrace_3453752
  have hstable : (prefixWord ++ tailWord_3453752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453752).length < 2 ^ (prefixWord ++ tailWord_3453752).sum := by decide
  have hdescent : baseEnd_3453752 < baseStart_3453752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453765 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3453765 : Nat := 118140960795 + 3453765 * 2 ^ 59
def prefixEnd_3453765 : Nat := 4983230072969 + 3 ^ 40 * 3453765 * 2
def baseEnd_3453765 : Nat := 1182294341783856574835953

theorem tailTrace_3453765 : CollatzResearch.WordTrace tailWord_3453765 prefixEnd_3453765 1182294341783856574835953 := by
  unfold tailWord_3453765
  simp only [CollatzResearch.WordTrace]
  refine ⟨125969158332606735946266749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83979438888404490630844499 125969158332606735946266749)
  ·
    refine ⟨47238434374727525979850031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125969158332606735946266749 47238434374727525979850031)
    ·
      refine ⟨70857651562091288969775047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47238434374727525979850031 70857651562091288969775047)
      ·
        refine ⟨106286477343136933454662571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70857651562091288969775047 106286477343136933454662571)
        ·
          refine ⟨159429716014705400181993857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106286477343136933454662571 159429716014705400181993857)
          ·
            refine ⟨119572287011029050136495393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159429716014705400181993857 119572287011029050136495393)
            ·
              refine ⟨89679215258271787602371545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119572287011029050136495393 89679215258271787602371545)
              ·
                refine ⟨67259411443703840701778659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89679215258271787602371545 67259411443703840701778659)
                ·
                  refine ⟨100889117165555761052667989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67259411443703840701778659 100889117165555761052667989)
                  ·
                    refine ⟨1182294341783856574835953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100889117165555761052667989 1182294341783856574835953)
                    ·
                      rfl

theorem cell22_3453765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3453765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453765 prefixEnd_3453765 := by exact prefixLift 3453765
  have htrace : WordTrace (prefixWord ++ tailWord_3453765) baseStart_3453765 baseEnd_3453765 := by
    simpa [prefixWord, tailWord_3453765, baseEnd_3453765] using wordTrace_append hprefix tailTrace_3453765
  have hstable : (prefixWord ++ tailWord_3453765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453765).length < 2 ^ (prefixWord ++ tailWord_3453765).sum := by decide
  have hdescent : baseEnd_3453765 < baseStart_3453765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453767 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 7, 3]
def baseStart_3453767 : Nat := 118140960795 + 3453767 * 2 ^ 59
def prefixEnd_3453767 : Nat := 4983230072969 + 3 ^ 40 * 3453767 * 2
def baseEnd_3453767 : Nat := 1182295026424729236285947

theorem tailTrace_3453767 : CollatzResearch.WordTrace tailWord_3453767 prefixEnd_3453767 1182295026424729236285947 := by
  unfold tailWord_3453767
  simp only [CollatzResearch.WordTrace]
  refine ⟨125969231278599490287839555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83979487519066326858559703 125969231278599490287839555)
  ·
    refine ⟨188953846917899235431759333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125969231278599490287839555 188953846917899235431759333)
    ·
      refine ⟨35428846297106106643454875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188953846917899235431759333 35428846297106106643454875)
      ·
        refine ⟨53143269445659159965182313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35428846297106106643454875 53143269445659159965182313)
        ·
          refine ⟨39857452084244369973886735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53143269445659159965182313 39857452084244369973886735)
          ·
            refine ⟨59786178126366554960830103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39857452084244369973886735 59786178126366554960830103)
            ·
              refine ⟨89679267189549832441245155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59786178126366554960830103 89679267189549832441245155)
              ·
                refine ⟨134518900784324748661867733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89679267189549832441245155 134518900784324748661867733)
                ·
                  refine ⟨3152786737132611296762525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 134518900784324748661867733 3152786737132611296762525)
                  ·
                    refine ⟨1182295026424729236285947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152786737132611296762525 1182295026424729236285947)
                    ·
                      rfl

theorem cell22_3453767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_3453767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453767 prefixEnd_3453767 := by exact prefixLift 3453767
  have htrace : WordTrace (prefixWord ++ tailWord_3453767) baseStart_3453767 baseEnd_3453767 := by
    simpa [prefixWord, tailWord_3453767, baseEnd_3453767] using wordTrace_append hprefix tailTrace_3453767
  have hstable : (prefixWord ++ tailWord_3453767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453767).length < 2 ^ (prefixWord ++ tailWord_3453767).sum := by decide
  have hdescent : baseEnd_3453767 < baseStart_3453767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453797 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 5]
def baseStart_3453797 : Nat := 118140960795 + 3453797 * 2 ^ 59
def prefixEnd_3453797 : Nat := 4983230072969 + 3 ^ 40 * 3453797 * 2
def baseEnd_3453797 : Nat := 394101765345939719345285

theorem tailTrace_3453797 : CollatzResearch.WordTrace tailWord_3453797 prefixEnd_3453797 394101765345939719345285 := by
  unfold tailWord_3453797
  simp only [CollatzResearch.WordTrace]
  refine ⟨125970325468490805411431645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83980216978993870274287763 125970325468490805411431645)
  ·
    refine ⟨47238872050684052029286867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125970325468490805411431645 47238872050684052029286867)
    ·
      refine ⟨70858308076026078043930301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47238872050684052029286867 70858308076026078043930301)
      ·
        refine ⟨26571865528509779266473863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70858308076026078043930301 26571865528509779266473863)
        ·
          refine ⟨39857798292764668899710795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26571865528509779266473863 39857798292764668899710795)
          ·
            refine ⟨59786697439147003349566193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39857798292764668899710795 59786697439147003349566193)
            ·
              refine ⟨44840023079360252512174645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59786697439147003349566193 44840023079360252512174645)
              ·
                refine ⟨4203752163690023673016373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44840023079360252512174645 4203752163690023673016373)
                ·
                  refine ⟨394101765345939719345285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4203752163690023673016373 394101765345939719345285)
                  ·
                    rfl

theorem cell22_3453797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_3453797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453797 prefixEnd_3453797 := by exact prefixLift 3453797
  have htrace : WordTrace (prefixWord ++ tailWord_3453797) baseStart_3453797 baseEnd_3453797 := by
    simpa [prefixWord, tailWord_3453797, baseEnd_3453797] using wordTrace_append hprefix tailTrace_3453797
  have hstable : (prefixWord ++ tailWord_3453797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453797).length < 2 ^ (prefixWord ++ tailWord_3453797).sum := by decide
  have hdescent : baseEnd_3453797 < baseStart_3453797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453814 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3453814 : Nat := 118140960795 + 3453814 * 2 ^ 59
def prefixEnd_3453814 : Nat := 4983230072969 + 3 ^ 40 * 3453814 * 2
def baseEnd_3453814 : Nat := 394103705161745593453601

theorem tailTrace_3453814 : CollatzResearch.WordTrace tailWord_3453814 prefixEnd_3453814 394103705161745593453601 := by
  unfold tailWord_3453814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873184094339326082175031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83980630339619478209866997 7873184094339326082175031)
  ·
    refine ⟨11809776141508989123262547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7873184094339326082175031 11809776141508989123262547)
    ·
      refine ⟨17714664212263483684893821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11809776141508989123262547 17714664212263483684893821)
      ·
        refine ⟨6642999079598806381835183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17714664212263483684893821 6642999079598806381835183)
        ·
          refine ⟨9964498619398209572752775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6642999079598806381835183 9964498619398209572752775)
          ·
            refine ⟨14946747929097314359129163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964498619398209572752775 14946747929097314359129163)
            ·
              refine ⟨22420121893645971538693745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14946747929097314359129163 22420121893645971538693745)
              ·
                refine ⟨16815091420234478654020309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22420121893645971538693745 16815091420234478654020309)
                ·
                  refine ⟨394103705161745593453601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16815091420234478654020309 394103705161745593453601)
                  ·
                    rfl

theorem cell22_3453814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3453814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453814 prefixEnd_3453814 := by exact prefixLift 3453814
  have htrace : WordTrace (prefixWord ++ tailWord_3453814) baseStart_3453814 baseEnd_3453814 := by
    simpa [prefixWord, tailWord_3453814, baseEnd_3453814] using wordTrace_append hprefix tailTrace_3453814
  have hstable : (prefixWord ++ tailWord_3453814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453814).length < 2 ^ (prefixWord ++ tailWord_3453814).sum := by decide
  have hdescent : baseEnd_3453814 < baseStart_3453814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453844 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3453844 : Nat := 118140960795 + 3453844 * 2 ^ 59
def prefixEnd_3453844 : Nat := 4983230072969 + 3 ^ 40 * 3453844 * 2
def baseEnd_3453844 : Nat := 1182321385098326702110711

theorem tailTrace_3453844 : CollatzResearch.WordTrace tailWord_3453844 prefixEnd_3453844 1182321385098326702110711 := by
  unfold tailWord_3453844
  simp only [CollatzResearch.WordTrace]
  refine ⟨62986019849660266219196293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83981359799547021625595057 62986019849660266219196293)
  ·
    refine ⟨11809878721811299916099305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62986019849660266219196293 11809878721811299916099305)
    ·
      refine ⟨8857409041358474937074479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11809878721811299916099305 8857409041358474937074479)
      ·
        refine ⟨13286113562037712405611719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857409041358474937074479 13286113562037712405611719)
        ·
          refine ⟨19929170343056568608417579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13286113562037712405611719 19929170343056568608417579)
          ·
            refine ⟨29893755514584852912626369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19929170343056568608417579 29893755514584852912626369)
            ·
              refine ⟨22420316635938639684469777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29893755514584852912626369 22420316635938639684469777)
              ·
                refine ⟨16815237476953979763352333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22420316635938639684469777 16815237476953979763352333)
                ·
                  refine ⟨6305714053857742411257125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16815237476953979763352333 6305714053857742411257125)
                  ·
                    refine ⟨1182321385098326702110711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6305714053857742411257125 1182321385098326702110711)
                    ·
                      rfl

theorem cell22_3453844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3453844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453844 prefixEnd_3453844 := by exact prefixLift 3453844
  have htrace : WordTrace (prefixWord ++ tailWord_3453844) baseStart_3453844 baseEnd_3453844 := by
    simpa [prefixWord, tailWord_3453844, baseEnd_3453844] using wordTrace_append hprefix tailTrace_3453844
  have hstable : (prefixWord ++ tailWord_3453844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453844).length < 2 ^ (prefixWord ++ tailWord_3453844).sum := by decide
  have hdescent : baseEnd_3453844 < baseStart_3453844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453953 : List Nat := [1, 2, 4, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3453953 : Nat := 118140960795 + 3453953 * 2 ^ 59
def prefixEnd_3453953 : Nat := 4983230072969 + 3 ^ 40 * 3453953 * 2
def baseEnd_3453953 : Nat := 1182358698025886751135377

theorem tailTrace_3453953 : CollatzResearch.WordTrace tailWord_3453953 prefixEnd_3453953 1182358698025886751135377 := by
  unfold tailWord_3453953
  simp only [CollatzResearch.WordTrace]
  refine ⟨125976015255925644054110513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83984010170617096036073675 125976015255925644054110513)
  ·
    refine ⟨94482011441944233040582885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125976015255925644054110513 94482011441944233040582885)
    ·
      refine ⟨17715377145364543695109291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94482011441944233040582885 17715377145364543695109291)
      ·
        refine ⟨26573065718046815542663937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17715377145364543695109291 26573065718046815542663937)
        ·
          refine ⟨19929799288535111656997953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26573065718046815542663937 19929799288535111656997953)
          ·
            refine ⟨14947349466401333742748465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19929799288535111656997953 14947349466401333742748465)
            ·
              refine ⟨11210512099801000307061349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14947349466401333742748465 11210512099801000307061349)
              ·
                refine ⟨2101971018712687557574003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11210512099801000307061349 2101971018712687557574003)
                ·
                  refine ⟨3152956528069031336361005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101971018712687557574003 3152956528069031336361005)
                  ·
                    refine ⟨1182358698025886751135377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152956528069031336361005 1182358698025886751135377)
                    ·
                      rfl

theorem cell22_3453953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3453953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453953 prefixEnd_3453953 := by exact prefixLift 3453953
  have htrace : WordTrace (prefixWord ++ tailWord_3453953) baseStart_3453953 baseEnd_3453953 := by
    simpa [prefixWord, tailWord_3453953, baseEnd_3453953] using wordTrace_append hprefix tailTrace_3453953
  have hstable : (prefixWord ++ tailWord_3453953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453953).length < 2 ^ (prefixWord ++ tailWord_3453953).sum := by decide
  have hdescent : baseEnd_3453953 < baseStart_3453953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453964 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_3453964 : Nat := 118140960795 + 3453964 * 2 ^ 59
def prefixEnd_3453964 : Nat := 4983230072969 + 3 ^ 40 * 3453964 * 2
def baseEnd_3453964 : Nat := 1182362463550686389110343

theorem tailTrace_3453964 : CollatzResearch.WordTrace tailWord_3453964 prefixEnd_3453964 1182362463550686389110343 := by
  unfold tailWord_3453964
  simp only [CollatzResearch.WordTrace]
  refine ⟨62988208229442896466380473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83984277639257195288507297 62988208229442896466380473)
  ·
    refine ⟨47241156172082172349785355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62988208229442896466380473 47241156172082172349785355)
    ·
      refine ⟨70861734258123258524678033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47241156172082172349785355 70861734258123258524678033)
      ·
        refine ⟨53146300693592443893508525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70861734258123258524678033 53146300693592443893508525)
        ·
          refine ⟨19929862760097166460065697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53146300693592443893508525 19929862760097166460065697)
          ·
            refine ⟨14947397070072874845049273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19929862760097166460065697 14947397070072874845049273)
            ·
              refine ⟨11210547802554656133786955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14947397070072874845049273 11210547802554656133786955)
              ·
                refine ⟨16815821703831984200680433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11210547802554656133786955 16815821703831984200680433)
                ·
                  refine ⟨12611866277873988150510325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16815821703831984200680433 12611866277873988150510325)
                  ·
                    refine ⟨1182362463550686389110343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12611866277873988150510325 1182362463550686389110343)
                    ·
                      rfl

theorem cell22_3453964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_3453964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3453964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3453964 prefixEnd_3453964 := by exact prefixLift 3453964
  have htrace : WordTrace (prefixWord ++ tailWord_3453964) baseStart_3453964 baseEnd_3453964 := by
    simpa [prefixWord, tailWord_3453964, baseEnd_3453964] using wordTrace_append hprefix tailTrace_3453964
  have hstable : (prefixWord ++ tailWord_3453964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453964).length < 2 ^ (prefixWord ++ tailWord_3453964).sum := by decide
  have hdescent : baseEnd_3453964 < baseStart_3453964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454024 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_3454024 : Nat := 118140960795 + 3454024 * 2 ^ 59
def prefixEnd_3454024 : Nat := 4983230072969 + 3 ^ 40 * 3454024 * 2
def baseEnd_3454024 : Nat := 1182383002776866232610159

theorem tailTrace_3454024 : CollatzResearch.WordTrace tailWord_3454024 prefixEnd_3454024 1182383002776866232610159 := by
  unfold tailWord_3454024
  simp only [CollatzResearch.WordTrace]
  refine ⟨62989302419334211589972563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83985736559112282119963417 62989302419334211589972563)
  ·
    refine ⟨94483953629001317384958845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62989302419334211589972563 94483953629001317384958845)
    ·
      refine ⟨35431482610875494019359567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94483953629001317384958845 35431482610875494019359567)
      ·
        refine ⟨53147223916313241029039351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35431482610875494019359567 53147223916313241029039351)
        ·
          refine ⟨79720835874469861543559027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53147223916313241029039351 79720835874469861543559027)
          ·
            refine ⟨119581253811704792315338541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79720835874469861543559027 119581253811704792315338541)
            ·
              refine ⟨44842970179389297118251953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119581253811704792315338541 44842970179389297118251953)
              ·
                refine ⟨33632227634541972838688965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44842970179389297118251953 33632227634541972838688965)
                ·
                  refine ⟨6306042681476619907254181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33632227634541972838688965 6306042681476619907254181)
                  ·
                    refine ⟨1182383002776866232610159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6306042681476619907254181 1182383002776866232610159)
                    ·
                      rfl

theorem cell22_3454024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_3454024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454024 prefixEnd_3454024 := by exact prefixLift 3454024
  have htrace : WordTrace (prefixWord ++ tailWord_3454024) baseStart_3454024 baseEnd_3454024 := by
    simpa [prefixWord, tailWord_3454024, baseEnd_3454024] using wordTrace_append hprefix tailTrace_3454024
  have hstable : (prefixWord ++ tailWord_3454024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454024).length < 2 ^ (prefixWord ++ tailWord_3454024).sum := by decide
  have hdescent : baseEnd_3454024 < baseStart_3454024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454056 : List Nat := [2, 1, 4, 4, 1, 10]
def baseStart_3454056 : Nat := 118140960795 + 3454056 * 2 ^ 59
def prefixEnd_3454056 : Nat := 4983230072969 + 3 ^ 40 * 3454056 * 2
def baseEnd_3454056 : Nat := 14597456259639861923581

theorem tailTrace_3454056 : CollatzResearch.WordTrace tailWord_3454056 prefixEnd_3454056 14597456259639861923581 := by
  unfold tailWord_3454056
  simp only [CollatzResearch.WordTrace]
  refine ⟨62989885987276246322555011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83986514649701661763406681 62989885987276246322555011)
  ·
    refine ⟨94484828980914369483832517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62989885987276246322555011 94484828980914369483832517)
    ·
      refine ⟨17715905433921444278218597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94484828980914369483832517 17715905433921444278218597)
      ·
        refine ⟨3321732268860270802165987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17715905433921444278218597 3321732268860270802165987)
        ·
          refine ⟨4982598403290406203248981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321732268860270802165987 4982598403290406203248981)
          ·
            refine ⟨14597456259639861923581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4982598403290406203248981 14597456259639861923581)
            ·
              rfl

theorem cell22_3454056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 10].length) (baseStart_3454056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454056 prefixEnd_3454056 := by exact prefixLift 3454056
  have htrace : WordTrace (prefixWord ++ tailWord_3454056) baseStart_3454056 baseEnd_3454056 := by
    simpa [prefixWord, tailWord_3454056, baseEnd_3454056] using wordTrace_append hprefix tailTrace_3454056
  have hstable : (prefixWord ++ tailWord_3454056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454056).length < 2 ^ (prefixWord ++ tailWord_3454056).sum := by decide
  have hdescent : baseEnd_3454056 < baseStart_3454056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454071 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 3, 3]
def baseStart_3454071 : Nat := 118140960795 + 3454071 * 2 ^ 59
def prefixEnd_3454071 : Nat := 4983230072969 + 3 ^ 40 * 3454071 * 2
def baseEnd_3454071 : Nat := 1182399091837373776685015

theorem tailTrace_3454071 : CollatzResearch.WordTrace tailWord_3454071 prefixEnd_3454071 1182399091837373776685015 := by
  unfold tailWord_3454071
  simp only [CollatzResearch.WordTrace]
  refine ⟨125980319069498150206906067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83986879379665433471270711 125980319069498150206906067)
  ·
    refine ⟨188970478604247225310359101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125980319069498150206906067 188970478604247225310359101)
    ·
      refine ⟨70863929476592709491384663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188970478604247225310359101 70863929476592709491384663)
      ·
        refine ⟨106295894214889064237076995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70863929476592709491384663 106295894214889064237076995)
        ·
          refine ⟨159443841322333596355615493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106295894214889064237076995 159443841322333596355615493)
          ·
            refine ⟨29895720247937549316677905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159443841322333596355615493 29895720247937549316677905)
            ·
              refine ⟨22421790185953161987508429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29895720247937549316677905 22421790185953161987508429)
              ·
                refine ⟨8408171319732435745315661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22421790185953161987508429 8408171319732435745315661)
                ·
                  refine ⟨3153064244899663404493373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8408171319732435745315661 3153064244899663404493373)
                  ·
                    refine ⟨1182399091837373776685015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153064244899663404493373 1182399091837373776685015)
                    ·
                      rfl

theorem cell22_3454071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_3454071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454071 prefixEnd_3454071 := by exact prefixLift 3454071
  have htrace : WordTrace (prefixWord ++ tailWord_3454071) baseStart_3454071 baseEnd_3454071 := by
    simpa [prefixWord, tailWord_3454071, baseEnd_3454071] using wordTrace_append hprefix tailTrace_3454071
  have hstable : (prefixWord ++ tailWord_3454071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454071).length < 2 ^ (prefixWord ++ tailWord_3454071).sum := by decide
  have hdescent : baseEnd_3454071 < baseStart_3454071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454073 : List Nat := [1, 2, 1, 3, 6, 1, 1, 7]
def baseStart_3454073 : Nat := 118140960795 + 3454073 * 2 ^ 59
def prefixEnd_3454073 : Nat := 4983230072969 + 3 ^ 40 * 3454073 * 2
def baseEnd_3454073 : Nat := 131377752942027382015001

theorem tailTrace_3454073 : CollatzResearch.WordTrace tailWord_3454073 prefixEnd_3454073 131377752942027382015001 := by
  unfold tailWord_3454073
  simp only [CollatzResearch.WordTrace]
  refine ⟨125980392015490904548478873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83986928010327269698985915 125980392015490904548478873)
  ·
    refine ⟨94485294011618178411359155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125980392015490904548478873 94485294011618178411359155)
    ·
      refine ⟨141727941017427267617038733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94485294011618178411359155 141727941017427267617038733)
      ·
        refine ⟨53147977881535225356389525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141727941017427267617038733 53147977881535225356389525)
        ·
          refine ⟨2491311463196963688580759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53147977881535225356389525 2491311463196963688580759)
          ·
            refine ⟨3736967194795445532871139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491311463196963688580759 3736967194795445532871139)
            ·
              refine ⟨5605450792193168299306709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736967194795445532871139 5605450792193168299306709)
              ·
                refine ⟨131377752942027382015001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5605450792193168299306709 131377752942027382015001)
                ·
                  rfl

theorem cell22_3454073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 7].length) (baseStart_3454073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454073 prefixEnd_3454073 := by exact prefixLift 3454073
  have htrace : WordTrace (prefixWord ++ tailWord_3454073) baseStart_3454073 baseEnd_3454073 := by
    simpa [prefixWord, tailWord_3454073, baseEnd_3454073] using wordTrace_append hprefix tailTrace_3454073
  have hstable : (prefixWord ++ tailWord_3454073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454073).length < 2 ^ (prefixWord ++ tailWord_3454073).sum := by decide
  have hdescent : baseEnd_3454073 < baseStart_3454073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454116 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_3454116 : Nat := 118140960795 + 3454116 * 2 ^ 59
def prefixEnd_3454116 : Nat := 4983230072969 + 3 ^ 40 * 3454116 * 2
def baseEnd_3454116 : Nat := 1182414496257008659309877

theorem tailTrace_3454116 : CollatzResearch.WordTrace tailWord_3454116 prefixEnd_3454116 1182414496257008659309877 := by
  unfold tailWord_3454116
  simp only [CollatzResearch.WordTrace]
  refine ⟨62990980177167561446147101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83987973569556748594862801 62990980177167561446147101)
  ·
    refine ⟨23621617566437835542305163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62990980177167561446147101 23621617566437835542305163)
    ·
      refine ⟨35432426349656753313457745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23621617566437835542305163 35432426349656753313457745)
      ·
        refine ⟨26574319762242564985093309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35432426349656753313457745 26574319762242564985093309)
        ·
          refine ⟨9965369910840961869409991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26574319762242564985093309 9965369910840961869409991)
          ·
            refine ⟨14948054866261442804114987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9965369910840961869409991 14948054866261442804114987)
            ·
              refine ⟨22422082299392164206172481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14948054866261442804114987 22422082299392164206172481)
              ·
                refine ⟨16816561724544123154629361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22422082299392164206172481 16816561724544123154629361)
                ·
                  refine ⟨12612421293408092365972021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16816561724544123154629361 12612421293408092365972021)
                  ·
                    refine ⟨1182414496257008659309877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12612421293408092365972021 1182414496257008659309877)
                    ·
                      rfl

theorem cell22_3454116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_3454116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454116 prefixEnd_3454116 := by exact prefixLift 3454116
  have htrace : WordTrace (prefixWord ++ tailWord_3454116) baseStart_3454116 baseEnd_3454116 := by
    simpa [prefixWord, tailWord_3454116, baseEnd_3454116] using wordTrace_append hprefix tailTrace_3454116
  have hstable : (prefixWord ++ tailWord_3454116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454116).length < 2 ^ (prefixWord ++ tailWord_3454116).sum := by decide
  have hdescent : baseEnd_3454116 < baseStart_3454116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454122 : List Nat := [3, 1, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3454122 : Nat := 118140960795 + 3454122 * 2 ^ 59
def prefixEnd_3454122 : Nat := 4983230072969 + 3 ^ 40 * 3454122 * 2
def baseEnd_3454122 : Nat := 1182416550179626643659859

theorem tailTrace_3454122 : CollatzResearch.WordTrace tailWord_3454122 prefixEnd_3454122 1182416550179626643659859 := by
  unfold tailWord_3454122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31495544798078346479253155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83988119461542257278008413 31495544798078346479253155)
  ·
    refine ⟨47243317197117519718879733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31495544798078346479253155 47243317197117519718879733)
    ·
      refine ⟨4429060987229767473644975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47243317197117519718879733 4429060987229767473644975)
      ·
        refine ⟨6643591480844651210467463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4429060987229767473644975 6643591480844651210467463)
        ·
          refine ⟨9965387221266976815701195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6643591480844651210467463 9965387221266976815701195)
          ·
            refine ⟨14948080831900465223551793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9965387221266976815701195 14948080831900465223551793)
            ·
              refine ⟨11211060623925348917663845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14948080831900465223551793 11211060623925348917663845)
              ·
                refine ⟨2102073866986002922061971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11211060623925348917663845 2102073866986002922061971)
                ·
                  refine ⟨3153110800479004383092957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102073866986002922061971 3153110800479004383092957)
                  ·
                    refine ⟨1182416550179626643659859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153110800479004383092957 1182416550179626643659859)
                    ·
                      rfl

theorem cell22_3454122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3454122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454122 prefixEnd_3454122 := by exact prefixLift 3454122
  have htrace : WordTrace (prefixWord ++ tailWord_3454122) baseStart_3454122 baseEnd_3454122 := by
    simpa [prefixWord, tailWord_3454122, baseEnd_3454122] using wordTrace_append hprefix tailTrace_3454122
  have hstable : (prefixWord ++ tailWord_3454122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454122).length < 2 ^ (prefixWord ++ tailWord_3454122).sum := by decide
  have hdescent : baseEnd_3454122 < baseStart_3454122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454176 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_3454176 : Nat := 118140960795 + 3454176 * 2 ^ 59
def prefixEnd_3454176 : Nat := 4983230072969 + 3 ^ 40 * 3454176 * 2
def baseEnd_3454176 : Nat := 1182435035483188502809693

theorem tailTrace_3454176 : CollatzResearch.WordTrace tailWord_3454176 prefixEnd_3454176 1182435035483188502809693 := by
  unfold tailWord_3454176
  simp only [CollatzResearch.WordTrace]
  refine ⟨62992074367058876569739191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83989432489411835426318921 62992074367058876569739191)
  ·
    refine ⟨94488111550588314854608787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62992074367058876569739191 94488111550588314854608787)
    ·
      refine ⟨141732167325882472281913181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94488111550588314854608787 141732167325882472281913181)
      ·
        refine ⟨53149562747205927105717443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141732167325882472281913181 53149562747205927105717443)
        ·
          refine ⟨79724344120808890658576165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53149562747205927105717443 79724344120808890658576165)
          ·
            refine ⟨14948314522651666998483031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79724344120808890658576165 14948314522651666998483031)
            ·
              refine ⟨22422471783977500497724547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14948314522651666998483031 22422471783977500497724547)
              ·
                refine ⟨33633707675966250746586821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22422471783977500497724547 33633707675966250746586821)
                ·
                  refine ⟨6306320189243672014985029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33633707675966250746586821 6306320189243672014985029)
                  ·
                    refine ⟨1182435035483188502809693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6306320189243672014985029 1182435035483188502809693)
                    ·
                      rfl

theorem cell22_3454176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_3454176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454176 prefixEnd_3454176 := by exact prefixLift 3454176
  have htrace : WordTrace (prefixWord ++ tailWord_3454176) baseStart_3454176 baseEnd_3454176 := by
    simpa [prefixWord, tailWord_3454176, baseEnd_3454176] using wordTrace_append hprefix tailTrace_3454176
  have hstable : (prefixWord ++ tailWord_3454176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454176).length < 2 ^ (prefixWord ++ tailWord_3454176).sum := by decide
  have hdescent : baseEnd_3454176 < baseStart_3454176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454195 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 2, 3]
def baseStart_3454195 : Nat := 118140960795 + 3454195 * 2 ^ 59
def prefixEnd_3454195 : Nat := 4983230072969 + 3 ^ 40 * 3454195 * 2
def baseEnd_3454195 : Nat := 1182441539571478786584635

theorem tailTrace_3454195 : CollatzResearch.WordTrace tailWord_3454195 prefixEnd_3454195 1182441539571478786584635 := by
  unfold tailWord_3454195
  simp only [CollatzResearch.WordTrace]
  refine ⟨125984841721048919384420039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83989894480699279589613359 125984841721048919384420039)
  ·
    refine ⟨188977262581573379076630059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125984841721048919384420039 188977262581573379076630059)
    ·
      refine ⟨283465893872360068614945089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188977262581573379076630059 283465893872360068614945089)
      ·
        refine ⟨212599420404270051461208817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283465893872360068614945089 212599420404270051461208817)
        ·
          refine ⟨159449565303202538595906613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212599420404270051461208817 159449565303202538595906613)
          ·
            refine ⟨14948396747175237993366245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159449565303202538595906613 14948396747175237993366245)
            ·
              refine ⟨2802824390095357123756171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14948396747175237993366245 2802824390095357123756171)
              ·
                refine ⟨4204236585143035685634257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802824390095357123756171 4204236585143035685634257)
                ·
                  refine ⟨3153177438857276764225693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204236585143035685634257 3153177438857276764225693)
                  ·
                    refine ⟨1182441539571478786584635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153177438857276764225693 1182441539571478786584635)
                    ·
                      rfl

theorem cell22_3454195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 3].length) (baseStart_3454195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454195 prefixEnd_3454195 := by exact prefixLift 3454195
  have htrace : WordTrace (prefixWord ++ tailWord_3454195) baseStart_3454195 baseEnd_3454195 := by
    simpa [prefixWord, tailWord_3454195, baseEnd_3454195] using wordTrace_append hprefix tailTrace_3454195
  have hstable : (prefixWord ++ tailWord_3454195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454195).length < 2 ^ (prefixWord ++ tailWord_3454195).sum := by decide
  have hdescent : baseEnd_3454195 < baseStart_3454195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454236 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 7]
def baseStart_3454236 : Nat := 118140960795 + 3454236 * 2 ^ 59
def prefixEnd_3454236 : Nat := 4983230072969 + 3 ^ 40 * 3454236 * 2
def baseEnd_3454236 : Nat := 394151858236456115436503

theorem tailTrace_3454236 : CollatzResearch.WordTrace tailWord_3454236 prefixEnd_3454236 394151858236456115436503 := by
  unfold tailWord_3454236
  simp only [CollatzResearch.WordTrace]
  refine ⟨62993168556950191693331281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83990891409266922257775041 62993168556950191693331281)
  ·
    refine ⟨47244876417712643769998461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62993168556950191693331281 47244876417712643769998461)
    ·
      refine ⟨17716828656642241413749423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47244876417712643769998461 17716828656642241413749423)
      ·
        refine ⟨26575242984963362120624135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17716828656642241413749423 26575242984963362120624135)
        ·
          refine ⟨39862864477445043180936203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26575242984963362120624135 39862864477445043180936203)
          ·
            refine ⟨59794296716167564771404305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39862864477445043180936203 59794296716167564771404305)
            ·
              refine ⟨44845722537125673578553229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59794296716167564771404305 44845722537125673578553229)
              ·
                refine ⟨16817145951422127591957461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44845722537125673578553229 16817145951422127591957461)
                ·
                  refine ⟨394151858236456115436503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16817145951422127591957461 394151858236456115436503)
                  ·
                    rfl

theorem cell22_3454236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_3454236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454236 prefixEnd_3454236 := by exact prefixLift 3454236
  have htrace : WordTrace (prefixWord ++ tailWord_3454236) baseStart_3454236 baseEnd_3454236 := by
    simpa [prefixWord, tailWord_3454236, baseEnd_3454236] using wordTrace_append hprefix tailTrace_3454236
  have hstable : (prefixWord ++ tailWord_3454236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454236).length < 2 ^ (prefixWord ++ tailWord_3454236).sum := by decide
  have hdescent : baseEnd_3454236 < baseStart_3454236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454343 : List Nat := [1, 1, 4, 2, 2, 4, 8]
def baseStart_3454343 : Nat := 118140960795 + 3454343 * 2 ^ 59
def prefixEnd_3454343 : Nat := 4983230072969 + 3 ^ 40 * 3454343 * 2
def baseEnd_3454343 : Nat := 43796007518372434588303

theorem tailTrace_3454343 : CollatzResearch.WordTrace tailWord_3454343 prefixEnd_3454343 43796007518372434588303 := by
  unfold tailWord_3454343
  simp only [CollatzResearch.WordTrace]
  refine ⟨125990239724512740660807683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83993493149675160440538455 125990239724512740660807683)
  ·
    refine ⟨188985359586769110991211525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125990239724512740660807683 188985359586769110991211525)
    ·
      refine ⟨35434754922519208310852161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188985359586769110991211525 35434754922519208310852161)
      ·
        refine ⟨26576066191889406233139121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35434754922519208310852161 26576066191889406233139121)
        ·
          refine ⟨19932049643917054674854341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26576066191889406233139121 19932049643917054674854341)
          ·
            refine ⟨3737259308234447751535189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19932049643917054674854341 3737259308234447751535189)
            ·
              refine ⟨43796007518372434588303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3737259308234447751535189 43796007518372434588303)
              ·
                rfl

theorem cell22_3454343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 8].length) (baseStart_3454343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454343 prefixEnd_3454343 := by exact prefixLift 3454343
  have htrace : WordTrace (prefixWord ++ tailWord_3454343) baseStart_3454343 baseEnd_3454343 := by
    simpa [prefixWord, tailWord_3454343, baseEnd_3454343] using wordTrace_append hprefix tailTrace_3454343
  have hstable : (prefixWord ++ tailWord_3454343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454343).length < 2 ^ (prefixWord ++ tailWord_3454343).sum := by decide
  have hdescent : baseEnd_3454343 < baseStart_3454343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454345 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_3454345 : Nat := 118140960795 + 3454345 * 2 ^ 59
def prefixEnd_3454345 : Nat := 4983230072969 + 3 ^ 40 * 3454345 * 2
def baseEnd_3454345 : Nat := 1182492887636928395334175

theorem tailTrace_3454345 : CollatzResearch.WordTrace tailWord_3454345 prefixEnd_3454345 1182492887636928395334175 := by
  unfold tailWord_3454345
  simp only [CollatzResearch.WordTrace]
  refine ⟨125990312670505495002380489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83993541780336996668253659 125990312670505495002380489)
  ·
    refine ⟨94492734502879121251785367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125990312670505495002380489 94492734502879121251785367)
    ·
      refine ⟨141739101754318681877678051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94492734502879121251785367 141739101754318681877678051)
      ·
        refine ⟨212608652631478022816517077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141739101754318681877678051 212608652631478022816517077)
        ·
          refine ⟨4983015296050266159762119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 212608652631478022816517077 4983015296050266159762119)
          ·
            refine ⟨7474522944075399239643179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983015296050266159762119 7474522944075399239643179)
            ·
              refine ⟨11211784416113098859464769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7474522944075399239643179 11211784416113098859464769)
              ·
                refine ⟨8408838312084824144598577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11211784416113098859464769 8408838312084824144598577)
                ·
                  refine ⟨6306628734063618108448933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8408838312084824144598577 6306628734063618108448933)
                  ·
                    refine ⟨1182492887636928395334175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6306628734063618108448933 1182492887636928395334175)
                    ·
                      rfl

theorem cell22_3454345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_3454345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454345 prefixEnd_3454345 := by exact prefixLift 3454345
  have htrace : WordTrace (prefixWord ++ tailWord_3454345) baseStart_3454345 baseEnd_3454345 := by
    simpa [prefixWord, tailWord_3454345, baseEnd_3454345] using wordTrace_append hprefix tailTrace_3454345
  have hstable : (prefixWord ++ tailWord_3454345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454345).length < 2 ^ (prefixWord ++ tailWord_3454345).sum := by decide
  have hdescent : baseEnd_3454345 < baseStart_3454345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454360 : List Nat := [2, 1, 2, 5, 2, 1, 2, 7]
def baseStart_3454360 : Nat := 118140960795 + 3454360 * 2 ^ 59
def prefixEnd_3454360 : Nat := 4983230072969 + 3 ^ 40 * 3454360 * 2
def baseEnd_3454360 : Nat := 131388669160385928467681

theorem tailTrace_3454360 : CollatzResearch.WordTrace tailWord_3454360 prefixEnd_3454360 131388669160385928467681 := by
  unfold tailWord_3454360
  simp only [CollatzResearch.WordTrace]
  refine ⟨62995429882725576282088267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83993906510300768376117689 62995429882725576282088267)
  ·
    refine ⟨94493144824088364423132401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62995429882725576282088267 94493144824088364423132401)
    ·
      refine ⟨70869858618066273317349301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94493144824088364423132401 70869858618066273317349301)
      ·
        refine ⟨6644049245443713123501497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70869858618066273317349301 6644049245443713123501497)
        ·
          refine ⟨4983036934082784842626123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6644049245443713123501497 4983036934082784842626123)
          ·
            refine ⟨7474555401124177263939185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983036934082784842626123 7474555401124177263939185)
            ·
              refine ⟨5605916550843132947954389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7474555401124177263939185 5605916550843132947954389)
              ·
                refine ⟨131388669160385928467681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5605916550843132947954389 131388669160385928467681)
                ·
                  rfl

theorem cell22_3454360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_3454360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454360 prefixEnd_3454360 := by exact prefixLift 3454360
  have htrace : WordTrace (prefixWord ++ tailWord_3454360) baseStart_3454360 baseEnd_3454360 := by
    simpa [prefixWord, tailWord_3454360, baseEnd_3454360] using wordTrace_append hprefix tailTrace_3454360
  have hstable : (prefixWord ++ tailWord_3454360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454360).length < 2 ^ (prefixWord ++ tailWord_3454360).sum := by decide
  have hdescent : baseEnd_3454360 < baseStart_3454360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454364 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_3454364 : Nat := 118140960795 + 3454364 * 2 ^ 59
def prefixEnd_3454364 : Nat := 4983230072969 + 3 ^ 40 * 3454364 * 2
def baseEnd_3454364 : Nat := 1182499391725218679109117

theorem tailTrace_3454364 : CollatzResearch.WordTrace tailWord_3454364 prefixEnd_3454364 1182499391725218679109117 := by
  unfold tailWord_3454364
  simp only [CollatzResearch.WordTrace]
  refine ⟨62995502828718330623661073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83994003771624440831548097 62995502828718330623661073)
  ·
    refine ⟨47246627121538747967745805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62995502828718330623661073 47246627121538747967745805)
    ·
      refine ⟨17717485170577030487904677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47246627121538747967745805 17717485170577030487904677)
      ·
        refine ⟨3322028469483193216482127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17717485170577030487904677 3322028469483193216482127)
        ·
          refine ⟨4983042704224789824723191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322028469483193216482127 4983042704224789824723191)
          ·
            refine ⟨7474564056337184737084787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983042704224789824723191 7474564056337184737084787)
            ·
              refine ⟨11211846084505777105627181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7474564056337184737084787 11211846084505777105627181)
              ·
                refine ⟨4204442281689666414610193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11211846084505777105627181 4204442281689666414610193)
                ·
                  refine ⟨3153331711267249810957645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4204442281689666414610193 3153331711267249810957645)
                  ·
                    refine ⟨1182499391725218679109117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153331711267249810957645 1182499391725218679109117)
                    ·
                      rfl

theorem cell22_3454364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_3454364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454364 prefixEnd_3454364 := by exact prefixLift 3454364
  have htrace : WordTrace (prefixWord ++ tailWord_3454364) baseStart_3454364 baseEnd_3454364 := by
    simpa [prefixWord, tailWord_3454364, baseEnd_3454364] using wordTrace_append hprefix tailTrace_3454364
  have hstable : (prefixWord ++ tailWord_3454364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454364).length < 2 ^ (prefixWord ++ tailWord_3454364).sum := by decide
  have hdescent : baseEnd_3454364 < baseStart_3454364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454375 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3454375 : Nat := 118140960795 + 3454375 * 2 ^ 59
def prefixEnd_3454375 : Nat := 4983230072969 + 3 ^ 40 * 3454375 * 2
def baseEnd_3454375 : Nat := 1182503157250018317084083

theorem tailTrace_3454375 : CollatzResearch.WordTrace tailWord_3454375 prefixEnd_3454375 1182503157250018317084083 := by
  unfold tailWord_3454375
  simp only [CollatzResearch.WordTrace]
  refine ⟨125991406860396810125972579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83994271240264540083981719 125991406860396810125972579)
  ·
    refine ⟨188987110290595215188958869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125991406860396810125972579 188987110290595215188958869)
    ·
      refine ⟨8858770794871650711982447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188987110290595215188958869 8858770794871650711982447)
      ·
        refine ⟨13288156192307476067973671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8858770794871650711982447 13288156192307476067973671)
        ·
          refine ⟨19932234288461214101960507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13288156192307476067973671 19932234288461214101960507)
          ·
            refine ⟨29898351432691821152940761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19932234288461214101960507 29898351432691821152940761)
            ·
              refine ⟨22423763574518865864705571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29898351432691821152940761 22423763574518865864705571)
              ·
                refine ⟨33635645361778298797058357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22423763574518865864705571 33635645361778298797058357)
                ·
                  refine ⟨3153341752666715512224221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33635645361778298797058357 3153341752666715512224221)
                  ·
                    refine ⟨1182503157250018317084083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153341752666715512224221 1182503157250018317084083)
                    ·
                      rfl

theorem cell22_3454375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3454375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454375 prefixEnd_3454375 := by exact prefixLift 3454375
  have htrace : WordTrace (prefixWord ++ tailWord_3454375) baseStart_3454375 baseEnd_3454375 := by
    simpa [prefixWord, tailWord_3454375, baseEnd_3454375] using wordTrace_append hprefix tailTrace_3454375
  have hstable : (prefixWord ++ tailWord_3454375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454375).length < 2 ^ (prefixWord ++ tailWord_3454375).sum := by decide
  have hdescent : baseEnd_3454375 < baseStart_3454375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454422 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3454422 : Nat := 118140960795 + 3454422 * 2 ^ 59
def prefixEnd_3454422 : Nat := 4983230072969 + 3 ^ 40 * 3454422 * 2
def baseEnd_3454422 : Nat := 394173082103508620386313

theorem tailTrace_3454422 : CollatzResearch.WordTrace tailWord_3454422 prefixEnd_3454422 394173082103508620386313 := by
  unfold tailWord_3454422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874570068201658572058345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83995414060817691435289013 7874570068201658572058345)
  ·
    refine ⟨5905927551151243929043759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7874570068201658572058345 5905927551151243929043759)
    ·
      refine ⟨8858891326726865893565639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5905927551151243929043759 8858891326726865893565639)
      ·
        refine ⟨13288336990090298840348459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8858891326726865893565639 13288336990090298840348459)
        ·
          refine ⟨19932505485135448260522689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13288336990090298840348459 19932505485135448260522689)
          ·
            refine ⟨14949379113851586195392017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19932505485135448260522689 14949379113851586195392017)
            ·
              refine ⟨11212034335388689646544013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14949379113851586195392017 11212034335388689646544013)
              ·
                refine ⟨4204512875770758617454005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11212034335388689646544013 4204512875770758617454005)
                ·
                  refine ⟨394173082103508620386313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4204512875770758617454005 394173082103508620386313)
                  ·
                    rfl

theorem cell22_3454422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3454422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454422 prefixEnd_3454422 := by exact prefixLift 3454422
  have htrace : WordTrace (prefixWord ++ tailWord_3454422) baseStart_3454422 baseEnd_3454422 := by
    simpa [prefixWord, tailWord_3454422, baseEnd_3454422] using wordTrace_append hprefix tailTrace_3454422
  have hstable : (prefixWord ++ tailWord_3454422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454422).length < 2 ^ (prefixWord ++ tailWord_3454422).sum := by decide
  have hdescent : baseEnd_3454422 < baseStart_3454422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454433 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 8]
def baseStart_3454433 : Nat := 118140960795 + 3454433 * 2 ^ 59
def prefixEnd_3454433 : Nat := 4983230072969 + 3 ^ 40 * 3454433 * 2
def baseEnd_3454433 : Nat := 394174337278441833044635

theorem tailTrace_3454433 : CollatzResearch.WordTrace tailWord_3454433 prefixEnd_3454433 394174337278441833044635 := by
  unfold tailWord_3454433
  simp only [CollatzResearch.WordTrace]
  refine ⟨125993522294186686031583953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83995681529457790687722635 125993522294186686031583953)
  ·
    refine ⟨94495141720640014523687965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125993522294186686031583953 94495141720640014523687965)
    ·
      refine ⟨35435678145240005446382987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94495141720640014523687965 35435678145240005446382987)
      ·
        refine ⟨53153517217860008169574481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35435678145240005446382987 53153517217860008169574481)
        ·
          refine ⟨39865137913395006127180861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53153517217860008169574481 39865137913395006127180861)
          ·
            refine ⟨14949426717523127297692823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39865137913395006127180861 14949426717523127297692823)
            ·
              refine ⟨22424140076284690946539235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14949426717523127297692823 22424140076284690946539235)
              ·
                refine ⟨33636210114427036419808853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22424140076284690946539235 33636210114427036419808853)
                ·
                  refine ⟨394174337278441833044635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33636210114427036419808853 394174337278441833044635)
                  ·
                    rfl

theorem cell22_3454433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_3454433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454433 prefixEnd_3454433 := by exact prefixLift 3454433
  have htrace : WordTrace (prefixWord ++ tailWord_3454433) baseStart_3454433 baseEnd_3454433 := by
    simpa [prefixWord, tailWord_3454433, baseEnd_3454433] using wordTrace_append hprefix tailTrace_3454433
  have hstable : (prefixWord ++ tailWord_3454433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454433).length < 2 ^ (prefixWord ++ tailWord_3454433).sum := by decide
  have hdescent : baseEnd_3454433 < baseStart_3454433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454435 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 3, 4]
def baseStart_3454435 : Nat := 118140960795 + 3454435 * 2 ^ 59
def prefixEnd_3454435 : Nat := 4983230072969 + 3 ^ 40 * 3454435 * 2
def baseEnd_3454435 : Nat := 1182523696476198160583899

theorem tailTrace_3454435 : CollatzResearch.WordTrace tailWord_3454435 prefixEnd_3454435 1182523696476198160583899 := by
  unfold tailWord_3454435
  simp only [CollatzResearch.WordTrace]
  refine ⟨125993595240179440373156759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83995730160119626915437839 125993595240179440373156759)
  ·
    refine ⟨188990392860269160559735139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125993595240179440373156759 188990392860269160559735139)
    ·
      refine ⟨283485589290403740839602709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188990392860269160559735139 283485589290403740839602709)
      ·
        refine ⟨13288386997987675351856377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 283485589290403740839602709 13288386997987675351856377)
        ·
          refine ⟨9966290248490756513892283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13288386997987675351856377 9966290248490756513892283)
          ·
            refine ⟨14949435372736134770838425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9966290248490756513892283 14949435372736134770838425)
            ·
              refine ⟨11212076529552101078128819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14949435372736134770838425 11212076529552101078128819)
              ·
                refine ⟨16818114794328151617193229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11212076529552101078128819 16818114794328151617193229)
                ·
                  refine ⟨6306793047873056856447461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16818114794328151617193229 6306793047873056856447461)
                  ·
                    refine ⟨1182523696476198160583899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6306793047873056856447461 1182523696476198160583899)
                    ·
                      rfl

theorem cell22_3454435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_3454435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454435 prefixEnd_3454435 := by exact prefixLift 3454435
  have htrace : WordTrace (prefixWord ++ tailWord_3454435) baseStart_3454435 baseEnd_3454435 := by
    simpa [prefixWord, tailWord_3454435, baseEnd_3454435] using wordTrace_append hprefix tailTrace_3454435
  have hstable : (prefixWord ++ tailWord_3454435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454435).length < 2 ^ (prefixWord ++ tailWord_3454435).sum := by decide
  have hdescent : baseEnd_3454435 < baseStart_3454435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454495 : List Nat := [1, 1, 2, 4, 1, 1, 6, 6]
def baseStart_3454495 : Nat := 118140960795 + 3454495 * 2 ^ 59
def prefixEnd_3454495 : Nat := 4983230072969 + 3 ^ 40 * 3454495 * 2
def baseEnd_3454495 : Nat := 131393803966930889342635

theorem tailTrace_3454495 : CollatzResearch.WordTrace tailWord_3454495 prefixEnd_3454495 131393803966930889342635 := by
  unfold tailWord_3454495
  simp only [CollatzResearch.WordTrace]
  refine ⟨125995783619962070620340939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83997189079974713746893959 125995783619962070620340939)
  ·
    refine ⟨188993675429943105930511409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125995783619962070620340939 188993675429943105930511409)
    ·
      refine ⟨141745256572457329447883557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188993675429943105930511409 141745256572457329447883557)
      ·
        refine ⟨26577235607335749271478167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141745256572457329447883557 26577235607335749271478167)
        ·
          refine ⟨39865853411003623907217251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26577235607335749271478167 39865853411003623907217251)
          ·
            refine ⟨59798780116505435860825877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39865853411003623907217251 59798780116505435860825877)
            ·
              refine ⟨2803067817961192305976213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59798780116505435860825877 2803067817961192305976213)
              ·
                refine ⟨131393803966930889342635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2803067817961192305976213 131393803966930889342635)
                ·
                  rfl

theorem cell22_3454495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 6].length) (baseStart_3454495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454495 prefixEnd_3454495 := by exact prefixLift 3454495
  have htrace : WordTrace (prefixWord ++ tailWord_3454495) baseStart_3454495 baseEnd_3454495 := by
    simpa [prefixWord, tailWord_3454495, baseEnd_3454495] using wordTrace_append hprefix tailTrace_3454495
  have hstable : (prefixWord ++ tailWord_3454495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454495).length < 2 ^ (prefixWord ++ tailWord_3454495).sum := by decide
  have hdescent : baseEnd_3454495 < baseStart_3454495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454508 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_3454508 : Nat := 118140960795 + 3454508 * 2 ^ 59
def prefixEnd_3454508 : Nat := 4983230072969 + 3 ^ 40 * 3454508 * 2
def baseEnd_3454508 : Nat := 1182548685868050303508675

theorem tailTrace_3454508 : CollatzResearch.WordTrace tailWord_3454508 prefixEnd_3454508 1182548685868050303508675 := by
  unfold tailWord_3454508
  simp only [CollatzResearch.WordTrace]
  refine ⟨62998128884457486920282089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83997505179276649227042785 62998128884457486920282089)
  ·
    refine ⟨47248596663343115190211567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62998128884457486920282089 47248596663343115190211567)
    ·
      refine ⟨70872894995014672785317351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47248596663343115190211567 70872894995014672785317351)
      ·
        refine ⟨106309342492522009177976027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70872894995014672785317351 106309342492522009177976027)
        ·
          refine ⟨159464013738783013766964041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106309342492522009177976027 159464013738783013766964041)
          ·
            refine ⟨119598010304087260325223031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159464013738783013766964041 119598010304087260325223031)
            ·
              refine ⟨179397015456130890487834547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119598010304087260325223031 179397015456130890487834547)
              ·
                refine ⟨269095523184196335731751821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179397015456130890487834547 269095523184196335731751821)
                ·
                  refine ⟨100910821194073625899406933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269095523184196335731751821 100910821194073625899406933)
                  ·
                    refine ⟨1182548685868050303508675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100910821194073625899406933 1182548685868050303508675)
                    ·
                      rfl

theorem cell22_3454508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_3454508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454508 prefixEnd_3454508 := by exact prefixLift 3454508
  have htrace : WordTrace (prefixWord ++ tailWord_3454508) baseStart_3454508 baseEnd_3454508 := by
    simpa [prefixWord, tailWord_3454508, baseEnd_3454508] using wordTrace_append hprefix tailTrace_3454508
  have hstable : (prefixWord ++ tailWord_3454508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454508).length < 2 ^ (prefixWord ++ tailWord_3454508).sum := by decide
  have hdescent : baseEnd_3454508 < baseStart_3454508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454527 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 3, 3]
def baseStart_3454527 : Nat := 118140960795 + 3454527 * 2 ^ 59
def prefixEnd_3454527 : Nat := 4983230072969 + 3 ^ 40 * 3454527 * 2
def baseEnd_3454527 : Nat := 1182555189956340587283617

theorem tailTrace_3454527 : CollatzResearch.WordTrace tailWord_3454527 prefixEnd_3454527 1182555189956340587283617 := by
  unfold tailWord_3454527
  simp only [CollatzResearch.WordTrace]
  refine ⟨125996950755846140085505835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83997967170564093390337223 125996950755846140085505835)
  ·
    refine ⟨188995426133769210128258753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125996950755846140085505835 188995426133769210128258753)
    ·
      refine ⟨141746569600326907596194065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188995426133769210128258753 141746569600326907596194065)
      ·
        refine ⟨106309927200245180697145549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141746569600326907596194065 106309927200245180697145549)
        ·
          refine ⟨39866222700091942761429581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106309927200245180697145549 39866222700091942761429581)
          ·
            refine ⟨14949833512534478535536093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39866222700091942761429581 14949833512534478535536093)
            ·
              refine ⟨5606187567200429450826035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14949833512534478535536093 5606187567200429450826035)
              ·
                refine ⟨8409281350800644176239053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606187567200429450826035 8409281350800644176239053)
                ·
                  refine ⟨3153480506550241566089645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8409281350800644176239053 3153480506550241566089645)
                  ·
                    refine ⟨1182555189956340587283617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153480506550241566089645 1182555189956340587283617)
                    ·
                      rfl

theorem cell22_3454527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_3454527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454527 prefixEnd_3454527 := by exact prefixLift 3454527
  have htrace : WordTrace (prefixWord ++ tailWord_3454527) baseStart_3454527 baseEnd_3454527 := by
    simpa [prefixWord, tailWord_3454527, baseEnd_3454527] using wordTrace_append hprefix tailTrace_3454527
  have hstable : (prefixWord ++ tailWord_3454527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454527).length < 2 ^ (prefixWord ++ tailWord_3454527).sum := by decide
  have hdescent : baseEnd_3454527 < baseStart_3454527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454574 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_3454574 : Nat := 118140960795 + 3454574 * 2 ^ 59
def prefixEnd_3454574 : Nat := 4983230072969 + 3 ^ 40 * 3454574 * 2
def baseEnd_3454574 : Nat := 394190426338949377119491

theorem tailTrace_3454574 : CollatzResearch.WordTrace tailWord_3454574 prefixEnd_3454574 394190426338949377119491 := by
  unfold tailWord_3454574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15749833123334483389058347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83999109991117244741644517 15749833123334483389058347)
  ·
    refine ⟨23624749685001725083587521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15749833123334483389058347 23624749685001725083587521)
    ·
      refine ⟨17718562263751293812690641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23624749685001725083587521 17718562263751293812690641)
      ·
        refine ⟨13288921697813470359517981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17718562263751293812690641 13288921697813470359517981)
        ·
          refine ⟨4983345636680051384819243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13288921697813470359517981 4983345636680051384819243)
          ·
            refine ⟨7475018455020077077228865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983345636680051384819243 7475018455020077077228865)
            ·
              refine ⟨5606263841265057807921649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7475018455020077077228865 5606263841265057807921649)
              ·
                refine ⟨4204697880948793355941237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5606263841265057807921649 4204697880948793355941237)
                ·
                  refine ⟨394190426338949377119491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4204697880948793355941237 394190426338949377119491)
                  ·
                    rfl

theorem cell22_3454574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_3454574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454574 prefixEnd_3454574 := by exact prefixLift 3454574
  have htrace : WordTrace (prefixWord ++ tailWord_3454574) baseStart_3454574 baseEnd_3454574 := by
    simpa [prefixWord, tailWord_3454574, baseEnd_3454574] using wordTrace_append hprefix tailTrace_3454574
  have hstable : (prefixWord ++ tailWord_3454574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454574).length < 2 ^ (prefixWord ++ tailWord_3454574).sum := by decide
  have hdescent : baseEnd_3454574 < baseStart_3454574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454578 : List Nat := [3, 2, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_3454578 : Nat := 118140960795 + 3454578 * 2 ^ 59
def prefixEnd_3454578 : Nat := 4983230072969 + 3 ^ 40 * 3454578 * 2
def baseEnd_3454578 : Nat := 1182572648298593454258461

theorem tailTrace_3454578 : CollatzResearch.WordTrace tailWord_3454578 prefixEnd_3454578 1182572648298593454258461 := by
  unfold tailWord_3454578
  simp only [CollatzResearch.WordTrace]
  refine ⟨31499702719665343948903097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83999207252440917197074925 31499702719665343948903097)
  ·
    refine ⟨23624777039749007961677323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31499702719665343948903097 23624777039749007961677323)
    ·
      refine ⟨35437165559623511942515985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23624777039749007961677323 35437165559623511942515985)
      ·
        refine ⟨26577874169717633956886989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35437165559623511942515985 26577874169717633956886989)
        ·
          refine ⟨9966702813644112733832621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26577874169717633956886989 9966702813644112733832621)
          ·
            refine ⟨3737513555116542275187233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9966702813644112733832621 3737513555116542275187233)
            ·
              refine ⟨2803135166337406706390425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3737513555116542275187233 2803135166337406706390425)
              ·
                refine ⟨2102351374753055029792819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2803135166337406706390425 2102351374753055029792819)
                ·
                  refine ⟨3153527062129582544689229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102351374753055029792819 3153527062129582544689229)
                  ·
                    refine ⟨1182572648298593454258461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153527062129582544689229 1182572648298593454258461)
                    ·
                      rfl

theorem cell22_3454578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_3454578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454578 prefixEnd_3454578 := by exact prefixLift 3454578
  have htrace : WordTrace (prefixWord ++ tailWord_3454578) baseStart_3454578 baseEnd_3454578 := by
    simpa [prefixWord, tailWord_3454578, baseEnd_3454578] using wordTrace_append hprefix tailTrace_3454578
  have hstable : (prefixWord ++ tailWord_3454578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454578).length < 2 ^ (prefixWord ++ tailWord_3454578).sum := by decide
  have hdescent : baseEnd_3454578 < baseStart_3454578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454585 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 6]
def baseStart_3454585 : Nat := 118140960795 + 3454585 * 2 ^ 59
def prefixEnd_3454585 : Nat := 4983230072969 + 3 ^ 40 * 3454585 * 2
def baseEnd_3454585 : Nat := 394191681513882589777813

theorem tailTrace_3454585 : CollatzResearch.WordTrace tailWord_3454585 prefixEnd_3454585 394191681513882589777813 := by
  unfold tailWord_3454585
  simp only [CollatzResearch.WordTrace]
  refine ⟨125999066189636015991117209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83999377459757343994078139 125999066189636015991117209)
  ·
    refine ⟨94499299642227011993337907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125999066189636015991117209 94499299642227011993337907)
    ·
      refine ⟨141748949463340517990006861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94499299642227011993337907 141748949463340517990006861)
      ·
        refine ⟨53155856048752694246252573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141748949463340517990006861 53155856048752694246252573)
        ·
          refine ⟨19933446018282260342344715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53155856048752694246252573 19933446018282260342344715)
          ·
            refine ⟨29900169027423390513517073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19933446018282260342344715 29900169027423390513517073)
            ·
              refine ⟨22425126770567542885137805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29900169027423390513517073 22425126770567542885137805)
              ·
                refine ⟨8409422538962828581926677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22425126770567542885137805 8409422538962828581926677)
                ·
                  refine ⟨394191681513882589777813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8409422538962828581926677 394191681513882589777813)
                  ·
                    rfl

theorem cell22_3454585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_3454585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454585 prefixEnd_3454585 := by exact prefixLift 3454585
  have htrace : WordTrace (prefixWord ++ tailWord_3454585) baseStart_3454585 baseEnd_3454585 := by
    simpa [prefixWord, tailWord_3454585, baseEnd_3454585] using wordTrace_append hprefix tailTrace_3454585
  have hstable : (prefixWord ++ tailWord_3454585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454585).length < 2 ^ (prefixWord ++ tailWord_3454585).sum := by decide
  have hdescent : baseEnd_3454585 < baseStart_3454585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454602 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_3454602 : Nat := 118140960795 + 3454602 * 2 ^ 59
def prefixEnd_3454602 : Nat := 4983230072969 + 3 ^ 40 * 3454602 * 2
def baseEnd_3454602 : Nat := 394193621329688463886129

theorem tailTrace_3454602 : CollatzResearch.WordTrace tailWord_3454602 prefixEnd_3454602 394193621329688463886129 := by
  unfold tailWord_3454602
  simp only [CollatzResearch.WordTrace]
  refine ⟨31499921557643606973621515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83999790820382951929657373 31499921557643606973621515)
  ·
    refine ⟨47249882336465410460432273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31499921557643606973621515 47249882336465410460432273)
    ·
      refine ⟨35437411752349057845324205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47249882336465410460432273 35437411752349057845324205)
      ·
        refine ⟨13289029407130896691996577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35437411752349057845324205 13289029407130896691996577)
        ·
          refine ⟨9966772055348172518997433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13289029407130896691996577 9966772055348172518997433)
          ·
            refine ⟨7475079041511129389248075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9966772055348172518997433 7475079041511129389248075)
            ·
              refine ⟨11212618562266694083872113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475079041511129389248075 11212618562266694083872113)
              ·
                refine ⟨8409463921700020562904085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11212618562266694083872113 8409463921700020562904085)
                ·
                  refine ⟨394193621329688463886129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8409463921700020562904085 394193621329688463886129)
                  ·
                    rfl

theorem cell22_3454602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_3454602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454602 prefixEnd_3454602 := by exact prefixLift 3454602
  have htrace : WordTrace (prefixWord ++ tailWord_3454602) baseStart_3454602 baseEnd_3454602 := by
    simpa [prefixWord, tailWord_3454602, baseEnd_3454602] using wordTrace_append hprefix tailTrace_3454602
  have hstable : (prefixWord ++ tailWord_3454602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454602).length < 2 ^ (prefixWord ++ tailWord_3454602).sum := by decide
  have hdescent : baseEnd_3454602 < baseStart_3454602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454692 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 5]
def baseStart_3454692 : Nat := 118140960795 + 3454692 * 2 ^ 59
def prefixEnd_3454692 : Nat := 4983230072969 + 3 ^ 40 * 3454692 * 2
def baseEnd_3454692 : Nat := 394203890942778385636037

theorem tailTrace_3454692 : CollatzResearch.WordTrace tailWord_3454692 prefixEnd_3454692 394203890942778385636037 := by
  unfold tailWord_3454692
  simp only [CollatzResearch.WordTrace]
  refine ⟨63001484400124186632631165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84001979200165582176841553 63001484400124186632631165)
  ·
    refine ⟨23625556650046569987236687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63001484400124186632631165 23625556650046569987236687)
    ·
      refine ⟨35438334975069854980855031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23625556650046569987236687 35438334975069854980855031)
      ·
        refine ⟨53157502462604782471282547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35438334975069854980855031 53157502462604782471282547)
        ·
          refine ⟨79736253693907173706923821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53157502462604782471282547 79736253693907173706923821)
          ·
            refine ⟨29901095135215190140096433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79736253693907173706923821 29901095135215190140096433)
            ·
              refine ⟨22425821351411392605072325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29901095135215190140096433 22425821351411392605072325)
              ·
                refine ⟨4204841503389636113451061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22425821351411392605072325 4204841503389636113451061)
                ·
                  refine ⟨394203890942778385636037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4204841503389636113451061 394203890942778385636037)
                  ·
                    rfl

theorem cell22_3454692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_3454692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454692 prefixEnd_3454692 := by exact prefixLift 3454692
  have htrace : WordTrace (prefixWord ++ tailWord_3454692) baseStart_3454692 baseEnd_3454692 := by
    simpa [prefixWord, tailWord_3454692, baseEnd_3454692] using wordTrace_append hprefix tailTrace_3454692
  have hstable : (prefixWord ++ tailWord_3454692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454692).length < 2 ^ (prefixWord ++ tailWord_3454692).sum := by decide
  have hdescent : baseEnd_3454692 < baseStart_3454692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454696 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 3, 3]
def baseStart_3454696 : Nat := 118140960795 + 3454696 * 2 ^ 59
def prefixEnd_3454696 : Nat := 4983230072969 + 3 ^ 40 * 3454696 * 2
def baseEnd_3454696 : Nat := 1182613042110080479808099

theorem tailTrace_3454696 : CollatzResearch.WordTrace tailWord_3454696 prefixEnd_3454696 1182613042110080479808099 := by
  unfold tailWord_3454696
  simp only [CollatzResearch.WordTrace]
  refine ⟨63001557346116940974203971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84002076461489254632271961 63001557346116940974203971)
  ·
    refine ⟨94502336019175411461305957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63001557346116940974203971 94502336019175411461305957)
    ·
      refine ⟨17719188003595389648994867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94502336019175411461305957 17719188003595389648994867)
      ·
        refine ⟨26578782005393084473492301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17719188003595389648994867 26578782005393084473492301)
        ·
          refine ⟨9967043252022406677559613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26578782005393084473492301 9967043252022406677559613)
          ·
            refine ⟨3737641219508402504084855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9967043252022406677559613 3737641219508402504084855)
            ·
              refine ⟨5606461829262603756127283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737641219508402504084855 5606461829262603756127283)
              ·
                refine ⟨8409692743893905634190925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606461829262603756127283 8409692743893905634190925)
                ·
                  refine ⟨3153634778960214612821597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8409692743893905634190925 3153634778960214612821597)
                  ·
                    refine ⟨1182613042110080479808099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153634778960214612821597 1182613042110080479808099)
                    ·
                      rfl

theorem cell22_3454696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_3454696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454696 prefixEnd_3454696 := by exact prefixLift 3454696
  have htrace : WordTrace (prefixWord ++ tailWord_3454696) baseStart_3454696 baseEnd_3454696 := by
    simpa [prefixWord, tailWord_3454696, baseEnd_3454696] using wordTrace_append hprefix tailTrace_3454696
  have hstable : (prefixWord ++ tailWord_3454696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454696).length < 2 ^ (prefixWord ++ tailWord_3454696).sum := by decide
  have hdescent : baseEnd_3454696 < baseStart_3454696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454752 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_3454752 : Nat := 118140960795 + 3454752 * 2 ^ 59
def prefixEnd_3454752 : Nat := 4983230072969 + 3 ^ 40 * 3454752 * 2
def baseEnd_3454752 : Nat := 1182632212054515000407927

theorem tailTrace_3454752 : CollatzResearch.WordTrace tailWord_3454752 prefixEnd_3454752 1182632212054515000407927 := by
  unfold tailWord_3454752
  simp only [CollatzResearch.WordTrace]
  refine ⟨63002578590015501756223255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84003438120020669008297673 63002578590015501756223255)
  ·
    refine ⟨94503867885023252634334883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63002578590015501756223255 94503867885023252634334883)
    ·
      refine ⟨141755801827534878951502325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94503867885023252634334883 141755801827534878951502325)
      ·
        refine ⟨13289606421331394901703343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141755801827534878951502325 13289606421331394901703343)
        ·
          refine ⟨19934409631997092352555015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13289606421331394901703343 19934409631997092352555015)
          ·
            refine ⟨29901614447995638528832523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19934409631997092352555015 29901614447995638528832523)
            ·
              refine ⟨44852421671993457793248785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29901614447995638528832523 44852421671993457793248785)
              ·
                refine ⟨33639316253995093344936589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44852421671993457793248785 33639316253995093344936589)
                ·
                  refine ⟨12614743595248160004351221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33639316253995093344936589 12614743595248160004351221)
                  ·
                    refine ⟨1182632212054515000407927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12614743595248160004351221 1182632212054515000407927)
                    ·
                      rfl

theorem cell22_3454752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_3454752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454752 prefixEnd_3454752 := by exact prefixLift 3454752
  have htrace : WordTrace (prefixWord ++ tailWord_3454752) baseStart_3454752 baseEnd_3454752 := by
    simpa [prefixWord, tailWord_3454752, baseEnd_3454752] using wordTrace_append hprefix tailTrace_3454752
  have hstable : (prefixWord ++ tailWord_3454752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454752).length < 2 ^ (prefixWord ++ tailWord_3454752).sum := by decide
  have hdescent : baseEnd_3454752 < baseStart_3454752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454769 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_3454769 : Nat := 118140960795 + 3454769 * 2 ^ 59
def prefixEnd_3454769 : Nat := 4983230072969 + 3 ^ 40 * 3454769 * 2
def baseEnd_3454769 : Nat := 1182638031501932622732875

theorem tailTrace_3454769 : CollatzResearch.WordTrace tailWord_3454769 prefixEnd_3454769 1182638031501932622732875 := by
  unfold tailWord_3454769
  simp only [CollatzResearch.WordTrace]
  refine ⟨126005777220969415415815361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84003851480646276943876907 126005777220969415415815361)
  ·
    refine ⟨94504332915727061561861521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126005777220969415415815361 94504332915727061561861521)
    ·
      refine ⟨70878249686795296171396141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94504332915727061561861521 70878249686795296171396141)
      ·
        refine ⟨26579343632548236064273553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70878249686795296171396141 26579343632548236064273553)
        ·
          refine ⟨19934507724411177048205165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26579343632548236064273553 19934507724411177048205165)
          ·
            refine ⟨7475440396654191393076937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19934507724411177048205165 7475440396654191393076937)
            ·
              refine ⟨5606580297490643544807703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7475440396654191393076937 5606580297490643544807703)
              ·
                refine ⟨8409870446235965317211555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606580297490643544807703 8409870446235965317211555)
                ·
                  refine ⟨12614805669353947975817333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8409870446235965317211555 12614805669353947975817333)
                  ·
                    refine ⟨1182638031501932622732875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12614805669353947975817333 1182638031501932622732875)
                    ·
                      rfl

theorem cell22_3454769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_3454769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454769 prefixEnd_3454769 := by exact prefixLift 3454769
  have htrace : WordTrace (prefixWord ++ tailWord_3454769) baseStart_3454769 baseEnd_3454769 := by
    simpa [prefixWord, tailWord_3454769, baseEnd_3454769] using wordTrace_append hprefix tailTrace_3454769
  have hstable : (prefixWord ++ tailWord_3454769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454769).length < 2 ^ (prefixWord ++ tailWord_3454769).sum := by decide
  have hdescent : baseEnd_3454769 < baseStart_3454769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454790 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3454790 : Nat := 118140960795 + 3454790 * 2 ^ 59
def prefixEnd_3454790 : Nat := 4983230072969 + 3 ^ 40 * 3454790 * 2
def baseEnd_3454790 : Nat := 1182645220231095567957811

theorem tailTrace_3454790 : CollatzResearch.WordTrace tailWord_3454790 prefixEnd_3454790 1182645220231095567957811 := by
  unfold tailWord_3454790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937704473559166750072807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84004362102595557334886549 3937704473559166750072807)
  ·
    refine ⟨5906556710338750125109211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3937704473559166750072807 5906556710338750125109211)
    ·
      refine ⟨8859835065508125187663817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5906556710338750125109211 8859835065508125187663817)
      ·
        refine ⟨6644876299131093890747863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8859835065508125187663817 6644876299131093890747863)
        ·
          refine ⟨9967314448696640836121795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6644876299131093890747863 9967314448696640836121795)
          ·
            refine ⟨14950971673044961254182693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9967314448696640836121795 14950971673044961254182693)
            ·
              refine ⟨2803307188695930235159255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14950971673044961254182693 2803307188695930235159255)
              ·
                refine ⟨4204960783043895352738883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803307188695930235159255 4204960783043895352738883)
                ·
                  refine ⟨6307441174565843029108325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4204960783043895352738883 6307441174565843029108325)
                  ·
                    refine ⟨1182645220231095567957811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6307441174565843029108325 1182645220231095567957811)
                    ·
                      rfl

theorem cell22_3454790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3454790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454790 prefixEnd_3454790 := by exact prefixLift 3454790
  have htrace : WordTrace (prefixWord ++ tailWord_3454790) baseStart_3454790 baseEnd_3454790 := by
    simpa [prefixWord, tailWord_3454790, baseEnd_3454790] using wordTrace_append hprefix tailTrace_3454790
  have hstable : (prefixWord ++ tailWord_3454790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454790).length < 2 ^ (prefixWord ++ tailWord_3454790).sum := by decide
  have hdescent : baseEnd_3454790 < baseStart_3454790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454842 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_3454842 : Nat := 118140960795 + 3454842 * 2 ^ 59
def prefixEnd_3454842 : Nat := 4983230072969 + 3 ^ 40 * 3454842 * 2
def baseEnd_3454842 : Nat := 1182663020893784765657651

theorem tailTrace_3454842 : CollatzResearch.WordTrace tailWord_3454842 prefixEnd_3454842 1182663020893784765657651 := by
  unfold tailWord_3454842
  simp only [CollatzResearch.WordTrace]
  refine ⟨31502109937426237220805695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84005626499803299255481853 31502109937426237220805695)
  ·
    refine ⟨47253164906139355831208543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31502109937426237220805695 47253164906139355831208543)
    ·
      refine ⟨70879747359209033746812815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47253164906139355831208543 70879747359209033746812815)
      ·
        refine ⟨106319621038813550620219223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70879747359209033746812815 106319621038813550620219223)
        ·
          refine ⟨159479431558220325930328835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106319621038813550620219223 159479431558220325930328835)
          ·
            refine ⟨239219147337330488895493253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159479431558220325930328835 239219147337330488895493253)
            ·
              refine ⟨44853590125749466667904985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239219147337330488895493253 44853590125749466667904985)
              ·
                refine ⟨33640192594312100000928739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44853590125749466667904985 33640192594312100000928739)
                ·
                  refine ⟨50460288891468150001393109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33640192594312100000928739 50460288891468150001393109)
                  ·
                    refine ⟨1182663020893784765657651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50460288891468150001393109 1182663020893784765657651)
                    ·
                      rfl

theorem cell22_3454842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_3454842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454842 prefixEnd_3454842 := by exact prefixLift 3454842
  have htrace : WordTrace (prefixWord ++ tailWord_3454842) baseStart_3454842 baseEnd_3454842 := by
    simpa [prefixWord, tailWord_3454842, baseEnd_3454842] using wordTrace_append hprefix tailTrace_3454842
  have hstable : (prefixWord ++ tailWord_3454842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454842).length < 2 ^ (prefixWord ++ tailWord_3454842).sum := by decide
  have hdescent : baseEnd_3454842 < baseStart_3454842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454904 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_3454904 : Nat := 118140960795 + 3454904 * 2 ^ 59
def prefixEnd_3454904 : Nat := 4983230072969 + 3 ^ 40 * 3454904 * 2
def baseEnd_3454904 : Nat := 1182684244760837270607461

theorem tailTrace_3454904 : CollatzResearch.WordTrace tailWord_3454904 prefixEnd_3454904 1182684244760837270607461 := by
  unfold tailWord_3454904
  simp only [CollatzResearch.WordTrace]
  refine ⟨63005350537740166735989883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84007134050320222314653177 63005350537740166735989883)
  ·
    refine ⟨94508025806610250103984825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63005350537740166735989883 94508025806610250103984825)
    ·
      refine ⟨70881019354957687577988619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94508025806610250103984825 70881019354957687577988619)
      ·
        refine ⟨106321529032436531366982929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70881019354957687577988619 106321529032436531366982929)
        ·
          refine ⟨79741146774327398525237197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106321529032436531366982929 79741146774327398525237197)
          ·
            refine ⟨29902930040372774446963949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79741146774327398525237197 29902930040372774446963949)
            ·
              refine ⟨11213598765139790417611481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29902930040372774446963949 11213598765139790417611481)
              ·
                refine ⟨8410199073854842813208611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11213598765139790417611481 8410199073854842813208611)
                ·
                  refine ⟨12615298610782264219812917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410199073854842813208611 12615298610782264219812917)
                  ·
                    refine ⟨1182684244760837270607461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12615298610782264219812917 1182684244760837270607461)
                    ·
                      rfl

theorem cell22_3454904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_3454904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454904 prefixEnd_3454904 := by exact prefixLift 3454904
  have htrace : WordTrace (prefixWord ++ tailWord_3454904) baseStart_3454904 baseEnd_3454904 := by
    simpa [prefixWord, tailWord_3454904, baseEnd_3454904] using wordTrace_append hprefix tailTrace_3454904
  have hstable : (prefixWord ++ tailWord_3454904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454904).length < 2 ^ (prefixWord ++ tailWord_3454904).sum := by decide
  have hdescent : baseEnd_3454904 < baseStart_3454904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454940 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 6]
def baseStart_3454940 : Nat := 118140960795 + 3454940 * 2 ^ 59
def prefixEnd_3454940 : Nat := 4983230072969 + 3 ^ 40 * 3454940 * 2
def baseEnd_3454940 : Nat := 394232189432181725569117

theorem tailTrace_3454940 : CollatzResearch.WordTrace tailWord_3454940 prefixEnd_3454940 394232189432181725569117 := by
  unfold tailWord_3454940
  simp only [CollatzResearch.WordTrace]
  refine ⟨63006007051674955810145137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84008009402233274413526849 63006007051674955810145137)
  ·
    refine ⟨47254505288756216857608853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63006007051674955810145137 47254505288756216857608853)
    ·
      refine ⟨2215054935410447665200415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47254505288756216857608853 2215054935410447665200415)
      ·
        refine ⟨3322582403115671497800623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215054935410447665200415 3322582403115671497800623)
        ·
          refine ⟨4983873604673507246700935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322582403115671497800623 4983873604673507246700935)
          ·
            refine ⟨7475810407010260870051403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983873604673507246700935 7475810407010260870051403)
            ·
              refine ⟨11213715610515391305077105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475810407010260870051403 11213715610515391305077105)
              ·
                refine ⟨8410286707886543478807829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11213715610515391305077105 8410286707886543478807829)
                ·
                  refine ⟨394232189432181725569117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8410286707886543478807829 394232189432181725569117)
                  ·
                    rfl

theorem cell22_3454940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_3454940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454940 prefixEnd_3454940 := by exact prefixLift 3454940
  have htrace : WordTrace (prefixWord ++ tailWord_3454940) baseStart_3454940 baseEnd_3454940 := by
    simpa [prefixWord, tailWord_3454940, baseEnd_3454940] using wordTrace_append hprefix tailTrace_3454940
  have hstable : (prefixWord ++ tailWord_3454940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454940).length < 2 ^ (prefixWord ++ tailWord_3454940).sum := by decide
  have hdescent : baseEnd_3454940 < baseStart_3454940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454983 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 3, 3]
def baseStart_3454983 : Nat := 118140960795 + 3454983 * 2 ^ 59
def prefixEnd_3454983 : Nat := 4983230072969 + 3 ^ 40 * 3454983 * 2
def baseEnd_3454983 : Nat := 1182711288075307397882219

theorem tailTrace_3454983 : CollatzResearch.WordTrace tailWord_3454983 prefixEnd_3454983 1182711288075307397882219 := by
  unfold tailWord_3454983
  simp only [CollatzResearch.WordTrace]
  refine ⟨126013582442194129964105603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84009054961462753309403735 126013582442194129964105603)
  ·
    refine ⟨189020373663291194946158405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126013582442194129964105603 189020373663291194946158405)
    ·
      refine ⟨35441320061867099052404701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189020373663291194946158405 35441320061867099052404701)
      ·
        refine ⟨13290495023200162144651763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35441320061867099052404701 13290495023200162144651763)
        ·
          refine ⟨19935742534800243216977645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13290495023200162144651763 19935742534800243216977645)
          ·
            refine ⟨7475903450550091206366617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19935742534800243216977645 7475903450550091206366617)
            ·
              refine ⟨5606927587912568404774963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7475903450550091206366617 5606927587912568404774963)
              ·
                refine ⟨8410391381868852607162445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606927587912568404774963 8410391381868852607162445)
                ·
                  refine ⟨3153896768200819727685917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8410391381868852607162445 3153896768200819727685917)
                  ·
                    refine ⟨1182711288075307397882219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153896768200819727685917 1182711288075307397882219)
                    ·
                      rfl

theorem cell22_3454983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_3454983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454983 prefixEnd_3454983 := by exact prefixLift 3454983
  have htrace : WordTrace (prefixWord ++ tailWord_3454983) baseStart_3454983 baseEnd_3454983 := by
    simpa [prefixWord, tailWord_3454983, baseEnd_3454983] using wordTrace_append hprefix tailTrace_3454983
  have hstable : (prefixWord ++ tailWord_3454983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454983).length < 2 ^ (prefixWord ++ tailWord_3454983).sum := by decide
  have hdescent : baseEnd_3454983 < baseStart_3454983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3454989 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3454989 : Nat := 118140960795 + 3454989 * 2 ^ 59
def prefixEnd_3454989 : Nat := 4983230072969 + 3 ^ 40 * 3454989 * 2
def baseEnd_3454989 : Nat := 1182713341997925382232201

theorem tailTrace_3454989 : CollatzResearch.WordTrace tailWord_3454989 prefixEnd_3454989 1182713341997925382232201 := by
  unfold tailWord_3454989
  simp only [CollatzResearch.WordTrace]
  refine ⟨126013801280172392988824021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84009200853448261992549347 126013801280172392988824021)
  ·
    refine ⟨2953448467504040460675563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 126013801280172392988824021 2953448467504040460675563)
    ·
      refine ⟨4430172701256060691013345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2953448467504040460675563 4430172701256060691013345)
      ·
        refine ⟨3322629525942045518260009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430172701256060691013345 3322629525942045518260009)
        ·
          refine ⟨2491972144456534138695007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3322629525942045518260009 2491972144456534138695007)
          ·
            refine ⟨3737958216684801208042511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491972144456534138695007 3737958216684801208042511)
            ·
              refine ⟨5606937325027201812063767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737958216684801208042511 5606937325027201812063767)
              ·
                refine ⟨8410405987540802718095651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5606937325027201812063767 8410405987540802718095651)
                ·
                  refine ⟨12615608981311204077143477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8410405987540802718095651 12615608981311204077143477)
                  ·
                    refine ⟨1182713341997925382232201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12615608981311204077143477 1182713341997925382232201)
                    ·
                      rfl

theorem cell22_3454989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3454989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3454989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3454989 prefixEnd_3454989 := by exact prefixLift 3454989
  have htrace : WordTrace (prefixWord ++ tailWord_3454989) baseStart_3454989 baseEnd_3454989 := by
    simpa [prefixWord, tailWord_3454989, baseEnd_3454989] using wordTrace_append hprefix tailTrace_3454989
  have hstable : (prefixWord ++ tailWord_3454989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3454989).length < 2 ^ (prefixWord ++ tailWord_3454989).sum := by decide
  have hdescent : baseEnd_3454989 < baseStart_3454989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3454989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455090 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_3455090 : Nat := 118140960795 + 3455090 * 2 ^ 59
def prefixEnd_3455090 : Nat := 4983230072969 + 3 ^ 40 * 3455090 * 2
def baseEnd_3455090 : Nat := 1182747916361994785456891

theorem tailTrace_3455090 : CollatzResearch.WordTrace tailWord_3455090 prefixEnd_3455090 1182747916361994785456891 := by
  unfold tailWord_3455090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31504371263201621809562681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84011656701870991492167149 31504371263201621809562681)
  ·
    refine ⟨23628278447401216357172011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31504371263201621809562681 23628278447401216357172011)
    ·
      refine ⟨35442417671101824535758017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23628278447401216357172011 35442417671101824535758017)
      ·
        refine ⟨26581813253326368401818513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35442417671101824535758017 26581813253326368401818513)
        ·
          refine ⟨19936359939994776301363885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26581813253326368401818513 19936359939994776301363885)
          ·
            refine ⟨7476134977498041113011457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19936359939994776301363885 7476134977498041113011457)
            ·
              refine ⟨5607101233123530834758593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7476134977498041113011457 5607101233123530834758593)
              ·
                refine ⟨4205325924842648126068945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607101233123530834758593 4205325924842648126068945)
                ·
                  refine ⟨3153994443631986094551709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205325924842648126068945 3153994443631986094551709)
                  ·
                    refine ⟨1182747916361994785456891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3153994443631986094551709 1182747916361994785456891)
                    ·
                      rfl

theorem cell22_3455090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_3455090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455090 prefixEnd_3455090 := by exact prefixLift 3455090
  have htrace : WordTrace (prefixWord ++ tailWord_3455090) baseStart_3455090 baseEnd_3455090 := by
    simpa [prefixWord, tailWord_3455090, baseEnd_3455090] using wordTrace_append hprefix tailTrace_3455090
  have hstable : (prefixWord ++ tailWord_3455090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455090).length < 2 ^ (prefixWord ++ tailWord_3455090).sum := by decide
  have hdescent : baseEnd_3455090 < baseStart_3455090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455191 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3455191 : Nat := 118140960795 + 3455191 * 2 ^ 59
def prefixEnd_3455191 : Nat := 4983230072969 + 3 ^ 40 * 3455191 * 2
def baseEnd_3455191 : Nat := 1182782490726064188681581

theorem tailTrace_3455191 : CollatzResearch.WordTrace tailWord_3455191 prefixEnd_3455191 1182782490726064188681581 := by
  unfold tailWord_3455191
  simp only [CollatzResearch.WordTrace]
  refine ⟨126021168825440581487677427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84014112550293720991784951 126021168825440581487677427)
  ·
    refine ⟨189031753238160872231516141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126021168825440581487677427 189031753238160872231516141)
    ·
      refine ⟨70886907464310327086818553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189031753238160872231516141 70886907464310327086818553)
      ·
        refine ⟨53165180598232745315113915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70886907464310327086818553 53165180598232745315113915)
        ·
          refine ⟨79747770897349117972670873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53165180598232745315113915 79747770897349117972670873)
          ·
            refine ⟨59810828173011838479503155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79747770897349117972670873 59810828173011838479503155)
            ·
              refine ⟨89716242259517757719254733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59810828173011838479503155 89716242259517757719254733)
              ·
                refine ⟨33643590847319159144720525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89716242259517757719254733 33643590847319159144720525)
                ·
                  refine ⟨12616346567744684679270197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33643590847319159144720525 12616346567744684679270197)
                  ·
                    refine ⟨1182782490726064188681581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12616346567744684679270197 1182782490726064188681581)
                    ·
                      rfl

theorem cell22_3455191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3455191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455191 prefixEnd_3455191 := by exact prefixLift 3455191
  have htrace : WordTrace (prefixWord ++ tailWord_3455191) baseStart_3455191 baseEnd_3455191 := by
    simpa [prefixWord, tailWord_3455191, baseEnd_3455191] using wordTrace_append hprefix tailTrace_3455191
  have hstable : (prefixWord ++ tailWord_3455191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455191).length < 2 ^ (prefixWord ++ tailWord_3455191).sum := by decide
  have hdescent : baseEnd_3455191 < baseStart_3455191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455240 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_3455240 : Nat := 118140960795 + 3455240 * 2 ^ 59
def prefixEnd_3455240 : Nat := 4983230072969 + 3 ^ 40 * 3455240 * 2
def baseEnd_3455240 : Nat := 1182799264427444394206431

theorem tailTrace_3455240 : CollatzResearch.WordTrace tailWord_3455240 prefixEnd_3455240 1182799264427444394206431 := by
  unfold tailWord_3455240
  simp only [CollatzResearch.WordTrace]
  refine ⟨63011478001131531428105587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84015304001508708570807449 63011478001131531428105587)
  ·
    refine ⟨94517217001697297142158381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63011478001131531428105587 94517217001697297142158381)
    ·
      refine ⟨35443956375636486428309393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94517217001697297142158381 35443956375636486428309393)
      ·
        refine ⟨26582967281727364821232045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35443956375636486428309393 26582967281727364821232045)
        ·
          refine ⟨9968612730647761807962017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26582967281727364821232045 9968612730647761807962017)
          ·
            refine ⟨7476459547985821355971513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9968612730647761807962017 7476459547985821355971513)
            ·
              refine ⟨5607344660989366016978635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7476459547985821355971513 5607344660989366016978635)
              ·
                refine ⟨8411016991484049025467953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607344660989366016978635 8411016991484049025467953)
                ·
                  refine ⟨6308262743613036769100965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8411016991484049025467953 6308262743613036769100965)
                  ·
                    refine ⟨1182799264427444394206431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6308262743613036769100965 1182799264427444394206431)
                    ·
                      rfl

theorem cell22_3455240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_3455240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455240 prefixEnd_3455240 := by exact prefixLift 3455240
  have htrace : WordTrace (prefixWord ++ tailWord_3455240) baseStart_3455240 baseEnd_3455240 := by
    simpa [prefixWord, tailWord_3455240, baseEnd_3455240] using wordTrace_append hprefix tailTrace_3455240
  have hstable : (prefixWord ++ tailWord_3455240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455240).length < 2 ^ (prefixWord ++ tailWord_3455240).sum := by decide
  have hdescent : baseEnd_3455240 < baseStart_3455240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455251 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 4, 6]
def baseStart_3455251 : Nat := 118140960795 + 3455251 * 2 ^ 59
def prefixEnd_3455251 : Nat := 4983230072969 + 3 ^ 40 * 3455251 * 2
def baseEnd_3455251 : Nat := 1182803029952244032181397

theorem tailTrace_3455251 : CollatzResearch.WordTrace tailWord_3455251 prefixEnd_3455251 1182803029952244032181397 := by
  unfold tailWord_3455251
  simp only [CollatzResearch.WordTrace]
  refine ⟨126023357205223211734861607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84015571470148807823241071 126023357205223211734861607)
  ·
    refine ⟨189035035807834817602292411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126023357205223211734861607 189035035807834817602292411)
    ·
      refine ⟨283552553711752226403438617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189035035807834817602292411 283552553711752226403438617)
      ·
        refine ⟨212664415283814169802578963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283552553711752226403438617 212664415283814169802578963)
        ·
          refine ⟨318996622925721254703868445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212664415283814169802578963 318996622925721254703868445)
          ·
            refine ⟨119623733597145470513950667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318996622925721254703868445 119623733597145470513950667)
            ·
              refine ⟨179435600395718205770926001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119623733597145470513950667 179435600395718205770926001)
              ·
                refine ⟨134576700296788654328194501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179435600395718205770926001 134576700296788654328194501)
                ·
                  refine ⟨25233131305647872686536469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134576700296788654328194501 25233131305647872686536469)
                  ·
                    refine ⟨1182803029952244032181397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25233131305647872686536469 1182803029952244032181397)
                    ·
                      rfl

theorem cell22_3455251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_3455251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455251 prefixEnd_3455251 := by exact prefixLift 3455251
  have htrace : WordTrace (prefixWord ++ tailWord_3455251) baseStart_3455251 baseEnd_3455251 := by
    simpa [prefixWord, tailWord_3455251, baseEnd_3455251] using wordTrace_append hprefix tailTrace_3455251
  have hstable : (prefixWord ++ tailWord_3455251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455251).length < 2 ^ (prefixWord ++ tailWord_3455251).sum := by decide
  have hdescent : baseEnd_3455251 < baseStart_3455251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455261 : List Nat := [1, 4, 2, 3, 3, 1, 2, 2, 4]
def baseStart_3455261 : Nat := 118140960795 + 3455261 * 2 ^ 59
def prefixEnd_3455261 : Nat := 4983230072969 + 3 ^ 40 * 3455261 * 2
def baseEnd_3455261 : Nat := 394268817718869113143789

theorem tailTrace_3455261 : CollatzResearch.WordTrace tailWord_3455261 prefixEnd_3455261 394268817718869113143789 := by
  unfold tailWord_3455261
  simp only [CollatzResearch.WordTrace]
  refine ⟨126023721935186983442725637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84015814623457988961817091 126023721935186983442725637)
  ·
    refine ⟨23629447862847559395511057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126023721935186983442725637 23629447862847559395511057)
    ·
      refine ⟨17722085897135669546633293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23629447862847559395511057 17722085897135669546633293)
      ·
        refine ⟨6645782211425876079987485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17722085897135669546633293 6645782211425876079987485)
        ·
          refine ⟨2492168329284703529995307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6645782211425876079987485 2492168329284703529995307)
          ·
            refine ⟨3738252493927055294992961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492168329284703529995307 3738252493927055294992961)
            ·
              refine ⟨2803689370445291471244721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3738252493927055294992961 2803689370445291471244721)
              ·
                refine ⟨2102767027833968603433541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2803689370445291471244721 2102767027833968603433541)
                ·
                  refine ⟨394268817718869113143789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2102767027833968603433541 394268817718869113143789)
                  ·
                    rfl

theorem cell22_3455261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_3455261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455261 prefixEnd_3455261 := by exact prefixLift 3455261
  have htrace : WordTrace (prefixWord ++ tailWord_3455261) baseStart_3455261 baseEnd_3455261 := by
    simpa [prefixWord, tailWord_3455261, baseEnd_3455261] using wordTrace_append hprefix tailTrace_3455261
  have hstable : (prefixWord ++ tailWord_3455261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455261).length < 2 ^ (prefixWord ++ tailWord_3455261).sum := by decide
  have hdescent : baseEnd_3455261 < baseStart_3455261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455268 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_3455268 : Nat := 118140960795 + 3455268 * 2 ^ 59
def prefixEnd_3455268 : Nat := 4983230072969 + 3 ^ 40 * 3455268 * 2
def baseEnd_3455268 : Nat := 1182808849399661654506345

theorem tailTrace_3455268 : CollatzResearch.WordTrace tailWord_3455268 prefixEnd_3455268 1182808849399661654506345 := by
  unfold tailWord_3455268
  simp only [CollatzResearch.WordTrace]
  refine ⟨63011988623080811819115229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84015984830774415758820305 63011988623080811819115229)
  ·
    refine ⟨23629495733655304432168211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63011988623080811819115229 23629495733655304432168211)
    ·
      refine ⟨35444243600482956648252317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23629495733655304432168211 35444243600482956648252317)
      ·
        refine ⟨13291591350181108743094619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35444243600482956648252317 13291591350181108743094619)
        ·
          refine ⟨19937387025271663114641929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13291591350181108743094619 19937387025271663114641929)
          ·
            refine ⟨14953040268953747335981447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19937387025271663114641929 14953040268953747335981447)
            ·
              refine ⟨22429560403430621003972171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14953040268953747335981447 22429560403430621003972171)
              ·
                refine ⟨33644340605145931505958257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22429560403430621003972171 33644340605145931505958257)
                ·
                  refine ⟨25233255453859448629468693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33644340605145931505958257 25233255453859448629468693)
                  ·
                    refine ⟨1182808849399661654506345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25233255453859448629468693 1182808849399661654506345)
                    ·
                      rfl

theorem cell22_3455268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_3455268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455268 prefixEnd_3455268 := by exact prefixLift 3455268
  have htrace : WordTrace (prefixWord ++ tailWord_3455268) baseStart_3455268 baseEnd_3455268 := by
    simpa [prefixWord, tailWord_3455268, baseEnd_3455268] using wordTrace_append hprefix tailTrace_3455268
  have hstable : (prefixWord ++ tailWord_3455268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455268).length < 2 ^ (prefixWord ++ tailWord_3455268).sum := by decide
  have hdescent : baseEnd_3455268 < baseStart_3455268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455272 : List Nat := [2, 1, 5, 1, 4, 1, 1, 7]
def baseStart_3455272 : Nat := 118140960795 + 3455272 * 2 ^ 59
def prefixEnd_3455272 : Nat := 4983230072969 + 3 ^ 40 * 3455272 * 2
def baseEnd_3455272 : Nat := 131423357631267441934037

theorem tailTrace_3455272 : CollatzResearch.WordTrace tailWord_3455272 prefixEnd_3455272 131423357631267441934037 := by
  unfold tailWord_3455272
  simp only [CollatzResearch.WordTrace]
  refine ⟨63012061569073566160688035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84016082092098088214250713 63012061569073566160688035)
  ·
    refine ⟨94518092353610349241032053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63012061569073566160688035 94518092353610349241032053)
    ·
      refine ⟨8861071158150970241346755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94518092353610349241032053 8861071158150970241346755)
      ·
        refine ⟨13291606737226455362020133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861071158150970241346755 13291606737226455362020133)
        ·
          refine ⟨2492176263229960380378775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13291606737226455362020133 2492176263229960380378775)
          ·
            refine ⟨3738264394844940570568163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492176263229960380378775 3738264394844940570568163)
            ·
              refine ⟨5607396592267410855852245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738264394844940570568163 5607396592267410855852245)
              ·
                refine ⟨131423357631267441934037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5607396592267410855852245 131423357631267441934037)
                ·
                  rfl

theorem cell22_3455272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 7].length) (baseStart_3455272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455272 prefixEnd_3455272 := by exact prefixLift 3455272
  have htrace : WordTrace (prefixWord ++ tailWord_3455272) baseStart_3455272 baseEnd_3455272 := by
    simpa [prefixWord, tailWord_3455272, baseEnd_3455272] using wordTrace_append hprefix tailTrace_3455272
  have hstable : (prefixWord ++ tailWord_3455272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455272).length < 2 ^ (prefixWord ++ tailWord_3455272).sum := by decide
  have hdescent : baseEnd_3455272 < baseStart_3455272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455283 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 5]
def baseStart_3455283 : Nat := 118140960795 + 3455283 * 2 ^ 59
def prefixEnd_3455283 : Nat := 4983230072969 + 3 ^ 40 * 3455283 * 2
def baseEnd_3455283 : Nat := 394271328068735538460433

theorem tailTrace_3455283 : CollatzResearch.WordTrace tailWord_3455283 prefixEnd_3455283 394271328068735538460433 := by
  unfold tailWord_3455283
  simp only [CollatzResearch.WordTrace]
  refine ⟨126024524341107281200026503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84016349560738187466684335 126024524341107281200026503)
  ·
    refine ⟨189036786511660921800039755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126024524341107281200026503 189036786511660921800039755)
    ·
      refine ⟨283555179767491382700059633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189036786511660921800039755 283555179767491382700059633)
      ·
        refine ⟨212666384825618537025044725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283555179767491382700059633 212666384825618537025044725)
        ·
          refine ⟨19937473577401737846097943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212666384825618537025044725 19937473577401737846097943)
          ·
            refine ⟨29906210366102606769146915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19937473577401737846097943 29906210366102606769146915)
            ·
              refine ⟨44859315549153910153720373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29906210366102606769146915 44859315549153910153720373)
              ·
                refine ⟨4205560832733179076911285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44859315549153910153720373 4205560832733179076911285)
                ·
                  refine ⟨394271328068735538460433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205560832733179076911285 394271328068735538460433)
                  ·
                    rfl

theorem cell22_3455283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 5].length) (baseStart_3455283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455283 prefixEnd_3455283 := by exact prefixLift 3455283
  have htrace : WordTrace (prefixWord ++ tailWord_3455283) baseStart_3455283 baseEnd_3455283 := by
    simpa [prefixWord, tailWord_3455283, baseEnd_3455283] using wordTrace_append hprefix tailTrace_3455283
  have hstable : (prefixWord ++ tailWord_3455283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455283).length < 2 ^ (prefixWord ++ tailWord_3455283).sum := by decide
  have hdescent : baseEnd_3455283 < baseStart_3455283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455317 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 5]
def baseStart_3455317 : Nat := 118140960795 + 3455317 * 2 ^ 59
def prefixEnd_3455317 : Nat := 4983230072969 + 3 ^ 40 * 3455317 * 2
def baseEnd_3455317 : Nat := 394275207700347286677065

theorem tailTrace_3455317 : CollatzResearch.WordTrace tailWord_3455317 prefixEnd_3455317 394275207700347286677065 := by
  unfold tailWord_3455317
  simp only [CollatzResearch.WordTrace]
  refine ⟨126025764422984105006764205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84017176281989403337842803 126025764422984105006764205)
  ·
    refine ⟨47259661658619039377536577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126025764422984105006764205 47259661658619039377536577)
    ·
      refine ⟨35444746243964279533152433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47259661658619039377536577 35444746243964279533152433)
      ·
        refine ⟨26583559682973209649864325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35444746243964279533152433 26583559682973209649864325)
        ·
          refine ⟨4984417440557476809349561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26583559682973209649864325 4984417440557476809349561)
          ·
            refine ⟨3738313080418107607012171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984417440557476809349561 3738313080418107607012171)
            ·
              refine ⟨5607469620627161410518257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738313080418107607012171 5607469620627161410518257)
              ·
                refine ⟨4205602215470371057888693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607469620627161410518257 4205602215470371057888693)
                ·
                  refine ⟨394275207700347286677065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205602215470371057888693 394275207700347286677065)
                  ·
                    rfl

theorem cell22_3455317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_3455317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455317 prefixEnd_3455317 := by exact prefixLift 3455317
  have htrace : WordTrace (prefixWord ++ tailWord_3455317) baseStart_3455317 baseEnd_3455317 := by
    simpa [prefixWord, tailWord_3455317, baseEnd_3455317] using wordTrace_append hprefix tailTrace_3455317
  have hstable : (prefixWord ++ tailWord_3455317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455317).length < 2 ^ (prefixWord ++ tailWord_3455317).sum := by decide
  have hdescent : baseEnd_3455317 < baseStart_3455317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455343 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 1, 5]
def baseStart_3455343 : Nat := 118140960795 + 3455343 * 2 ^ 59
def prefixEnd_3455343 : Nat := 4983230072969 + 3 ^ 40 * 3455343 * 2
def baseEnd_3455343 : Nat := 1182834523432386458881115

theorem tailTrace_3455343 : CollatzResearch.WordTrace tailWord_3455343 prefixEnd_3455343 1182834523432386458881115 := by
  unfold tailWord_3455343
  simp only [CollatzResearch.WordTrace]
  refine ⟨126026712720889911447210683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84017808480593274298140455 126026712720889911447210683)
  ·
    refine ⟨189040069081334867170816025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126026712720889911447210683 189040069081334867170816025)
    ·
      refine ⟨141780051811001150378112019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189040069081334867170816025 141780051811001150378112019)
      ·
        refine ⟨212670077716501725567168029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141780051811001150378112019 212670077716501725567168029)
        ·
          refine ⟨79751279143688147087688011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212670077716501725567168029 79751279143688147087688011)
          ·
            refine ⟨119626918715532220631532017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79751279143688147087688011 119626918715532220631532017)
            ·
              refine ⟨89720189036649165473649013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119626918715532220631532017 89720189036649165473649013)
              ·
                refine ⟨8411267722185859263154595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89720189036649165473649013 8411267722185859263154595)
                ·
                  refine ⟨12616901583278788894731893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411267722185859263154595 12616901583278788894731893)
                  ·
                    refine ⟨1182834523432386458881115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12616901583278788894731893 1182834523432386458881115)
                    ·
                      rfl

theorem cell22_3455343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_3455343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455343 prefixEnd_3455343 := by exact prefixLift 3455343
  have htrace : WordTrace (prefixWord ++ tailWord_3455343) baseStart_3455343 baseEnd_3455343 := by
    simpa [prefixWord, tailWord_3455343, baseEnd_3455343] using wordTrace_append hprefix tailTrace_3455343
  have hstable : (prefixWord ++ tailWord_3455343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455343).length < 2 ^ (prefixWord ++ tailWord_3455343).sum := by decide
  have hdescent : baseEnd_3455343 < baseStart_3455343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455418 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_3455418 : Nat := 118140960795 + 3455418 * 2 ^ 59
def prefixEnd_3455418 : Nat := 4983230072969 + 3 ^ 40 * 3455418 * 2
def baseEnd_3455418 : Nat := 394286732488370421085295

theorem tailTrace_3455418 : CollatzResearch.WordTrace tailWord_3455418 prefixEnd_3455418 394286732488370421085295 := by
  unfold tailWord_3455418
  simp only [CollatzResearch.WordTrace]
  refine ⟨31507362048904549814047727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84019632130412132837460605 31507362048904549814047727)
  ·
    refine ⟨47261043073356824721071591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31507362048904549814047727 47261043073356824721071591)
    ·
      refine ⟨70891564610035237081607387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47261043073356824721071591 70891564610035237081607387)
      ·
        refine ⟨106337346915052855622411081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70891564610035237081607387 106337346915052855622411081)
        ·
          refine ⟨79753010186289641716808311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106337346915052855622411081 79753010186289641716808311)
          ·
            refine ⟨119629515279434462575212467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79753010186289641716808311 119629515279434462575212467)
            ·
              refine ⟨179444272919151693862818701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119629515279434462575212467 179444272919151693862818701)
              ·
                refine ⟨67291602344681885198557013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179444272919151693862818701 67291602344681885198557013)
                ·
                  refine ⟨394286732488370421085295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67291602344681885198557013 394286732488370421085295)
                  ·
                    rfl

theorem cell22_3455418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_3455418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455418 prefixEnd_3455418 := by exact prefixLift 3455418
  have htrace : WordTrace (prefixWord ++ tailWord_3455418) baseStart_3455418 baseEnd_3455418 := by
    simpa [prefixWord, tailWord_3455418, baseEnd_3455418] using wordTrace_append hprefix tailTrace_3455418
  have hstable : (prefixWord ++ tailWord_3455418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455418).length < 2 ^ (prefixWord ++ tailWord_3455418).sum := by decide
  have hdescent : baseEnd_3455418 < baseStart_3455418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455450 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_3455450 : Nat := 118140960795 + 3455450 * 2 ^ 59
def prefixEnd_3455450 : Nat := 4983230072969 + 3 ^ 40 * 3455450 * 2
def baseEnd_3455450 : Nat := 1182871151719073846455787

theorem tailTrace_3455450 : CollatzResearch.WordTrace tailWord_3455450 prefixEnd_3455450 1182871151719073846455787 := by
  unfold tailWord_3455450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31507653832875567180338951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84020410221001512480903869 31507653832875567180338951)
  ·
    refine ⟨47261480749313350770508427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31507653832875567180338951 47261480749313350770508427)
    ·
      refine ⟨70892221123970026155762641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47261480749313350770508427 70892221123970026155762641)
      ·
        refine ⟨53169165842977519616821981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70892221123970026155762641 53169165842977519616821981)
        ·
          refine ⟨19938437191116569856308243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53169165842977519616821981 19938437191116569856308243)
          ·
            refine ⟨29907655786674854784462365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19938437191116569856308243 29907655786674854784462365)
            ·
              refine ⟨11215370920003070544173387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29907655786674854784462365 11215370920003070544173387)
              ·
                refine ⟨16823056380004605816260081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11215370920003070544173387 16823056380004605816260081)
                ·
                  refine ⟨12617292285003454362195061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16823056380004605816260081 12617292285003454362195061)
                  ·
                    refine ⟨1182871151719073846455787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12617292285003454362195061 1182871151719073846455787)
                    ·
                      rfl

theorem cell22_3455450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_3455450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455450 prefixEnd_3455450 := by exact prefixLift 3455450
  have htrace : WordTrace (prefixWord ++ tailWord_3455450) baseStart_3455450 baseEnd_3455450 := by
    simpa [prefixWord, tailWord_3455450, baseEnd_3455450] using wordTrace_append hprefix tailTrace_3455450
  have hstable : (prefixWord ++ tailWord_3455450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455450).length < 2 ^ (prefixWord ++ tailWord_3455450).sum := by decide
  have hdescent : baseEnd_3455450 < baseStart_3455450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455512 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_3455512 : Nat := 118140960795 + 3455512 * 2 ^ 59
def prefixEnd_3455512 : Nat := 4983230072969 + 3 ^ 40 * 3455512 * 2
def baseEnd_3455512 : Nat := 1182892375586126351405597

theorem tailTrace_3455512 : CollatzResearch.WordTrace tailWord_3455512 prefixEnd_3455512 1182892375586126351405597 := by
  unfold tailWord_3455512
  simp only [CollatzResearch.WordTrace]
  refine ⟨63016438328638826655056395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84021917771518435540075193 63016438328638826655056395)
  ·
    refine ⟨94524657492958239982584593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63016438328638826655056395 94524657492958239982584593)
    ·
      refine ⟨70893493119718679986938445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94524657492958239982584593 70893493119718679986938445)
      ·
        refine ⟨26585059919894504995101917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70893493119718679986938445 26585059919894504995101917)
        ·
          refine ⟨9969397469960439373163219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26585059919894504995101917 9969397469960439373163219)
          ·
            refine ⟨14954096204940659059744829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9969397469960439373163219 14954096204940659059744829)
            ·
              refine ⟨5607786076852747147404311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14954096204940659059744829 5607786076852747147404311)
              ·
                refine ⟨8411679115279120721106467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5607786076852747147404311 8411679115279120721106467)
                ·
                  refine ⟨12617518672918681081659701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8411679115279120721106467 12617518672918681081659701)
                  ·
                    refine ⟨1182892375586126351405597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12617518672918681081659701 1182892375586126351405597)
                    ·
                      rfl

theorem cell22_3455512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_3455512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455512 prefixEnd_3455512 := by exact prefixLift 3455512
  have htrace : WordTrace (prefixWord ++ tailWord_3455512) baseStart_3455512 baseEnd_3455512 := by
    simpa [prefixWord, tailWord_3455512, baseEnd_3455512] using wordTrace_append hprefix tailTrace_3455512
  have hstable : (prefixWord ++ tailWord_3455512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455512).length < 2 ^ (prefixWord ++ tailWord_3455512).sum := by decide
  have hdescent : baseEnd_3455512 < baseStart_3455512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455542 : List Nat := [5, 1, 2, 1, 2, 1, 10]
def baseStart_3455542 : Nat := 118140960795 + 3455542 * 2 ^ 59
def prefixEnd_3455542 : Nat := 4983230072969 + 3 ^ 40 * 3455542 * 2
def baseEnd_3455542 : Nat := 43811209081452454561315

theorem tailTrace_3455542 : CollatzResearch.WordTrace tailWord_3455542 prefixEnd_3455542 43811209081452454561315 := by
  unfold tailWord_3455542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877123177948060527106555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84022647231445978955803253 7877123177948060527106555)
  ·
    refine ⟨11815684766922090790659833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7877123177948060527106555 11815684766922090790659833)
    ·
      refine ⟨8861763575191568092994875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11815684766922090790659833 8861763575191568092994875)
      ·
        refine ⟨13292645362787352139492313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861763575191568092994875 13292645362787352139492313)
        ·
          refine ⟨9969484022090514104619235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13292645362787352139492313 9969484022090514104619235)
          ·
            refine ⟨14954226033135771156928853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9969484022090514104619235 14954226033135771156928853)
            ·
              refine ⟨43811209081452454561315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14954226033135771156928853 43811209081452454561315)
              ·
                rfl

theorem cell22_3455542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 10].length) (baseStart_3455542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455542 prefixEnd_3455542 := by exact prefixLift 3455542
  have htrace : WordTrace (prefixWord ++ tailWord_3455542) baseStart_3455542 baseEnd_3455542 := by
    simpa [prefixWord, tailWord_3455542, baseEnd_3455542] using wordTrace_append hprefix tailTrace_3455542
  have hstable : (prefixWord ++ tailWord_3455542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455542).length < 2 ^ (prefixWord ++ tailWord_3455542).sum := by decide
  have hdescent : baseEnd_3455542 < baseStart_3455542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455617 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3455617 : Nat := 118140960795 + 3455617 * 2 ^ 59
def prefixEnd_3455617 : Nat := 4983230072969 + 3 ^ 40 * 3455617 * 2
def baseEnd_3455617 : Nat := 1182928319231941077530275

theorem tailTrace_3455617 : CollatzResearch.WordTrace tailWord_3455617 prefixEnd_3455617 1182928319231941077530275 := by
  unfold tailWord_3455617
  simp only [CollatzResearch.WordTrace]
  refine ⟨126036706321897256242685105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84024470881264837495123403 126036706321897256242685105)
  ·
    refine ⟨94527529741422942182013829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126036706321897256242685105 94527529741422942182013829)
    ·
      refine ⟨17723911826516801659127593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94527529741422942182013829 17723911826516801659127593)
      ·
        refine ⟨13292933869887601244345695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17723911826516801659127593 13292933869887601244345695)
        ·
          refine ⟨19939400804831401866518543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13292933869887601244345695 19939400804831401866518543)
          ·
            refine ⟨29909101207247102799777815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19939400804831401866518543 29909101207247102799777815)
            ·
              refine ⟨44863651810870654199666723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29909101207247102799777815 44863651810870654199666723)
              ·
                refine ⟨67295477716305981299500085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44863651810870654199666723 67295477716305981299500085)
                ·
                  refine ⟨6308951035903685746828133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67295477716305981299500085 6308951035903685746828133)
                  ·
                    refine ⟨1182928319231941077530275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6308951035903685746828133 1182928319231941077530275)
                    ·
                      rfl

theorem cell22_3455617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3455617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455617 prefixEnd_3455617 := by exact prefixLift 3455617
  have htrace : WordTrace (prefixWord ++ tailWord_3455617) baseStart_3455617 baseEnd_3455617 := by
    simpa [prefixWord, tailWord_3455617, baseEnd_3455617] using wordTrace_append hprefix tailTrace_3455617
  have hstable : (prefixWord ++ tailWord_3455617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455617).length < 2 ^ (prefixWord ++ tailWord_3455617).sum := by decide
  have hdescent : baseEnd_3455617 < baseStart_3455617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455634 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3455634 : Nat := 118140960795 + 3455634 * 2 ^ 59
def prefixEnd_3455634 : Nat := 4983230072969 + 3 ^ 40 * 3455634 * 2
def baseEnd_3455634 : Nat := 1182934138679358699855223

theorem tailTrace_3455634 : CollatzResearch.WordTrace tailWord_3455634 prefixEnd_3455634 1182934138679358699855223 := by
  unfold tailWord_3455634
  simp only [CollatzResearch.WordTrace]
  refine ⟨31509331590708917036513489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84024884241890445430702637 31509331590708917036513489)
  ·
    refine ⟨23631998693031687777385117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31509331590708917036513489 23631998693031687777385117)
    ·
      refine ⟨8861999509886882916519419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23631998693031687777385117 8861999509886882916519419)
      ·
        refine ⟨13292999264830324374779129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861999509886882916519419 13292999264830324374779129)
        ·
          refine ⟨9969749448622743281084347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13292999264830324374779129 9969749448622743281084347)
          ·
            refine ⟨14954624172934114921626521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9969749448622743281084347 14954624172934114921626521)
            ·
              refine ⟨11215968129700586191219891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14954624172934114921626521 11215968129700586191219891)
              ·
                refine ⟨16823952194550879286829837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11215968129700586191219891 16823952194550879286829837)
                ·
                  refine ⟨6308982072956579732561189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16823952194550879286829837 6308982072956579732561189)
                  ·
                    refine ⟨1182934138679358699855223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6308982072956579732561189 1182934138679358699855223)
                    ·
                      rfl

theorem cell22_3455634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3455634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455634 prefixEnd_3455634 := by exact prefixLift 3455634
  have htrace : WordTrace (prefixWord ++ tailWord_3455634) baseStart_3455634 baseEnd_3455634 := by
    simpa [prefixWord, tailWord_3455634, baseEnd_3455634] using wordTrace_append hprefix tailTrace_3455634
  have hstable : (prefixWord ++ tailWord_3455634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455634).length < 2 ^ (prefixWord ++ tailWord_3455634).sum := by decide
  have hdescent : baseEnd_3455634 < baseStart_3455634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455694 : List Nat := [4, 1, 1, 1, 3, 2, 4, 6]
def baseStart_3455694 : Nat := 118140960795 + 3455694 * 2 ^ 59
def prefixEnd_3455694 : Nat := 4983230072969 + 3 ^ 40 * 3455694 * 2
def baseEnd_3455694 : Nat := 131439408656170949261671

theorem tailTrace_3455694 : CollatzResearch.WordTrace tailWord_3455694 prefixEnd_3455694 131439408656170949261671 := by
  unfold tailWord_3455694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15754939342827287299154767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84026343161745532262158757 15754939342827287299154767)
  ·
    refine ⟨23632409014240930948732151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15754939342827287299154767 23632409014240930948732151)
    ·
      refine ⟨35448613521361396423098227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23632409014240930948732151 35448613521361396423098227)
      ·
        refine ⟨53172920282042094634647341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35448613521361396423098227 53172920282042094634647341)
        ·
          refine ⟨19939845105765785487992753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53172920282042094634647341 19939845105765785487992753)
          ·
            refine ⟨14954883829324339115994565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19939845105765785487992753 14954883829324339115994565)
            ·
              refine ⟨2804040717998313584248981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14954883829324339115994565 2804040717998313584248981)
              ·
                refine ⟨131439408656170949261671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2804040717998313584248981 131439408656170949261671)
                ·
                  rfl

theorem cell22_3455694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_3455694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455694 prefixEnd_3455694 := by exact prefixLift 3455694
  have htrace : WordTrace (prefixWord ++ tailWord_3455694) baseStart_3455694 baseEnd_3455694 := by
    simpa [prefixWord, tailWord_3455694, baseEnd_3455694] using wordTrace_append hprefix tailTrace_3455694
  have hstable : (prefixWord ++ tailWord_3455694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455694).length < 2 ^ (prefixWord ++ tailWord_3455694).sum := by decide
  have hdescent : baseEnd_3455694 < baseStart_3455694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455700 : List Nat := [2, 4, 1, 3, 3, 1, 1, 3, 4]
def baseStart_3455700 : Nat := 118140960795 + 3455700 * 2 ^ 59
def prefixEnd_3455700 : Nat := 4983230072969 + 3 ^ 40 * 3455700 * 2
def baseEnd_3455700 : Nat := 394318910609385509235007

theorem tailTrace_3455700 : CollatzResearch.WordTrace tailWord_3455700 prefixEnd_3455700 394318910609385509235007 := by
  unfold tailWord_3455700
  simp only [CollatzResearch.WordTrace]
  refine ⟨63019866790298280708978277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84026489053731040945304369 63019866790298280708978277)
  ·
    refine ⟨11816225023180927632933427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63019866790298280708978277 11816225023180927632933427)
    ·
      refine ⟨17724337534771391449400141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11816225023180927632933427 17724337534771391449400141)
      ·
        refine ⟨6646626575539271793525053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17724337534771391449400141 6646626575539271793525053)
        ·
          refine ⟨2492484965827226922571895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6646626575539271793525053 2492484965827226922571895)
          ·
            refine ⟨3738727448740840383857843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492484965827226922571895 3738727448740840383857843)
            ·
              refine ⟨5608091173111260575786765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738727448740840383857843 5608091173111260575786765)
              ·
                refine ⟨2103034189916722715920037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5608091173111260575786765 2103034189916722715920037)
                ·
                  refine ⟨394318910609385509235007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103034189916722715920037 394318910609385509235007)
                  ·
                    rfl

theorem cell22_3455700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_3455700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455700 prefixEnd_3455700 := by exact prefixLift 3455700
  have htrace : WordTrace (prefixWord ++ tailWord_3455700) baseStart_3455700 baseEnd_3455700 := by
    simpa [prefixWord, tailWord_3455700, baseEnd_3455700] using wordTrace_append hprefix tailTrace_3455700
  have hstable : (prefixWord ++ tailWord_3455700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455700).length < 2 ^ (prefixWord ++ tailWord_3455700).sum := by decide
  have hdescent : baseEnd_3455700 < baseStart_3455700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455726 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3455726 : Nat := 118140960795 + 3455726 * 2 ^ 59
def prefixEnd_3455726 : Nat := 4983230072969 + 3 ^ 40 * 3455726 * 2
def baseEnd_3455726 : Nat := 1182965632159501126554941

theorem tailTrace_3455726 : CollatzResearch.WordTrace tailWord_3455726 prefixEnd_3455726 1182965632159501126554941 := by
  unfold tailWord_3455726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15755085234812795982300379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84027121252334911905602021 15755085234812795982300379)
  ·
    refine ⟨23632627852219193973450569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15755085234812795982300379 23632627852219193973450569)
    ·
      refine ⟨17724470889164395480087927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23632627852219193973450569 17724470889164395480087927)
      ·
        refine ⟨26586706333746593220131891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17724470889164395480087927 26586706333746593220131891)
        ·
          refine ⟨39880059500619889830197837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26586706333746593220131891 39880059500619889830197837)
          ·
            refine ⟨14955022312732458686324189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39880059500619889830197837 14955022312732458686324189)
            ·
              refine ⟨5608133367274672007371571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14955022312732458686324189 5608133367274672007371571)
              ·
                refine ⟨8412200050912008011057357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608133367274672007371571 8412200050912008011057357)
                ·
                  refine ⟨3154575019092003004146509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8412200050912008011057357 3154575019092003004146509)
                  ·
                    refine ⟨1182965632159501126554941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3154575019092003004146509 1182965632159501126554941)
                    ·
                      rfl

theorem cell22_3455726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3455726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455726 prefixEnd_3455726 := by exact prefixLift 3455726
  have htrace : WordTrace (prefixWord ++ tailWord_3455726) baseStart_3455726 baseEnd_3455726 := by
    simpa [prefixWord, tailWord_3455726, baseEnd_3455726] using wordTrace_append hprefix tailTrace_3455726
  have hstable : (prefixWord ++ tailWord_3455726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455726).length < 2 ^ (prefixWord ++ tailWord_3455726).sum := by decide
  have hdescent : baseEnd_3455726 < baseStart_3455726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455737 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_3455737 : Nat := 118140960795 + 3455737 * 2 ^ 59
def prefixEnd_3455737 : Nat := 4983230072969 + 3 ^ 40 * 3455737 * 2
def baseEnd_3455737 : Nat := 1182969397684300764529907

theorem tailTrace_3455737 : CollatzResearch.WordTrace tailWord_3455737 prefixEnd_3455737 1182969397684300764529907 := by
  unfold tailWord_3455737
  simp only [CollatzResearch.WordTrace]
  refine ⟨126041083081462516737053465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84027388720975011158035643 126041083081462516737053465)
  ·
    refine ⟨94530812311096887552790099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126041083081462516737053465 94530812311096887552790099)
    ·
      refine ⟨141796218466645331329185149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94530812311096887552790099 141796218466645331329185149)
      ·
        refine ⟨53173581924991999248444431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141796218466645331329185149 53173581924991999248444431)
        ·
          refine ⟨79760372887487998872666647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53173581924991999248444431 79760372887487998872666647)
          ·
            refine ⟨119640559331231998308999971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79760372887487998872666647 119640559331231998308999971)
            ·
              refine ⟨179460838996847997463499957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119640559331231998308999971 179460838996847997463499957)
              ·
                refine ⟨16824453655954499762203121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179460838996847997463499957 16824453655954499762203121)
                ·
                  refine ⟨12618340241965874821652341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16824453655954499762203121 12618340241965874821652341)
                  ·
                    refine ⟨1182969397684300764529907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12618340241965874821652341 1182969397684300764529907)
                    ·
                      rfl

theorem cell22_3455737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_3455737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455737 prefixEnd_3455737 := by exact prefixLift 3455737
  have htrace : WordTrace (prefixWord ++ tailWord_3455737) baseStart_3455737 baseEnd_3455737 := by
    simpa [prefixWord, tailWord_3455737, baseEnd_3455737] using wordTrace_append hprefix tailTrace_3455737
  have hstable : (prefixWord ++ tailWord_3455737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455737).length < 2 ^ (prefixWord ++ tailWord_3455737).sum := by decide
  have hdescent : baseEnd_3455737 < baseStart_3455737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455773 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 5]
def baseStart_3455773 : Nat := 118140960795 + 3455773 * 2 ^ 59
def prefixEnd_3455773 : Nat := 4983230072969 + 3 ^ 40 * 3455773 * 2
def baseEnd_3455773 : Nat := 394327240406669556876599

theorem tailTrace_3455773 : CollatzResearch.WordTrace tailWord_3455773 prefixEnd_3455773 394327240406669556876599 := by
  unfold tailWord_3455773
  simp only [CollatzResearch.WordTrace]
  refine ⟨126042396109332094885363973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84028264072888063256909315 126042396109332094885363973)
  ·
    refine ⟨23632949270499767791005745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126042396109332094885363973 23632949270499767791005745)
    ·
      refine ⟨17724711952874825843254309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23632949270499767791005745 17724711952874825843254309)
      ·
        refine ⟨3323383491164029845610183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17724711952874825843254309 3323383491164029845610183)
        ·
          refine ⟨4985075236746044768415275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323383491164029845610183 4985075236746044768415275)
          ·
            refine ⟨7477612855119067152622913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985075236746044768415275 7477612855119067152622913)
            ·
              refine ⟨5608209641339300364467185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7477612855119067152622913 5608209641339300364467185)
              ·
                refine ⟨4206157231004475273350389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608209641339300364467185 4206157231004475273350389)
                ·
                  refine ⟨394327240406669556876599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4206157231004475273350389 394327240406669556876599)
                  ·
                    rfl

theorem cell22_3455773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_3455773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455773 prefixEnd_3455773 := by exact prefixLift 3455773
  have htrace : WordTrace (prefixWord ++ tailWord_3455773) baseStart_3455773 baseEnd_3455773 := by
    simpa [prefixWord, tailWord_3455773, baseEnd_3455773] using wordTrace_append hprefix tailTrace_3455773
  have hstable : (prefixWord ++ tailWord_3455773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455773).length < 2 ^ (prefixWord ++ tailWord_3455773).sum := by decide
  have hdescent : baseEnd_3455773 < baseStart_3455773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455784 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 6]
def baseStart_3455784 : Nat := 118140960795 + 3455784 * 2 ^ 59
def prefixEnd_3455784 : Nat := 4983230072969 + 3 ^ 40 * 3455784 * 2
def baseEnd_3455784 : Nat := 394328495581602769534921

theorem tailTrace_3455784 : CollatzResearch.WordTrace tailWord_3455784 prefixEnd_3455784 394328495581602769534921 := by
  unfold tailWord_3455784
  simp only [CollatzResearch.WordTrace]
  refine ⟨63021398656146121882007203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84028531541528162509342937 63021398656146121882007203)
  ·
    refine ⟨94532097984219182823010805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63021398656146121882007203 94532097984219182823010805)
    ·
      refine ⟨8862384186020548389657263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94532097984219182823010805 8862384186020548389657263)
      ·
        refine ⟨13293576279030822584485895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8862384186020548389657263 13293576279030822584485895)
        ·
          refine ⟨19940364418546233876728843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13293576279030822584485895 19940364418546233876728843)
          ·
            refine ⟨29910546627819350815093265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19940364418546233876728843 29910546627819350815093265)
            ·
              refine ⟨22432909970864513111319949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29910546627819350815093265 22432909970864513111319949)
              ·
                refine ⟨8412341239074192416744981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22432909970864513111319949 8412341239074192416744981)
                ·
                  refine ⟨394328495581602769534921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8412341239074192416744981 394328495581602769534921)
                  ·
                    rfl

theorem cell22_3455784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_3455784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455784 prefixEnd_3455784 := by exact prefixLift 3455784
  have htrace : WordTrace (prefixWord ++ tailWord_3455784) baseStart_3455784 baseEnd_3455784 := by
    simpa [prefixWord, tailWord_3455784, baseEnd_3455784] using wordTrace_append hprefix tailTrace_3455784
  have hstable : (prefixWord ++ tailWord_3455784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455784).length < 2 ^ (prefixWord ++ tailWord_3455784).sum := by decide
  have hdescent : baseEnd_3455784 < baseStart_3455784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455799 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 1, 5]
def baseStart_3455799 : Nat := 118140960795 + 3455799 * 2 ^ 59
def prefixEnd_3455799 : Nat := 4983230072969 + 3 ^ 40 * 3455799 * 2
def baseEnd_3455799 : Nat := 1182990621551353269479717

theorem tailTrace_3455799 : CollatzResearch.WordTrace tailWord_3455799 prefixEnd_3455799 1182990621551353269479717 := by
  unfold tailWord_3455799
  simp only [CollatzResearch.WordTrace]
  refine ⟨126043344407237901325810451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84028896271491934217206967 126043344407237901325810451)
  ·
    refine ⟨189065016610856851988715677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126043344407237901325810451 189065016610856851988715677)
    ·
      refine ⟨70899381229071319495768379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189065016610856851988715677 70899381229071319495768379)
      ·
        refine ⟨106349071843606979243652569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70899381229071319495768379 106349071843606979243652569)
        ·
          refine ⟨79761803882705234432739427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106349071843606979243652569 79761803882705234432739427)
          ·
            refine ⟨119642705824057851649109141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79761803882705234432739427 119642705824057851649109141)
            ·
              refine ⟨5608251835502711796051991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119642705824057851649109141 5608251835502711796051991)
              ·
                refine ⟨8412377753254067694077987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608251835502711796051991 8412377753254067694077987)
                ·
                  refine ⟨12618566629881101541116981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8412377753254067694077987 12618566629881101541116981)
                  ·
                    refine ⟨1182990621551353269479717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12618566629881101541116981 1182990621551353269479717)
                    ·
                      rfl

theorem cell22_3455799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_3455799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455799 prefixEnd_3455799 := by exact prefixLift 3455799
  have htrace : WordTrace (prefixWord ++ tailWord_3455799) baseStart_3455799 baseEnd_3455799 := by
    simpa [prefixWord, tailWord_3455799, baseEnd_3455799] using wordTrace_append hprefix tailTrace_3455799
  have hstable : (prefixWord ++ tailWord_3455799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455799).length < 2 ^ (prefixWord ++ tailWord_3455799).sum := by decide
  have hdescent : baseEnd_3455799 < baseStart_3455799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455827 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 9]
def baseStart_3455827 : Nat := 118140960795 + 3455827 * 2 ^ 59
def prefixEnd_3455827 : Nat := 4983230072969 + 3 ^ 40 * 3455827 * 2
def baseEnd_3455827 : Nat := 1183000206523570529779631

theorem tailTrace_3455827 : CollatzResearch.WordTrace tailWord_3455827 prefixEnd_3455827 1183000206523570529779631 := by
  unfold tailWord_3455827
  simp only [CollatzResearch.WordTrace]
  refine ⟨126044365651136462107829735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84029577100757641405219823 126044365651136462107829735)
  ·
    refine ⟨189066548476704693161744603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126044365651136462107829735 189066548476704693161744603)
    ·
      refine ⟨283599822715057039742616905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189066548476704693161744603 283599822715057039742616905)
      ·
        refine ⟨212699867036292779806962679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283599822715057039742616905 212699867036292779806962679)
        ·
          refine ⟨319049800554439169710444019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212699867036292779806962679 319049800554439169710444019)
          ·
            refine ⟨478574700831658754565666029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319049800554439169710444019 478574700831658754565666029)
            ·
              refine ⟨179465512811872032962124761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478574700831658754565666029 179465512811872032962124761)
              ·
                refine ⟨134599134608904024721593571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179465512811872032962124761 134599134608904024721593571)
                ·
                  refine ⟨201898701913356037082390357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134599134608904024721593571 201898701913356037082390357)
                  ·
                    refine ⟨1183000206523570529779631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 201898701913356037082390357 1183000206523570529779631)
                    ·
                      rfl

theorem cell22_3455827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_3455827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455827 prefixEnd_3455827 := by exact prefixLift 3455827
  have htrace : WordTrace (prefixWord ++ tailWord_3455827) baseStart_3455827 baseEnd_3455827 := by
    simpa [prefixWord, tailWord_3455827, baseEnd_3455827] using wordTrace_append hprefix tailTrace_3455827
  have hstable : (prefixWord ++ tailWord_3455827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455827).length < 2 ^ (prefixWord ++ tailWord_3455827).sum := by decide
  have hdescent : baseEnd_3455827 < baseStart_3455827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455833 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 2, 3]
def baseStart_3455833 : Nat := 118140960795 + 3455833 * 2 ^ 59
def prefixEnd_3455833 : Nat := 4983230072969 + 3 ^ 40 * 3455833 * 2
def baseEnd_3455833 : Nat := 1183002260446188514129613

theorem tailTrace_3455833 : CollatzResearch.WordTrace tailWord_3455833 prefixEnd_3455833 1183002260446188514129613 := by
  unfold tailWord_3455833
  simp only [CollatzResearch.WordTrace]
  refine ⟨126044584489114725132548153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84029722992743150088365435 126044584489114725132548153)
  ·
    refine ⟨94533438366836043849411115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126044584489114725132548153 94533438366836043849411115)
    ·
      refine ⟨141800157550254065774116673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94533438366836043849411115 141800157550254065774116673)
      ·
        refine ⟨106350118162690549330587505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141800157550254065774116673 106350118162690549330587505)
        ·
          refine ⟨79762588622017911997940629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106350118162690549330587505 79762588622017911997940629)
          ·
            refine ⟨3738871341657089624903467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79762588622017911997940629 3738871341657089624903467)
            ·
              refine ⟨5608307012485634437355201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738871341657089624903467 5608307012485634437355201)
              ·
                refine ⟨4206230259364225828016401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5608307012485634437355201 4206230259364225828016401)
                ·
                  refine ⟨3154672694523169371012301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4206230259364225828016401 3154672694523169371012301)
                  ·
                    refine ⟨1183002260446188514129613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3154672694523169371012301 1183002260446188514129613)
                    ·
                      rfl

theorem cell22_3455833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_3455833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455833 prefixEnd_3455833 := by exact prefixLift 3455833
  have htrace : WordTrace (prefixWord ++ tailWord_3455833) baseStart_3455833 baseEnd_3455833 := by
    simpa [prefixWord, tailWord_3455833, baseEnd_3455833] using wordTrace_append hprefix tailTrace_3455833
  have hstable : (prefixWord ++ tailWord_3455833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455833).length < 2 ^ (prefixWord ++ tailWord_3455833).sum := by decide
  have hdescent : baseEnd_3455833 < baseStart_3455833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455895 : List Nat := [1, 1, 3, 3, 1, 2, 5, 2, 1, 3]
def baseStart_3455895 : Nat := 118140960795 + 3455895 * 2 ^ 59
def prefixEnd_3455895 : Nat := 4983230072969 + 3 ^ 40 * 3455895 * 2
def baseEnd_3455895 : Nat := 1183023484313241019079423

theorem tailTrace_3455895 : CollatzResearch.WordTrace tailWord_3455895 prefixEnd_3455895 1183023484313241019079423 := by
  unfold tailWord_3455895
  simp only [CollatzResearch.WordTrace]
  refine ⟨126046845814890109721305139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84031230543260073147536759 126046845814890109721305139)
  ·
    refine ⟨189070268722335164581957709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126046845814890109721305139 189070268722335164581957709)
    ·
      refine ⟨70901350770875686718234141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189070268722335164581957709 70901350770875686718234141)
      ·
        refine ⟨26588006539078382519337803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70901350770875686718234141 26588006539078382519337803)
        ·
          refine ⟨39882009808617573779006705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26588006539078382519337803 39882009808617573779006705)
          ·
            refine ⟨29911507356463180334255029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39882009808617573779006705 29911507356463180334255029)
            ·
              refine ⟨2804203814668423156336409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29911507356463180334255029 2804203814668423156336409)
              ·
                refine ⟨2103152861001317367252307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804203814668423156336409 2103152861001317367252307)
                ·
                  refine ⟨3154729291501976050878461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103152861001317367252307 3154729291501976050878461)
                  ·
                    refine ⟨1183023484313241019079423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3154729291501976050878461 1183023484313241019079423)
                    ·
                      rfl

theorem cell22_3455895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_3455895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455895 prefixEnd_3455895 := by exact prefixLift 3455895
  have htrace : WordTrace (prefixWord ++ tailWord_3455895) baseStart_3455895 baseEnd_3455895 := by
    simpa [prefixWord, tailWord_3455895, baseEnd_3455895] using wordTrace_append hprefix tailTrace_3455895
  have hstable : (prefixWord ++ tailWord_3455895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455895).length < 2 ^ (prefixWord ++ tailWord_3455895).sum := by decide
  have hdescent : baseEnd_3455895 < baseStart_3455895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455983 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 2, 4]
def baseStart_3455983 : Nat := 118140960795 + 3455983 * 2 ^ 59
def prefixEnd_3455983 : Nat := 4983230072969 + 3 ^ 40 * 3455983 * 2
def baseEnd_3455983 : Nat := 1183053608511638122879153

theorem tailTrace_3455983 : CollatzResearch.WordTrace tailWord_3455983 prefixEnd_3455983 1183053608511638122879153 := by
  unfold tailWord_3455983
  simp only [CollatzResearch.WordTrace]
  refine ⟨126050055438571300750508603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84033370292380867167005735 126050055438571300750508603)
  ·
    refine ⟨189075083157856951125762905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126050055438571300750508603 189075083157856951125762905)
    ·
      refine ⟨141806312368392713344322179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189075083157856951125762905 141806312368392713344322179)
      ·
        refine ⟨212709468552589070016483269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141806312368392713344322179 212709468552589070016483269)
        ·
          refine ⟨39883025353610450628090613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212709468552589070016483269 39883025353610450628090613)
          ·
            refine ⟨3739033626900979746383495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39883025353610450628090613 3739033626900979746383495)
            ·
              refine ⟨5608550440351469619575243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739033626900979746383495 5608550440351469619575243)
              ·
                refine ⟨8412825660527204429362865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5608550440351469619575243 8412825660527204429362865)
                ·
                  refine ⟨6309619245395403322022149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8412825660527204429362865 6309619245395403322022149)
                  ·
                    refine ⟨1183053608511638122879153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6309619245395403322022149 1183053608511638122879153)
                    ·
                      rfl

theorem cell22_3455983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_3455983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455983 prefixEnd_3455983 := by exact prefixLift 3455983
  have htrace : WordTrace (prefixWord ++ tailWord_3455983) baseStart_3455983 baseEnd_3455983 := by
    simpa [prefixWord, tailWord_3455983, baseEnd_3455983] using wordTrace_append hprefix tailTrace_3455983
  have hstable : (prefixWord ++ tailWord_3455983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455983).length < 2 ^ (prefixWord ++ tailWord_3455983).sum := by decide
  have hdescent : baseEnd_3455983 < baseStart_3455983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455989 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3455989 : Nat := 118140960795 + 3455989 * 2 ^ 59
def prefixEnd_3455989 : Nat := 4983230072969 + 3 ^ 40 * 3455989 * 2
def baseEnd_3455989 : Nat := 1183055662434256107229135

theorem tailTrace_3455989 : CollatzResearch.WordTrace tailWord_3455989 prefixEnd_3455989 1183055662434256107229135 := by
  unfold tailWord_3455989
  simp only [CollatzResearch.WordTrace]
  refine ⟨126050274276549563775227021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84033516184366375850151347 126050274276549563775227021)
  ·
    refine ⟨47268852853706086415710133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126050274276549563775227021 47268852853706086415710133)
    ·
      refine ⟨4431454955034945601472825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47268852853706086415710133 4431454955034945601472825)
      ·
        refine ⟨3323591216276209201104619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4431454955034945601472825 3323591216276209201104619)
        ·
          refine ⟨4985386824414313801656929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323591216276209201104619 4985386824414313801656929)
          ·
            refine ⟨3739040118310735351242697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4985386824414313801656929 3739040118310735351242697)
            ·
              refine ⟨2804280088733051513432023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739040118310735351242697 2804280088733051513432023)
              ·
                refine ⟨4206420133099577270148035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804280088733051513432023 4206420133099577270148035)
                ·
                  refine ⟨6309630199649365905222053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206420133099577270148035 6309630199649365905222053)
                  ·
                    refine ⟨1183055662434256107229135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6309630199649365905222053 1183055662434256107229135)
                    ·
                      rfl

theorem cell22_3455989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3455989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455989 prefixEnd_3455989 := by exact prefixLift 3455989
  have htrace : WordTrace (prefixWord ++ tailWord_3455989) baseStart_3455989 baseEnd_3455989 := by
    simpa [prefixWord, tailWord_3455989, baseEnd_3455989] using wordTrace_append hprefix tailTrace_3455989
  have hstable : (prefixWord ++ tailWord_3455989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455989).length < 2 ^ (prefixWord ++ tailWord_3455989).sum := by decide
  have hdescent : baseEnd_3455989 < baseStart_3455989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3455998 : List Nat := [4, 2, 2, 2, 2, 1, 9]
def baseStart_3455998 : Nat := 118140960795 + 3455998 * 2 ^ 59
def prefixEnd_3455998 : Nat := 4983230072969 + 3 ^ 40 * 3455998 * 2
def baseEnd_3455998 : Nat := 43816990493266040139041

theorem tailTrace_3455998 : CollatzResearch.WordTrace tailWord_3455998 prefixEnd_3455998 43816990493266040139041 := by
  unfold tailWord_3455998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15756325316689619789038081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84033735022344638874869765 15756325316689619789038081)
  ·
    refine ⟨11817243987517214841778561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15756325316689619789038081 11817243987517214841778561)
    ·
      refine ⟨8862932990637911131333921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11817243987517214841778561 8862932990637911131333921)
      ·
        refine ⟨6647199742978433348500441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8862932990637911131333921 6647199742978433348500441)
        ·
          refine ⟨4985399807233825011375331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6647199742978433348500441 4985399807233825011375331)
          ·
            refine ⟨7478099710850737517062997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985399807233825011375331 7478099710850737517062997)
            ·
              refine ⟨43816990493266040139041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7478099710850737517062997 43816990493266040139041)
              ·
                rfl

theorem cell22_3455998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 9].length) (baseStart_3455998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3455998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3455998 prefixEnd_3455998 := by exact prefixLift 3455998
  have htrace : WordTrace (prefixWord ++ tailWord_3455998) baseStart_3455998 baseEnd_3455998 := by
    simpa [prefixWord, tailWord_3455998, baseEnd_3455998] using wordTrace_append hprefix tailTrace_3455998
  have hstable : (prefixWord ++ tailWord_3455998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3455998).length < 2 ^ (prefixWord ++ tailWord_3455998).sum := by decide
  have hdescent : baseEnd_3455998 < baseStart_3455998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3455998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456002 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3456002 : Nat := 118140960795 + 3456002 * 2 ^ 59
def prefixEnd_3456002 : Nat := 4983230072969 + 3 ^ 40 * 3456002 * 2
def baseEnd_3456002 : Nat := 1183060112599928406654095

theorem tailTrace_3456002 : CollatzResearch.WordTrace tailWord_3456002 prefixEnd_3456002 1183060112599928406654095 := by
  unfold tailWord_3456002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31512687106375616748862565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84033832283668311330300173 31512687106375616748862565)
  ·
    refine ⟨5908628832445428140411731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31512687106375616748862565 5908628832445428140411731)
    ·
      refine ⟨8862943248668142210617597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908628832445428140411731 8862943248668142210617597)
      ·
        refine ⟨3323603718250553328981599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8862943248668142210617597 3323603718250553328981599)
        ·
          refine ⟨4985405577375829993472399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323603718250553328981599 4985405577375829993472399)
          ·
            refine ⟨7478108366063744990208599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985405577375829993472399 7478108366063744990208599)
            ·
              refine ⟨11217162549095617485312899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7478108366063744990208599 11217162549095617485312899)
              ·
                refine ⟨16825743823643426227969349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11217162549095617485312899 16825743823643426227969349)
                ·
                  refine ⟨3154826966933142417744253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16825743823643426227969349 3154826966933142417744253)
                  ·
                    refine ⟨1183060112599928406654095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3154826966933142417744253 1183060112599928406654095)
                    ·
                      rfl

theorem cell22_3456002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3456002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456002 prefixEnd_3456002 := by exact prefixLift 3456002
  have htrace : WordTrace (prefixWord ++ tailWord_3456002) baseStart_3456002 baseEnd_3456002 := by
    simpa [prefixWord, tailWord_3456002, baseEnd_3456002] using wordTrace_append hprefix tailTrace_3456002
  have hstable : (prefixWord ++ tailWord_3456002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456002).length < 2 ^ (prefixWord ++ tailWord_3456002).sum := by decide
  have hdescent : baseEnd_3456002 < baseStart_3456002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456032 : List Nat := [2, 1, 1, 7, 2, 1, 2, 6]
def baseStart_3456032 : Nat := 118140960795 + 3456032 * 2 ^ 59
def prefixEnd_3456032 : Nat := 4983230072969 + 3 ^ 40 * 3456032 * 2
def baseEnd_3456032 : Nat := 131452264690335369822667

theorem tailTrace_3456032 : CollatzResearch.WordTrace tailWord_3456032 prefixEnd_3456032 131452264690335369822667 := by
  unfold tailWord_3456032
  simp only [CollatzResearch.WordTrace]
  refine ⟨63025921307696891059521175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84034561743595854746028233 63025921307696891059521175)
  ·
    refine ⟨94538881961545336589281763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63025921307696891059521175 94538881961545336589281763)
    ·
      refine ⟨141808322942318004883922645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94538881961545336589281763 141808322942318004883922645)
      ·
        refine ⟨3323632568960578239466937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 141808322942318004883922645 3323632568960578239466937)
        ·
          refine ⟨2492724426720433679600203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3323632568960578239466937 2492724426720433679600203)
          ·
            refine ⟨3739086640080650519400305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492724426720433679600203 3739086640080650519400305)
            ·
              refine ⟨2804314980060487889550229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739086640080650519400305 2804314980060487889550229)
              ·
                refine ⟨131452264690335369822667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2804314980060487889550229 131452264690335369822667)
                ·
                  rfl

theorem cell22_3456032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 6].length) (baseStart_3456032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456032 prefixEnd_3456032 := by exact prefixLift 3456032
  have htrace : WordTrace (prefixWord ++ tailWord_3456032) baseStart_3456032 baseEnd_3456032 := by
    simpa [prefixWord, tailWord_3456032, baseEnd_3456032] using wordTrace_append hprefix tailTrace_3456032
  have hstable : (prefixWord ++ tailWord_3456032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456032).length < 2 ^ (prefixWord ++ tailWord_3456032).sum := by decide
  have hdescent : baseEnd_3456032 < baseStart_3456032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456077 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3456077 : Nat := 118140960795 + 3456077 * 2 ^ 59
def prefixEnd_3456077 : Nat := 4983230072969 + 3 ^ 40 * 3456077 * 2
def baseEnd_3456077 : Nat := 394361928877551070342955

theorem tailTrace_3456077 : CollatzResearch.WordTrace tailWord_3456077 prefixEnd_3456077 394361928877551070342955 := by
  unfold tailWord_3456077
  simp only [CollatzResearch.WordTrace]
  refine ⟨126053483900230754804430485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84035655933487169869620323 126053483900230754804430485)
  ·
    refine ⟨5908757057823316631457679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126053483900230754804430485 5908757057823316631457679)
    ·
      refine ⟨8863135586734974947186519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908757057823316631457679 8863135586734974947186519)
      ·
        refine ⟨13294703380102462420779779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863135586734974947186519 13294703380102462420779779)
        ·
          refine ⟨19942055070153693631169669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13294703380102462420779779 19942055070153693631169669)
          ·
            refine ⟨3739135325653817555844313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19942055070153693631169669 3739135325653817555844313)
            ·
              refine ⟨2804351494240363166883235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739135325653817555844313 2804351494240363166883235)
              ·
                refine ⟨4206527241360544750324853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804351494240363166883235 4206527241360544750324853)
                ·
                  refine ⟨394361928877551070342955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4206527241360544750324853 394361928877551070342955)
                  ·
                    rfl

theorem cell22_3456077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3456077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456077 prefixEnd_3456077 := by exact prefixLift 3456077
  have htrace : WordTrace (prefixWord ++ tailWord_3456077) baseStart_3456077 baseEnd_3456077 := by
    simpa [prefixWord, tailWord_3456077, baseEnd_3456077] using wordTrace_append hprefix tailTrace_3456077
  have hstable : (prefixWord ++ tailWord_3456077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456077).length < 2 ^ (prefixWord ++ tailWord_3456077).sum := by decide
  have hdescent : baseEnd_3456077 < baseStart_3456077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456103 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3456103 : Nat := 118140960795 + 3456103 * 2 ^ 59
def prefixEnd_3456103 : Nat := 4983230072969 + 3 ^ 40 * 3456103 * 2
def baseEnd_3456103 : Nat := 1183094686963997809878785

theorem tailTrace_3456103 : CollatzResearch.WordTrace tailWord_3456103 prefixEnd_3456103 1183094686963997809878785 := by
  unfold tailWord_3456103
  simp only [CollatzResearch.WordTrace]
  refine ⟨126054432198136561244876963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84036288132091040829917975 126054432198136561244876963)
  ·
    refine ⟨189081648297204841867315445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126054432198136561244876963 189081648297204841867315445)
    ·
      refine ⟨17726404527862953925060823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189081648297204841867315445 17726404527862953925060823)
      ·
        refine ⟨26589606791794430887591235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17726404527862953925060823 26589606791794430887591235)
        ·
          refine ⟨39884410187691646331386853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26589606791794430887591235 39884410187691646331386853)
          ·
            refine ⟨7478326910192183687135035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39884410187691646331386853 7478326910192183687135035)
            ·
              refine ⟨11217490365288275530702553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7478326910192183687135035 11217490365288275530702553)
              ·
                refine ⟨8413117773966206648026915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11217490365288275530702553 8413117773966206648026915)
                ·
                  refine ⟨12619676660949309972040373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8413117773966206648026915 12619676660949309972040373)
                  ·
                    refine ⟨1183094686963997809878785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12619676660949309972040373 1183094686963997809878785)
                    ·
                      rfl

theorem cell22_3456103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3456103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456103 prefixEnd_3456103 := by exact prefixLift 3456103
  have htrace : WordTrace (prefixWord ++ tailWord_3456103) baseStart_3456103 baseEnd_3456103 := by
    simpa [prefixWord, tailWord_3456103, baseEnd_3456103] using wordTrace_append hprefix tailTrace_3456103
  have hstable : (prefixWord ++ tailWord_3456103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456103).length < 2 ^ (prefixWord ++ tailWord_3456103).sum := by decide
  have hdescent : baseEnd_3456103 < baseStart_3456103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456176 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_3456176 : Nat := 118140960795 + 3456176 * 2 ^ 59
def prefixEnd_3456176 : Nat := 4983230072969 + 3 ^ 40 * 3456176 * 2
def baseEnd_3456176 : Nat := 1183119676355849952803561

theorem tailTrace_3456176 : CollatzResearch.WordTrace tailWord_3456176 prefixEnd_3456176 1183119676355849952803561 := by
  unfold tailWord_3456176
  simp only [CollatzResearch.WordTrace]
  refine ⟨63028547363436047356142191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84038063151248063141522921 63028547363436047356142191)
  ·
    refine ⟨94542821045154071034213287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63028547363436047356142191 94542821045154071034213287)
    ·
      refine ⟨141814231567731106551319931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94542821045154071034213287 141814231567731106551319931)
      ·
        refine ⟨212721347351596659826979897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141814231567731106551319931 212721347351596659826979897)
        ·
          refine ⟨159541010513697494870234923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212721347351596659826979897 159541010513697494870234923)
          ·
            refine ⟨239311515770546242305352385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159541010513697494870234923 239311515770546242305352385)
            ·
              refine ⟨179483636827909681729014289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239311515770546242305352385 179483636827909681729014289)
              ·
                refine ⟨134612727620932261296760717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179483636827909681729014289 134612727620932261296760717)
                ·
                  refine ⟨50479772857849597986285269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134612727620932261296760717 50479772857849597986285269)
                  ·
                    refine ⟨1183119676355849952803561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50479772857849597986285269 1183119676355849952803561)
                    ·
                      rfl

theorem cell22_3456176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_3456176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456176 prefixEnd_3456176 := by exact prefixLift 3456176
  have htrace : WordTrace (prefixWord ++ tailWord_3456176) baseStart_3456176 baseEnd_3456176 := by
    simpa [prefixWord, tailWord_3456176, baseEnd_3456176] using wordTrace_append hprefix tailTrace_3456176
  have hstable : (prefixWord ++ tailWord_3456176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456176).length < 2 ^ (prefixWord ++ tailWord_3456176).sum := by decide
  have hdescent : baseEnd_3456176 < baseStart_3456176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456178 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3456178 : Nat := 118140960795 + 3456178 * 2 ^ 59
def prefixEnd_3456178 : Nat := 4983230072969 + 3 ^ 40 * 3456178 * 2
def baseEnd_3456178 : Nat := 394373453665574204751185

theorem tailTrace_3456178 : CollatzResearch.WordTrace tailWord_3456178 prefixEnd_3456178 394373453665574204751185 := by
  unfold tailWord_3456178
  simp only [CollatzResearch.WordTrace]
  refine ⟨31514291918216212263464297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84038111781909899369238125 31514291918216212263464297)
  ·
    refine ⟨23635718938662159197598223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31514291918216212263464297 23635718938662159197598223)
    ·
      refine ⟨35453578407993238796397335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23635718938662159197598223 35453578407993238796397335)
      ·
        refine ⟨53180367611989858194596003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35453578407993238796397335 53180367611989858194596003)
        ·
          refine ⟨79770551417984787291894005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53180367611989858194596003 79770551417984787291894005)
          ·
            refine ⟨7478489195436073808615063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79770551417984787291894005 7478489195436073808615063)
            ·
              refine ⟨11217733793154110712922595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7478489195436073808615063 11217733793154110712922595)
              ·
                refine ⟨16826600689731166069383893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11217733793154110712922595 16826600689731166069383893)
                ·
                  refine ⟨394373453665574204751185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16826600689731166069383893 394373453665574204751185)
                  ·
                    rfl

theorem cell22_3456178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3456178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456178 prefixEnd_3456178 := by exact prefixLift 3456178
  have htrace : WordTrace (prefixWord ++ tailWord_3456178) baseStart_3456178 baseEnd_3456178 := by
    simpa [prefixWord, tailWord_3456178, baseEnd_3456178] using wordTrace_append hprefix tailTrace_3456178
  have hstable : (prefixWord ++ tailWord_3456178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456178).length < 2 ^ (prefixWord ++ tailWord_3456178).sum := by decide
  have hdescent : baseEnd_3456178 < baseStart_3456178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456216 : List Nat := [2, 1, 2, 2, 6, 1, 1, 3, 1, 3]
def baseStart_3456216 : Nat := 118140960795 + 3456216 * 2 ^ 59
def prefixEnd_3456216 : Nat := 4983230072969 + 3 ^ 40 * 3456216 * 2
def baseEnd_3456216 : Nat := 1183133369173303181803439

theorem tailTrace_3456216 : CollatzResearch.WordTrace tailWord_3456216 prefixEnd_3456216 1183133369173303181803439 := by
  unfold tailWord_3456216
  simp only [CollatzResearch.WordTrace]
  refine ⟨63029276823363590771870251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84039035764484787695827001 63029276823363590771870251)
  ·
    refine ⟨94543915235045386157805377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63029276823363590771870251 94543915235045386157805377)
    ·
      refine ⟨70907936426284039618354033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94543915235045386157805377 70907936426284039618354033)
      ·
        refine ⟨53180952319713029713765525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70907936426284039618354033 53180952319713029713765525)
        ·
          refine ⟨2492857139986548267832759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53180952319713029713765525 2492857139986548267832759)
          ·
            refine ⟨3739285709979822401749139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492857139986548267832759 3739285709979822401749139)
            ·
              refine ⟨5608928564969733602623709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739285709979822401749139 5608928564969733602623709)
              ·
                refine ⟨2103348211863650100983891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5608928564969733602623709 2103348211863650100983891)
                ·
                  refine ⟨3155022317795475151475837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103348211863650100983891 3155022317795475151475837)
                  ·
                    refine ⟨1183133369173303181803439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155022317795475151475837 1183133369173303181803439)
                    ·
                      rfl

theorem cell22_3456216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_3456216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456216 prefixEnd_3456216 := by exact prefixLift 3456216
  have htrace : WordTrace (prefixWord ++ tailWord_3456216) baseStart_3456216 baseEnd_3456216 := by
    simpa [prefixWord, tailWord_3456216, baseEnd_3456216] using wordTrace_append hprefix tailTrace_3456216
  have hstable : (prefixWord ++ tailWord_3456216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456216).length < 2 ^ (prefixWord ++ tailWord_3456216).sum := by decide
  have hdescent : baseEnd_3456216 < baseStart_3456216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456225 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3456225 : Nat := 118140960795 + 3456225 * 2 ^ 59
def prefixEnd_3456225 : Nat := 4983230072969 + 3 ^ 40 * 3456225 * 2
def baseEnd_3456225 : Nat := 1183136450057230158328411

theorem tailTrace_3456225 : CollatzResearch.WordTrace tailWord_3456225 prefixEnd_3456225 1183136450057230158328411 := by
  unfold tailWord_3456225
  simp only [CollatzResearch.WordTrace]
  refine ⟨126058881903694576080818129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84039254602463050720545419 126058881903694576080818129)
  ·
    refine ⟨94544161427770932060613597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126058881903694576080818129 94544161427770932060613597)
    ·
      refine ⟨35454060535414099522730099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94544161427770932060613597 35454060535414099522730099)
      ·
        refine ⟨53181090803121149284095149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35454060535414099522730099 53181090803121149284095149)
        ·
          refine ⟨19942909051170430981535681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53181090803121149284095149 19942909051170430981535681)
          ·
            refine ⟨14957181788377823236151761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19942909051170430981535681 14957181788377823236151761)
            ·
              refine ⟨11217886341283367427113821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14957181788377823236151761 11217886341283367427113821)
              ·
                refine ⟨4206707377981262785167683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11217886341283367427113821 4206707377981262785167683)
                ·
                  refine ⟨6310061066971894177751525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4206707377981262785167683 6310061066971894177751525)
                  ·
                    refine ⟨1183136450057230158328411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6310061066971894177751525 1183136450057230158328411)
                    ·
                      rfl

theorem cell22_3456225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3456225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456225 prefixEnd_3456225 := by exact prefixLift 3456225
  have htrace : WordTrace (prefixWord ++ tailWord_3456225) baseStart_3456225 baseEnd_3456225 := by
    simpa [prefixWord, tailWord_3456225, baseEnd_3456225] using wordTrace_append hprefix tailTrace_3456225
  have hstable : (prefixWord ++ tailWord_3456225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456225).length < 2 ^ (prefixWord ++ tailWord_3456225).sum := by decide
  have hdescent : baseEnd_3456225 < baseStart_3456225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456268 : List Nat := [2, 2, 1, 2, 2, 3, 2, 8]
def baseStart_3456268 : Nat := 118140960795 + 3456268 * 2 ^ 59
def prefixEnd_3456268 : Nat := 4983230072969 + 3 ^ 40 * 3456268 * 2
def baseEnd_3456268 : Nat := 131461241092888042167031

theorem tailTrace_3456268 : CollatzResearch.WordTrace tailWord_3456268 prefixEnd_3456268 131461241092888042167031 := by
  unfold tailWord_3456268
  simp only [CollatzResearch.WordTrace]
  refine ⟨63030225121269397212316729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84040300161692529616422305 63030225121269397212316729)
  ·
    refine ⟨47272668840952047909237547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63030225121269397212316729 47272668840952047909237547)
    ·
      refine ⟨70909003261428071863856321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47272668840952047909237547 70909003261428071863856321)
      ·
        refine ⟨53181752446071053897892241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70909003261428071863856321 53181752446071053897892241)
        ·
          refine ⟨39886314334553290423419181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53181752446071053897892241 39886314334553290423419181)
          ·
            refine ⟨14957367875457483908782193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39886314334553290423419181 14957367875457483908782193)
            ·
              refine ⟨11218025906593112931586645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14957367875457483908782193 11218025906593112931586645)
              ·
                refine ⟨131461241092888042167031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11218025906593112931586645 131461241092888042167031)
                ·
                  rfl

theorem cell22_3456268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 8].length) (baseStart_3456268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456268 prefixEnd_3456268 := by exact prefixLift 3456268
  have htrace : WordTrace (prefixWord ++ tailWord_3456268) baseStart_3456268 baseEnd_3456268 := by
    simpa [prefixWord, tailWord_3456268, baseEnd_3456268] using wordTrace_append hprefix tailTrace_3456268
  have hstable : (prefixWord ++ tailWord_3456268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456268).length < 2 ^ (prefixWord ++ tailWord_3456268).sum := by decide
  have hdescent : baseEnd_3456268 < baseStart_3456268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456270 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3456270 : Nat := 118140960795 + 3456270 * 2 ^ 59
def prefixEnd_3456270 : Nat := 4983230072969 + 3 ^ 40 * 3456270 * 2
def baseEnd_3456270 : Nat := 1183151854476865040953273

theorem tailTrace_3456270 : CollatzResearch.WordTrace tailWord_3456270 prefixEnd_3456270 1183151854476865040953273 := by
  unfold tailWord_3456270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757565398566443595775783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84040348792354365844137509 15757565398566443595775783)
  ·
    refine ⟨23636348097849665393663675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15757565398566443595775783 23636348097849665393663675)
    ·
      refine ⟨35454522146774498090495513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23636348097849665393663675 35454522146774498090495513)
      ·
        refine ⟨26590891610080873567871635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35454522146774498090495513 26590891610080873567871635)
        ·
          refine ⟨39886337415121310351807453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26590891610080873567871635 39886337415121310351807453)
          ·
            refine ⟨14957376530670491381927795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39886337415121310351807453 14957376530670491381927795)
            ·
              refine ⟨22436064796005737072891693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14957376530670491381927795 22436064796005737072891693)
              ·
                refine ⟨8413524298502151402334385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22436064796005737072891693 8413524298502151402334385)
                ·
                  refine ⟨6310143223876613551750789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8413524298502151402334385 6310143223876613551750789)
                  ·
                    refine ⟨1183151854476865040953273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6310143223876613551750789 1183151854476865040953273)
                    ·
                      rfl

theorem cell22_3456270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3456270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456270 prefixEnd_3456270 := by exact prefixLift 3456270
  have htrace : WordTrace (prefixWord ++ tailWord_3456270) baseStart_3456270 baseEnd_3456270 := by
    simpa [prefixWord, tailWord_3456270, baseEnd_3456270] using wordTrace_append hprefix tailTrace_3456270
  have hstable : (prefixWord ++ tailWord_3456270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456270).length < 2 ^ (prefixWord ++ tailWord_3456270).sum := by decide
  have hdescent : baseEnd_3456270 < baseStart_3456270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456300 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_3456300 : Nat := 118140960795 + 3456300 * 2 ^ 59
def prefixEnd_3456300 : Nat := 4983230072969 + 3 ^ 40 * 3456300 * 2
def baseEnd_3456300 : Nat := 1183162124089954962703181

theorem tailTrace_3456300 : CollatzResearch.WordTrace tailWord_3456300 prefixEnd_3456300 1183162124089954962703181 := by
  unfold tailWord_3456300
  simp only [CollatzResearch.WordTrace]
  refine ⟨63030808689211431944899177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84041078252281909259865569 63030808689211431944899177)
  ·
    refine ⟨47273106516908573958674383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63030808689211431944899177 47273106516908573958674383)
    ·
      refine ⟨70909659775362860938011575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47273106516908573958674383 70909659775362860938011575)
      ·
        refine ⟨106364489663044291407017363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70909659775362860938011575 106364489663044291407017363)
        ·
          refine ⟨159546734494566437110526045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106364489663044291407017363 159546734494566437110526045)
          ·
            refine ⟨59830025435462413916447267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159546734494566437110526045 59830025435462413916447267)
            ·
              refine ⟨89745038153193620874670901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59830025435462413916447267 89745038153193620874670901)
              ·
                refine ⟨8413597326861901957000397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89745038153193620874670901 8413597326861901957000397)
                ·
                  refine ⟨3155098997573213233875149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8413597326861901957000397 3155098997573213233875149)
                  ·
                    refine ⟨1183162124089954962703181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155098997573213233875149 1183162124089954962703181)
                    ·
                      rfl

theorem cell22_3456300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_3456300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456300 prefixEnd_3456300 := by exact prefixLift 3456300
  have htrace : WordTrace (prefixWord ++ tailWord_3456300) baseStart_3456300 baseEnd_3456300 := by
    simpa [prefixWord, tailWord_3456300, baseEnd_3456300] using wordTrace_append hprefix tailTrace_3456300
  have hstable : (prefixWord ++ tailWord_3456300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456300).length < 2 ^ (prefixWord ++ tailWord_3456300).sum := by decide
  have hdescent : baseEnd_3456300 < baseStart_3456300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456328 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_3456328 : Nat := 118140960795 + 3456328 * 2 ^ 59
def prefixEnd_3456328 : Nat := 4983230072969 + 3 ^ 40 * 3456328 * 2
def baseEnd_3456328 : Nat := 1183171709062172223003095

theorem tailTrace_3456328 : CollatzResearch.WordTrace tailWord_3456328 prefixEnd_3456328 1183171709062172223003095 := by
  unfold tailWord_3456328
  simp only [CollatzResearch.WordTrace]
  refine ⟨63031319311160712335908819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84041759081547616447878425 63031319311160712335908819)
  ·
    refine ⟨94546978966741068503863229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63031319311160712335908819 94546978966741068503863229)
    ·
      refine ⟨35455117112527900688948711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94546978966741068503863229 35455117112527900688948711)
      ·
        refine ⟨53182675668791851033423067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35455117112527900688948711 53182675668791851033423067)
        ·
          refine ⟨79774013503187776550134601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53182675668791851033423067 79774013503187776550134601)
          ·
            refine ⟨59830510127390832412600951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79774013503187776550134601 59830510127390832412600951)
            ·
              refine ⟨89745765191086248618901427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59830510127390832412600951 89745765191086248618901427)
              ·
                refine ⟨134618647786629372928352141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89745765191086248618901427 134618647786629372928352141)
                ·
                  refine ⟨50481992919986014848132053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134618647786629372928352141 50481992919986014848132053)
                  ·
                    refine ⟨1183171709062172223003095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50481992919986014848132053 1183171709062172223003095)
                    ·
                      rfl

theorem cell22_3456328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_3456328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456328 prefixEnd_3456328 := by exact prefixLift 3456328
  have htrace : WordTrace (prefixWord ++ tailWord_3456328) baseStart_3456328 baseEnd_3456328 := by
    simpa [prefixWord, tailWord_3456328, baseEnd_3456328] using wordTrace_append hprefix tailTrace_3456328
  have hstable : (prefixWord ++ tailWord_3456328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456328).length < 2 ^ (prefixWord ++ tailWord_3456328).sum := by decide
  have hdescent : baseEnd_3456328 < baseStart_3456328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456334 : List Nat := [4, 1, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3456334 : Nat := 118140960795 + 3456334 * 2 ^ 59
def prefixEnd_3456334 : Nat := 4983230072969 + 3 ^ 40 * 3456334 * 2
def baseEnd_3456334 : Nat := 1183173762984790207353077

theorem tailTrace_3456334 : CollatzResearch.WordTrace tailWord_3456334 prefixEnd_3456334 1183173762984790207353077 := by
  unfold tailWord_3456334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757857182537460962067007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84041904973533125131024037 15757857182537460962067007)
  ·
    refine ⟨23636785773806191443100511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15757857182537460962067007 23636785773806191443100511)
    ·
      refine ⟨35455178660709287164650767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23636785773806191443100511 35455178660709287164650767)
      ·
        refine ⟨53182767991063930746976151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35455178660709287164650767 53182767991063930746976151)
        ·
          refine ⟨79774151986595896120464227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53182767991063930746976151 79774151986595896120464227)
          ·
            refine ⟨119661227979893844180696341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79774151986595896120464227 119661227979893844180696341)
            ·
              refine ⟨5609120061557523945970141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119661227979893844180696341 5609120061557523945970141)
              ·
                refine ⟨2103420023084071479738803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5609120061557523945970141 2103420023084071479738803)
                ·
                  refine ⟨3155130034626107219608205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103420023084071479738803 3155130034626107219608205)
                  ·
                    refine ⟨1183173762984790207353077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155130034626107219608205 1183173762984790207353077)
                    ·
                      rfl

theorem cell22_3456334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3456334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456334 prefixEnd_3456334 := by exact prefixLift 3456334
  have htrace : WordTrace (prefixWord ++ tailWord_3456334) baseStart_3456334 baseEnd_3456334 := by
    simpa [prefixWord, tailWord_3456334, baseEnd_3456334] using wordTrace_append hprefix tailTrace_3456334
  have hstable : (prefixWord ++ tailWord_3456334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456334).length < 2 ^ (prefixWord ++ tailWord_3456334).sum := by decide
  have hdescent : baseEnd_3456334 < baseStart_3456334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456405 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3456405 : Nat := 118140960795 + 3456405 * 2 ^ 59
def prefixEnd_3456405 : Nat := 4983230072969 + 3 ^ 40 * 3456405 * 2
def baseEnd_3456405 : Nat := 1183198067735769688827859

theorem tailTrace_3456405 : CollatzResearch.WordTrace tailWord_3456405 prefixEnd_3456405 1183198067735769688827859 := by
  unfold tailWord_3456405
  simp only [CollatzResearch.WordTrace]
  refine ⟨126065447043042466822370669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84043631362028311214913779 126065447043042466822370669)
  ·
    refine ⟨47274542641140925058389001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126065447043042466822370669 47274542641140925058389001)
    ·
      refine ⟨35455906980855693793791751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47274542641140925058389001 35455906980855693793791751)
      ·
        refine ⟨53183860471283540690687627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35455906980855693793791751 53183860471283540690687627)
        ·
          refine ⟨79775790706925311036031441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53183860471283540690687627 79775790706925311036031441)
          ·
            refine ⟨59831843030193983277023581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79775790706925311036031441 59831843030193983277023581)
            ·
              refine ⟨22436941136322743728883843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59831843030193983277023581 22436941136322743728883843)
              ·
                refine ⟨33655411704484115593325765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22436941136322743728883843 33655411704484115593325765)
                ·
                  refine ⟨6310389694590771673748581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33655411704484115593325765 6310389694590771673748581)
                  ·
                    refine ⟨1183198067735769688827859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6310389694590771673748581 1183198067735769688827859)
                    ·
                      rfl

theorem cell22_3456405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3456405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456405 prefixEnd_3456405 := by exact prefixLift 3456405
  have htrace : WordTrace (prefixWord ++ tailWord_3456405) baseStart_3456405 baseEnd_3456405 := by
    simpa [prefixWord, tailWord_3456405, baseEnd_3456405] using wordTrace_append hprefix tailTrace_3456405
  have hstable : (prefixWord ++ tailWord_3456405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456405).length < 2 ^ (prefixWord ++ tailWord_3456405).sum := by decide
  have hdescent : baseEnd_3456405 < baseStart_3456405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456407 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 2, 3]
def baseStart_3456407 : Nat := 118140960795 + 3456407 * 2 ^ 59
def prefixEnd_3456407 : Nat := 4983230072969 + 3 ^ 40 * 3456407 * 2
def baseEnd_3456407 : Nat := 1183198752376642350277853

theorem tailTrace_3456407 : CollatzResearch.WordTrace tailWord_3456407 prefixEnd_3456407 1183198752376642350277853 := by
  unfold tailWord_3456407
  simp only [CollatzResearch.WordTrace]
  refine ⟨126065519989035221163943475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84043679992690147442628983 126065519989035221163943475)
  ·
    refine ⟨189098279983552831745915213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126065519989035221163943475 189098279983552831745915213)
    ·
      refine ⟨70911854993832311904718205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189098279983552831745915213 70911854993832311904718205)
      ·
        refine ⟨26591945622687116964269327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70911854993832311904718205 26591945622687116964269327)
        ·
          refine ⟨39887918434030675446403991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26591945622687116964269327 39887918434030675446403991)
          ·
            refine ⟨59831877651046013169605987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39887918434030675446403991 59831877651046013169605987)
            ·
              refine ⟨89747816476569019754408981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59831877651046013169605987 89747816476569019754408981)
              ·
                refine ⟨4206928897339172800987921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89747816476569019754408981 4206928897339172800987921)
                ·
                  refine ⟨3155196673004379600740941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4206928897339172800987921 3155196673004379600740941)
                  ·
                    refine ⟨1183198752376642350277853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155196673004379600740941 1183198752376642350277853)
                    ·
                      rfl

theorem cell22_3456407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_3456407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456407 prefixEnd_3456407 := by exact prefixLift 3456407
  have htrace : WordTrace (prefixWord ++ tailWord_3456407) baseStart_3456407 baseEnd_3456407 := by
    simpa [prefixWord, tailWord_3456407, baseEnd_3456407] using wordTrace_append hprefix tailTrace_3456407
  have hstable : (prefixWord ++ tailWord_3456407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456407).length < 2 ^ (prefixWord ++ tailWord_3456407).sum := by decide
  have hdescent : baseEnd_3456407 < baseStart_3456407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456409 : List Nat := [1, 2, 1, 2, 1, 6, 3, 2, 4]
def baseStart_3456409 : Nat := 118140960795 + 3456409 * 2 ^ 59
def prefixEnd_3456409 : Nat := 4983230072969 + 3 ^ 40 * 3456409 * 2
def baseEnd_3456409 : Nat := 394399812339171670575949

theorem tailTrace_3456409 : CollatzResearch.WordTrace tailWord_3456409 prefixEnd_3456409 394399812339171670575949 := by
  unfold tailWord_3456409
  simp only [CollatzResearch.WordTrace]
  refine ⟨126065592935027975505516281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84043728623351983670344187 126065592935027975505516281)
  ·
    refine ⟨94549194701270981629137211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126065592935027975505516281 94549194701270981629137211)
    ·
      refine ⟨141823792051906472443705817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94549194701270981629137211 141823792051906472443705817)
      ·
        refine ⟨106367844038929854332779363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141823792051906472443705817 106367844038929854332779363)
        ·
          refine ⟨159551766058394781499169045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106367844038929854332779363 159551766058394781499169045)
          ·
            refine ⟨7478989033987255382773549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159551766058394781499169045 7478989033987255382773549)
            ·
              refine ⟨2804620887745220768540081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7478989033987255382773549 2804620887745220768540081)
              ·
                refine ⟨2103465665808915576405061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804620887745220768540081 2103465665808915576405061)
                ·
                  refine ⟨394399812339171670575949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103465665808915576405061 394399812339171670575949)
                  ·
                    rfl

theorem cell22_3456409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_3456409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456409 prefixEnd_3456409 := by exact prefixLift 3456409
  have htrace : WordTrace (prefixWord ++ tailWord_3456409) baseStart_3456409 baseEnd_3456409 := by
    simpa [prefixWord, tailWord_3456409, baseEnd_3456409] using wordTrace_append hprefix tailTrace_3456409
  have hstable : (prefixWord ++ tailWord_3456409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456409).length < 2 ^ (prefixWord ++ tailWord_3456409).sum := by decide
  have hdescent : baseEnd_3456409 < baseStart_3456409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456514 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3456514 : Nat := 118140960795 + 3456514 * 2 ^ 59
def prefixEnd_3456514 : Nat := 4983230072969 + 3 ^ 40 * 3456514 * 2
def baseEnd_3456514 : Nat := 1183235380663329737852525

theorem tailTrace_3456514 : CollatzResearch.WordTrace tailWord_3456514 prefixEnd_3456514 1183235380663329737852525 := by
  unfold tailWord_3456514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31517355649911894609522149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84046281733098385625392397 31517355649911894609522149)
  ·
    refine ⟨5909504184358480239285403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31517355649911894609522149 5909504184358480239285403)
    ·
      refine ⟨8864256276537720358928105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5909504184358480239285403 8864256276537720358928105)
      ·
        refine ⟨6648192207403290269196079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8864256276537720358928105 6648192207403290269196079)
        ·
          refine ⟨9972288311104935403794119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6648192207403290269196079 9972288311104935403794119)
          ·
            refine ⟨14958432466657403105691179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9972288311104935403794119 14958432466657403105691179)
            ·
              refine ⟨22437648699986104658536769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14958432466657403105691179 22437648699986104658536769)
              ·
                refine ⟨16828236524989578493902577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22437648699986104658536769 16828236524989578493902577)
                ·
                  refine ⟨12621177393742183870426933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16828236524989578493902577 12621177393742183870426933)
                  ·
                    refine ⟨1183235380663329737852525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12621177393742183870426933 1183235380663329737852525)
                    ·
                      rfl

theorem cell22_3456514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3456514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456514 prefixEnd_3456514 := by exact prefixLift 3456514
  have htrace : WordTrace (prefixWord ++ tailWord_3456514) baseStart_3456514 baseEnd_3456514 := by
    simpa [prefixWord, tailWord_3456514, baseEnd_3456514] using wordTrace_append hprefix tailTrace_3456514
  have hstable : (prefixWord ++ tailWord_3456514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456514).length < 2 ^ (prefixWord ++ tailWord_3456514).sum := by decide
  have hdescent : baseEnd_3456514 < baseStart_3456514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456516 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 5]
def baseStart_3456516 : Nat := 118140960795 + 3456516 * 2 ^ 59
def prefixEnd_3456516 : Nat := 4983230072969 + 3 ^ 40 * 3456516 * 2
def baseEnd_3456516 : Nat := 394412021768067466434173

theorem tailTrace_3456516 : CollatzResearch.WordTrace tailWord_3456516 prefixEnd_3456516 394412021768067466434173 := by
  unfold tailWord_3456516
  simp only [CollatzResearch.WordTrace]
  refine ⟨63034747772820166389830701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84046330363760221853107601 63034747772820166389830701)
  ·
    refine ⟨23638030414807562396186513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63034747772820166389830701 23638030414807562396186513)
    ·
      refine ⟨17728522811105671797139885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23638030414807562396186513 17728522811105671797139885)
      ·
        refine ⟨6648196054164626923927457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17728522811105671797139885 6648196054164626923927457)
        ·
          refine ⟨4986147040623470192945593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6648196054164626923927457 4986147040623470192945593)
          ·
            refine ⟨3739610280467602644709195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4986147040623470192945593 3739610280467602644709195)
            ·
              refine ⟨5609415420701403967063793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739610280467602644709195 5609415420701403967063793)
              ·
                refine ⟨4207061565526052975297845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5609415420701403967063793 4207061565526052975297845)
                ·
                  refine ⟨394412021768067466434173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4207061565526052975297845 394412021768067466434173)
                  ·
                    rfl

theorem cell22_3456516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_3456516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456516 prefixEnd_3456516 := by exact prefixLift 3456516
  have htrace : WordTrace (prefixWord ++ tailWord_3456516) baseStart_3456516 baseEnd_3456516 := by
    simpa [prefixWord, tailWord_3456516, baseEnd_3456516] using wordTrace_append hprefix tailTrace_3456516
  have hstable : (prefixWord ++ tailWord_3456516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456516).length < 2 ^ (prefixWord ++ tailWord_3456516).sum := by decide
  have hdescent : baseEnd_3456516 < baseStart_3456516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456664 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_3456664 : Nat := 118140960795 + 3456664 * 2 ^ 59
def prefixEnd_3456664 : Nat := 4983230072969 + 3 ^ 40 * 3456664 * 2
def baseEnd_3456664 : Nat := 1183286728728779346602065

theorem tailTrace_3456664 : CollatzResearch.WordTrace tailWord_3456664 prefixEnd_3456664 1183286728728779346602065 := by
  unfold tailWord_3456664
  simp only [CollatzResearch.WordTrace]
  refine ⟨63037446774552077028024523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84049929032736102704032697 63037446774552077028024523)
  ·
    refine ⟨94556170161828115542036785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63037446774552077028024523 94556170161828115542036785)
    ·
      refine ⟨70917127621371086656527589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94556170161828115542036785 70917127621371086656527589)
      ·
        refine ⟨13296961429007078748098923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70917127621371086656527589 13296961429007078748098923)
        ·
          refine ⟨19945442143510618122148385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13296961429007078748098923 19945442143510618122148385)
          ·
            refine ⟨14959081607632963591611289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19945442143510618122148385 14959081607632963591611289)
            ·
              refine ⟨11219311205724722693708467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14959081607632963591611289 11219311205724722693708467)
              ·
                refine ⟨16828966808587084040562701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11219311205724722693708467 16828966808587084040562701)
                ·
                  refine ⟨6310862553220156515211013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16828966808587084040562701 6310862553220156515211013)
                  ·
                    refine ⟨1183286728728779346602065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6310862553220156515211013 1183286728728779346602065)
                    ·
                      rfl

theorem cell22_3456664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_3456664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456664 prefixEnd_3456664 := by exact prefixLift 3456664
  have htrace : WordTrace (prefixWord ++ tailWord_3456664) baseStart_3456664 baseEnd_3456664 := by
    simpa [prefixWord, tailWord_3456664, baseEnd_3456664] using wordTrace_append hprefix tailTrace_3456664
  have hstable : (prefixWord ++ tailWord_3456664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456664).length < 2 ^ (prefixWord ++ tailWord_3456664).sum := by decide
  have hdescent : baseEnd_3456664 < baseStart_3456664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456743 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 2, 4]
def baseStart_3456743 : Nat := 118140960795 + 3456743 * 2 ^ 59
def prefixEnd_3456743 : Nat := 4983230072969 + 3 ^ 40 * 3456743 * 2
def baseEnd_3456743 : Nat := 1183313772043249473876823

theorem tailTrace_3456743 : CollatzResearch.WordTrace tailWord_3456743 prefixEnd_3456743 1183313772043249473876823 := by
  unfold tailWord_3456743
  simp only [CollatzResearch.WordTrace]
  refine ⟨126077774915817950548174883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84051849943878633698783255 126077774915817950548174883)
  ·
    refine ⟨189116662373726925822262325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126077774915817950548174883 189116662373726925822262325)
    ·
      refine ⟨17729687097536899295837093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189116662373726925822262325 17729687097536899295837093)
      ·
        refine ⟨3324316330788168617969455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17729687097536899295837093 3324316330788168617969455)
        ·
          refine ⟨4986474496182252926954183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324316330788168617969455 4986474496182252926954183)
          ·
            refine ⟨7479711744273379390431275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4986474496182252926954183 7479711744273379390431275)
            ·
              refine ⟨11219567616410069085646913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7479711744273379390431275 11219567616410069085646913)
              ·
                refine ⟨8414675712307551814235185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11219567616410069085646913 8414675712307551814235185)
                ·
                  refine ⟨6311006784230663860676389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8414675712307551814235185 6311006784230663860676389)
                  ·
                    refine ⟨1183313772043249473876823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6311006784230663860676389 1183313772043249473876823)
                    ·
                      rfl

theorem cell22_3456743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_3456743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456743 prefixEnd_3456743 := by exact prefixLift 3456743
  have htrace : WordTrace (prefixWord ++ tailWord_3456743) baseStart_3456743 baseEnd_3456743 := by
    simpa [prefixWord, tailWord_3456743, baseEnd_3456743] using wordTrace_append hprefix tailTrace_3456743
  have hstable : (prefixWord ++ tailWord_3456743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456743).length < 2 ^ (prefixWord ++ tailWord_3456743).sum := by decide
  have hdescent : baseEnd_3456743 < baseStart_3456743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456754 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3456754 : Nat := 118140960795 + 3456754 * 2 ^ 59
def prefixEnd_3456754 : Nat := 4983230072969 + 3 ^ 40 * 3456754 * 2
def baseEnd_3456754 : Nat := 1183317537568049111851789

theorem tailTrace_3456754 : CollatzResearch.WordTrace tailWord_3456754 prefixEnd_3456754 1183317537568049111851789 := by
  unfold tailWord_3456754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31519544029694524856706329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84052117412518732951216877 31519544029694524856706329)
  ·
    refine ⟨23639658022270893642529747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31519544029694524856706329 23639658022270893642529747)
    ·
      refine ⟨35459487033406340463794621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23639658022270893642529747 35459487033406340463794621)
      ·
        refine ⟨13297307637527377673922983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35459487033406340463794621 13297307637527377673922983)
        ·
          refine ⟨19945961456291066510884475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13297307637527377673922983 19945961456291066510884475)
          ·
            refine ⟨29918942184436599766326713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19945961456291066510884475 29918942184436599766326713)
            ·
              refine ⟨22439206638327449824745035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29918942184436599766326713 22439206638327449824745035)
              ·
                refine ⟨33658809957491174737117553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22439206638327449824745035 33658809957491174737117553)
                ·
                  refine ⟨25244107468118381052838165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33658809957491174737117553 25244107468118381052838165)
                  ·
                    refine ⟨1183317537568049111851789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25244107468118381052838165 1183317537568049111851789)
                    ·
                      rfl

theorem cell22_3456754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3456754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456754 prefixEnd_3456754 := by exact prefixLift 3456754
  have htrace : WordTrace (prefixWord ++ tailWord_3456754) baseStart_3456754 baseEnd_3456754 := by
    simpa [prefixWord, tailWord_3456754, baseEnd_3456754] using wordTrace_append hprefix tailTrace_3456754
  have hstable : (prefixWord ++ tailWord_3456754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456754).length < 2 ^ (prefixWord ++ tailWord_3456754).sum := by decide
  have hdescent : baseEnd_3456754 < baseStart_3456754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456831 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 6]
def baseStart_3456831 : Nat := 118140960795 + 3456831 * 2 ^ 59
def prefixEnd_3456831 : Nat := 4983230072969 + 3 ^ 40 * 3456831 * 2
def baseEnd_3456831 : Nat := 394447965413882192558851

theorem tailTrace_3456831 : CollatzResearch.WordTrace tailWord_3456831 prefixEnd_3456831 394447965413882192558851 := by
  unfold tailWord_3456831
  simp only [CollatzResearch.WordTrace]
  refine ⟨126080984539499141577378347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84053989692999427718252231 126080984539499141577378347)
  ·
    refine ⟨189121476809248712366067521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126080984539499141577378347 189121476809248712366067521)
    ·
      refine ⟨141841107606936534274550641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189121476809248712366067521 141841107606936534274550641)
      ·
        refine ⟨106380830705202400705912981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141841107606936534274550641 106380830705202400705912981)
        ·
          refine ⟨4986601439306362533089671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106380830705202400705912981 4986601439306362533089671)
          ·
            refine ⟨7479902158959543799634507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4986601439306362533089671 7479902158959543799634507)
            ·
              refine ⟨11219853238439315699451761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7479902158959543799634507 11219853238439315699451761)
              ·
                refine ⟨8414889928829486774588821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11219853238439315699451761 8414889928829486774588821)
                ·
                  refine ⟨394447965413882192558851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8414889928829486774588821 394447965413882192558851)
                  ·
                    rfl

theorem cell22_3456831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 6].length) (baseStart_3456831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456831 prefixEnd_3456831 := by exact prefixLift 3456831
  have htrace : WordTrace (prefixWord ++ tailWord_3456831) baseStart_3456831 baseEnd_3456831 := by
    simpa [prefixWord, tailWord_3456831, baseEnd_3456831] using wordTrace_append hprefix tailTrace_3456831
  have hstable : (prefixWord ++ tailWord_3456831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456831).length < 2 ^ (prefixWord ++ tailWord_3456831).sum := by decide
  have hdescent : baseEnd_3456831 < baseStart_3456831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456850 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_3456850 : Nat := 118140960795 + 3456850 * 2 ^ 59
def prefixEnd_3456850 : Nat := 4983230072969 + 3 ^ 40 * 3456850 * 2
def baseEnd_3456850 : Nat := 1183350400329936861451495

theorem tailTrace_3456850 : CollatzResearch.WordTrace tailWord_3456850 prefixEnd_3456850 1183350400329936861451495 := by
  unfold tailWord_3456850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31520419381607576955580001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84054451684286871881546669 31520419381607576955580001)
  ·
    refine ⟨23640314536205682716685001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31520419381607576955580001 23640314536205682716685001)
    ·
      refine ⟨17730235902154262037513751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23640314536205682716685001 17730235902154262037513751)
      ·
        refine ⟨26595353853231393056270627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17730235902154262037513751 26595353853231393056270627)
        ·
          refine ⟨39893030779847089584405941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26595353853231393056270627 39893030779847089584405941)
          ·
            refine ⟨3739971635610664648538057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39893030779847089584405941 3739971635610664648538057)
            ·
              refine ⟨2804978726707998486403543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739971635610664648538057 2804978726707998486403543)
              ·
                refine ⟨4207468090061997729605315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804978726707998486403543 4207468090061997729605315)
                ·
                  refine ⟨6311202135092996594407973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207468090061997729605315 6311202135092996594407973)
                  ·
                    refine ⟨1183350400329936861451495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6311202135092996594407973 1183350400329936861451495)
                    ·
                      rfl

theorem cell22_3456850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_3456850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456850 prefixEnd_3456850 := by exact prefixLift 3456850
  have htrace : WordTrace (prefixWord ++ tailWord_3456850) baseStart_3456850 baseEnd_3456850 := by
    simpa [prefixWord, tailWord_3456850, baseEnd_3456850] using wordTrace_append hprefix tailTrace_3456850
  have hstable : (prefixWord ++ tailWord_3456850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456850).length < 2 ^ (prefixWord ++ tailWord_3456850).sum := by decide
  have hdescent : baseEnd_3456850 < baseStart_3456850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456863 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 2, 3]
def baseStart_3456863 : Nat := 118140960795 + 3456863 * 2 ^ 59
def prefixEnd_3456863 : Nat := 4983230072969 + 3 ^ 40 * 3456863 * 2
def baseEnd_3456863 : Nat := 1183354850495609160876455

theorem tailTrace_3456863 : CollatzResearch.WordTrace tailWord_3456863 prefixEnd_3456863 1183354850495609160876455 := by
  unfold tailWord_3456863
  simp only [CollatzResearch.WordTrace]
  refine ⟨126082151675383211042543243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84054767783588807361695495 126082151675383211042543243)
  ·
    refine ⟨189123227513074816563814865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126082151675383211042543243 189123227513074816563814865)
    ·
      refine ⟨141842420634806112422861149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189123227513074816563814865 141842420634806112422861149)
      ·
        refine ⟨53190907738052292158572931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141842420634806112422861149 53190907738052292158572931)
        ·
          refine ⟨79786361607078438237859397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53190907738052292158572931 79786361607078438237859397)
          ·
            refine ⟨14959942801327207169598637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79786361607078438237859397 14959942801327207169598637)
            ·
              refine ⟨5609978550497702688599489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14959942801327207169598637 5609978550497702688599489)
              ·
                refine ⟨4207483912873277016449617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5609978550497702688599489 4207483912873277016449617)
                ·
                  refine ⟨3155612934654957762337213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207483912873277016449617 3155612934654957762337213)
                  ·
                    refine ⟨1183354850495609160876455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155612934654957762337213 1183354850495609160876455)
                    ·
                      rfl

theorem cell22_3456863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_3456863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456863 prefixEnd_3456863 := by exact prefixLift 3456863
  have htrace : WordTrace (prefixWord ++ tailWord_3456863) baseStart_3456863 baseEnd_3456863 := by
    simpa [prefixWord, tailWord_3456863, baseEnd_3456863] using wordTrace_append hprefix tailTrace_3456863
  have hstable : (prefixWord ++ tailWord_3456863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456863).length < 2 ^ (prefixWord ++ tailWord_3456863).sum := by decide
  have hdescent : baseEnd_3456863 < baseStart_3456863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456910 : List Nat := [4, 1, 1, 5, 2, 1, 8]
def baseStart_3456910 : Nat := 118140960795 + 3456910 * 2 ^ 59
def prefixEnd_3456910 : Nat := 4983230072969 + 3 ^ 40 * 3456910 * 2
def baseEnd_3456910 : Nat := 43828553316893211294493

theorem tailTrace_3456910 : CollatzResearch.WordTrace tailWord_3456910 prefixEnd_3456910 43828553316893211294493 := by
  unfold tailWord_3456910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15760483238276617258688023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84055910604141958713002789 15760483238276617258688023)
  ·
    refine ⟨23640724857414925888032035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15760483238276617258688023 23640724857414925888032035)
    ·
      refine ⟨35461087286122388832048053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23640724857414925888032035 35461087286122388832048053)
      ·
        refine ⟨3324476933073973953004505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35461087286122388832048053 3324476933073973953004505)
        ·
          refine ⟨2493357699805480464753379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324476933073973953004505 2493357699805480464753379)
          ·
            refine ⟨3740036549708220697130069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493357699805480464753379 3740036549708220697130069)
            ·
              refine ⟨43828553316893211294493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3740036549708220697130069 43828553316893211294493)
              ·
                rfl

theorem cell22_3456910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 8].length) (baseStart_3456910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456910 prefixEnd_3456910 := by exact prefixLift 3456910
  have htrace : WordTrace (prefixWord ++ tailWord_3456910) baseStart_3456910 baseEnd_3456910 := by
    simpa [prefixWord, tailWord_3456910, baseEnd_3456910] using wordTrace_append hprefix tailTrace_3456910
  have hstable : (prefixWord ++ tailWord_3456910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456910).length < 2 ^ (prefixWord ++ tailWord_3456910).sum := by decide
  have hdescent : baseEnd_3456910 < baseStart_3456910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456925 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_3456925 : Nat := 118140960795 + 3456925 * 2 ^ 59
def prefixEnd_3456925 : Nat := 4983230072969 + 3 ^ 40 * 3456925 * 2
def baseEnd_3456925 : Nat := 1183376074362661665826265

theorem tailTrace_3456925 : CollatzResearch.WordTrace tailWord_3456925 prefixEnd_3456925 1183376074362661665826265 := by
  unfold tailWord_3456925
  simp only [CollatzResearch.WordTrace]
  refine ⟨126084413001158595631300229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84056275334105730420866819 126084413001158595631300229)
  ·
    refine ⟨23640827437717236680868793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126084413001158595631300229 23640827437717236680868793)
    ·
      refine ⟨17730620578287927510651595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23640827437717236680868793 17730620578287927510651595)
      ·
        refine ⟨26595930867431891265977393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17730620578287927510651595 26595930867431891265977393)
        ·
          refine ⟨19946948150573918449483045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26595930867431891265977393 19946948150573918449483045)
          ·
            refine ⟨3740052778232609709278071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19946948150573918449483045 3740052778232609709278071)
            ·
              refine ⟨5610079167348914563917107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740052778232609709278071 5610079167348914563917107)
              ·
                refine ⟨8415118751023371845875661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610079167348914563917107 8415118751023371845875661)
                ·
                  refine ⟨3155669531633764442203373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8415118751023371845875661 3155669531633764442203373)
                  ·
                    refine ⟨1183376074362661665826265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155669531633764442203373 1183376074362661665826265)
                    ·
                      rfl

theorem cell22_3456925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_3456925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456925 prefixEnd_3456925 := by exact prefixLift 3456925
  have htrace : WordTrace (prefixWord ++ tailWord_3456925) baseStart_3456925 baseEnd_3456925 := by
    simpa [prefixWord, tailWord_3456925, baseEnd_3456925] using wordTrace_append hprefix tailTrace_3456925
  have hstable : (prefixWord ++ tailWord_3456925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456925).length < 2 ^ (prefixWord ++ tailWord_3456925).sum := by decide
  have hdescent : baseEnd_3456925 < baseStart_3456925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456983 : List Nat := [1, 1, 3, 2, 1, 1, 5, 4, 4]
def baseStart_3456983 : Nat := 118140960795 + 3456983 * 2 ^ 59
def prefixEnd_3456983 : Nat := 4983230072969 + 3 ^ 40 * 3456983 * 2
def baseEnd_3456983 : Nat := 394465309649322949292029

theorem tailTrace_3456983 : CollatzResearch.WordTrace tailWord_3456983 prefixEnd_3456983 394465309649322949292029 := by
  unfold tailWord_3456983
  simp only [CollatzResearch.WordTrace]
  refine ⟨126086528434948471536911603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84057685623298981024607735 126086528434948471536911603)
  ·
    refine ⟨189129792652422707305367405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126086528434948471536911603 189129792652422707305367405)
    ·
      refine ⟨70923672244658515239512777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189129792652422707305367405 70923672244658515239512777)
      ·
        refine ⟨53192754183493886429634583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70923672244658515239512777 53192754183493886429634583)
        ·
          refine ⟨79789131275240829644451875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53192754183493886429634583 79789131275240829644451875)
          ·
            refine ⟨119683696912861244466677813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79789131275240829644451875 119683696912861244466677813)
            ·
              refine ⟨11220346585580741668751045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119683696912861244466677813 11220346585580741668751045)
              ·
                refine ⟨2103814984796389062890821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11220346585580741668751045 2103814984796389062890821)
                ·
                  refine ⟨394465309649322949292029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103814984796389062890821 394465309649322949292029)
                  ·
                    rfl

theorem cell22_3456983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 4].length) (baseStart_3456983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456983 prefixEnd_3456983 := by exact prefixLift 3456983
  have htrace : WordTrace (prefixWord ++ tailWord_3456983) baseStart_3456983 baseEnd_3456983 := by
    simpa [prefixWord, tailWord_3456983, baseEnd_3456983] using wordTrace_append hprefix tailTrace_3456983
  have hstable : (prefixWord ++ tailWord_3456983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456983).length < 2 ^ (prefixWord ++ tailWord_3456983).sum := by decide
  have hdescent : baseEnd_3456983 < baseStart_3456983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3456996 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_3456996 : Nat := 118140960795 + 3456996 * 2 ^ 59
def prefixEnd_3456996 : Nat := 4983230072969 + 3 ^ 40 * 3456996 * 2
def baseEnd_3456996 : Nat := 1183400379113641147301047

theorem tailTrace_3456996 : CollatzResearch.WordTrace tailWord_3456996 prefixEnd_3456996 1183400379113641147301047 := by
  unfold tailWord_3456996
  simp only [CollatzResearch.WordTrace]
  refine ⟨63043501291950687378567421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84058001722600916504756561 63043501291950687378567421)
  ·
    refine ⟨23641312984481507766962783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63043501291950687378567421 23641312984481507766962783)
    ·
      refine ⟨35461969476722261650444175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23641312984481507766962783 35461969476722261650444175)
      ·
        refine ⟨53192954215083392475666263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35461969476722261650444175 53192954215083392475666263)
        ·
          refine ⟨79789431322625088713499395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53192954215083392475666263 79789431322625088713499395)
          ·
            refine ⟨119684146983937633070249093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79789431322625088713499395 119684146983937633070249093)
            ·
              refine ⟨22440777559488306200671705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119684146983937633070249093 22440777559488306200671705)
              ·
                refine ⟨16830583169616229650503779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22440777559488306200671705 16830583169616229650503779)
                ·
                  refine ⟨25245874754424344475755669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16830583169616229650503779 25245874754424344475755669)
                  ·
                    refine ⟨1183400379113641147301047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25245874754424344475755669 1183400379113641147301047)
                    ·
                      rfl

theorem cell22_3456996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_3456996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3456996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3456996 prefixEnd_3456996 := by exact prefixLift 3456996
  have htrace : WordTrace (prefixWord ++ tailWord_3456996) baseStart_3456996 baseEnd_3456996 := by
    simpa [prefixWord, tailWord_3456996, baseEnd_3456996] using wordTrace_append hprefix tailTrace_3456996
  have hstable : (prefixWord ++ tailWord_3456996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3456996).length < 2 ^ (prefixWord ++ tailWord_3456996).sum := by decide
  have hdescent : baseEnd_3456996 < baseStart_3456996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3456996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457043 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 3, 3]
def baseStart_3457043 : Nat := 118140960795 + 3457043 * 2 ^ 59
def prefixEnd_3457043 : Nat := 4983230072969 + 3 ^ 40 * 3457043 * 2
def baseEnd_3457043 : Nat := 1183416468174148691375903

theorem tailTrace_3457043 : CollatzResearch.WordTrace tailWord_3457043 prefixEnd_3457043 1183416468174148691375903 := by
  unfold tailWord_3457043
  simp only [CollatzResearch.WordTrace]
  refine ⟨126088716814731101784095783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84059144543154067856063855 126088716814731101784095783)
  ·
    refine ⟨189133075222096652676143675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126088716814731101784095783 189133075222096652676143675)
    ·
      refine ⟨283699612833144979014215513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189133075222096652676143675 283699612833144979014215513)
      ·
        refine ⟨212774709624858734260661635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283699612833144979014215513 212774709624858734260661635)
        ·
          refine ⟨319162064437288101390992453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212774709624858734260661635 319162064437288101390992453)
          ·
            refine ⟨59842887081991519010811085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319162064437288101390992453 59842887081991519010811085)
            ·
              refine ⟨22441082655746819629054157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59842887081991519010811085 22441082655746819629054157)
              ·
                refine ⟨8415405995905057360895309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22441082655746819629054157 8415405995905057360895309)
                ·
                  refine ⟨3155777248464396510335741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8415405995905057360895309 3155777248464396510335741)
                  ·
                    refine ⟨1183416468174148691375903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155777248464396510335741 1183416468174148691375903)
                    ·
                      rfl

theorem cell22_3457043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 3].length) (baseStart_3457043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457043 prefixEnd_3457043 := by exact prefixLift 3457043
  have htrace : WordTrace (prefixWord ++ tailWord_3457043) baseStart_3457043 baseEnd_3457043 := by
    simpa [prefixWord, tailWord_3457043, baseEnd_3457043] using wordTrace_append hprefix tailTrace_3457043
  have hstable : (prefixWord ++ tailWord_3457043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457043).length < 2 ^ (prefixWord ++ tailWord_3457043).sum := by decide
  have hdescent : baseEnd_3457043 < baseStart_3457043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457071 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 4, 5]
def baseStart_3457071 : Nat := 118140960795 + 3457071 * 2 ^ 59
def prefixEnd_3457071 : Nat := 4983230072969 + 3 ^ 40 * 3457071 * 2
def baseEnd_3457071 : Nat := 1183426053146365951675817

theorem tailTrace_3457071 : CollatzResearch.WordTrace tailWord_3457071 prefixEnd_3457071 1183426053146365951675817 := by
  unfold tailWord_3457071
  simp only [CollatzResearch.WordTrace]
  refine ⟨126089738058629662566115067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84059825372419775044076711 126089738058629662566115067)
  ·
    refine ⟨189134607087944493849172601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126089738058629662566115067 189134607087944493849172601)
    ·
      refine ⟨141850955315958370386879451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189134607087944493849172601 141850955315958370386879451)
      ·
        refine ⟨212776432973937555580319177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141850955315958370386879451 212776432973937555580319177)
        ·
          refine ⟨159582324730453166685239383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212776432973937555580319177 159582324730453166685239383)
          ·
            refine ⟨239373487095679750027859075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159582324730453166685239383 239373487095679750027859075)
            ·
              refine ⟨359060230643519625041788613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239373487095679750027859075 359060230643519625041788613)
              ·
                refine ⟨67323793245659929695335365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359060230643519625041788613 67323793245659929695335365)
                ·
                  refine ⟨12623211233561236817875381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67323793245659929695335365 12623211233561236817875381)
                  ·
                    refine ⟨1183426053146365951675817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12623211233561236817875381 1183426053146365951675817)
                    ·
                      rfl

theorem cell22_3457071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_3457071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457071 prefixEnd_3457071 := by exact prefixLift 3457071
  have htrace : WordTrace (prefixWord ++ tailWord_3457071) baseStart_3457071 baseEnd_3457071 := by
    simpa [prefixWord, tailWord_3457071, baseEnd_3457071] using wordTrace_append hprefix tailTrace_3457071
  have hstable : (prefixWord ++ tailWord_3457071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457071).length < 2 ^ (prefixWord ++ tailWord_3457071).sum := by decide
  have hdescent : baseEnd_3457071 < baseStart_3457071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457077 : List Nat := [1, 3, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3457077 : Nat := 118140960795 + 3457077 * 2 ^ 59
def prefixEnd_3457077 : Nat := 4983230072969 + 3 ^ 40 * 3457077 * 2
def baseEnd_3457077 : Nat := 1183428107068983936025799

theorem tailTrace_3457077 : CollatzResearch.WordTrace tailWord_3457077 prefixEnd_3457077 1183428107068983936025799 := by
  unfold tailWord_3457077
  simp only [CollatzResearch.WordTrace]
  refine ⟨126089956896607925590833485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84059971264405283727222323 126089956896607925590833485)
  ·
    refine ⟨47283733836227972096562557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126089956896607925590833485 47283733836227972096562557)
    ·
      refine ⟨17731400188585489536210959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47283733836227972096562557 17731400188585489536210959)
      ·
        refine ⟨26597100282878234304316439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17731400188585489536210959 26597100282878234304316439)
        ·
          refine ⟨39895650424317351456474659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26597100282878234304316439 39895650424317351456474659)
          ·
            refine ⟨59843475636476027184711989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39895650424317351456474659 59843475636476027184711989)
            ·
              refine ⟨5610325840919627548566749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59843475636476027184711989 5610325840919627548566749)
              ·
                refine ⟨2103872190344860330712531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5610325840919627548566749 2103872190344860330712531)
                ·
                  refine ⟨3155808285517290496068797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103872190344860330712531 3155808285517290496068797)
                  ·
                    refine ⟨1183428107068983936025799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155808285517290496068797 1183428107068983936025799)
                    ·
                      rfl

theorem cell22_3457077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3457077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457077 prefixEnd_3457077 := by exact prefixLift 3457077
  have htrace : WordTrace (prefixWord ++ tailWord_3457077) baseStart_3457077 baseEnd_3457077 := by
    simpa [prefixWord, tailWord_3457077, baseEnd_3457077] using wordTrace_append hprefix tailTrace_3457077
  have hstable : (prefixWord ++ tailWord_3457077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457077).length < 2 ^ (prefixWord ++ tailWord_3457077).sum := by decide
  have hdescent : baseEnd_3457077 < baseStart_3457077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457120 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_3457120 : Nat := 118140960795 + 3457120 * 2 ^ 59
def prefixEnd_3457120 : Nat := 4983230072969 + 3 ^ 40 * 3457120 * 2
def baseEnd_3457120 : Nat := 1183442826847746157200667

theorem tailTrace_3457120 : CollatzResearch.WordTrace tailWord_3457120 prefixEnd_3457120 1183442826847746157200667 := by
  unfold tailWord_3457120
  simp only [CollatzResearch.WordTrace]
  refine ⟨63045762617726071967324407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84061016823634762623099209 63045762617726071967324407)
  ·
    refine ⟨94568643926589107950986611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63045762617726071967324407 94568643926589107950986611)
    ·
      refine ⟨141852965889883661926479917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94568643926589107950986611 141852965889883661926479917)
      ·
        refine ⟨53194862208706373222429969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141852965889883661926479917 53194862208706373222429969)
        ·
          refine ⟨39896146656529779916822477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53194862208706373222429969 39896146656529779916822477)
          ·
            refine ⟨14961054996198667468808429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39896146656529779916822477 14961054996198667468808429)
            ·
              refine ⟨5610395623574500300803161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14961054996198667468808429 5610395623574500300803161)
              ·
                refine ⟨4207796717680875225602371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5610395623574500300803161 4207796717680875225602371)
                ·
                  refine ⟨6311695076521312838403557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207796717680875225602371 6311695076521312838403557)
                  ·
                    refine ⟨1183442826847746157200667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6311695076521312838403557 1183442826847746157200667)
                    ·
                      rfl

theorem cell22_3457120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_3457120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457120 prefixEnd_3457120 := by exact prefixLift 3457120
  have htrace : WordTrace (prefixWord ++ tailWord_3457120) baseStart_3457120 baseEnd_3457120 := by
    simpa [prefixWord, tailWord_3457120, baseEnd_3457120] using wordTrace_append hprefix tailTrace_3457120
  have hstable : (prefixWord ++ tailWord_3457120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457120).length < 2 ^ (prefixWord ++ tailWord_3457120).sum := by decide
  have hdescent : baseEnd_3457120 < baseStart_3457120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457180 : List Nat := [2, 2, 3, 2, 1, 1, 5, 6]
def baseStart_3457180 : Nat := 118140960795 + 3457180 * 2 ^ 59
def prefixEnd_3457180 : Nat := 4983230072969 + 3 ^ 40 * 3457180 * 2
def baseEnd_3457180 : Nat := 131495929563769555633387

theorem tailTrace_3457180 : CollatzResearch.WordTrace tailWord_3457180 prefixEnd_3457180 131495929563769555633387 := by
  unfold tailWord_3457180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63046856807617387090916497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84062475743489849454555329 63046856807617387090916497)
  ·
    refine ⟨47285142605713040318187373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63046856807617387090916497 47285142605713040318187373)
    ·
      refine ⟨17731928477142390119320265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47285142605713040318187373 17731928477142390119320265)
      ·
        refine ⟨13298946357856792589490199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17731928477142390119320265 13298946357856792589490199)
        ·
          refine ⟨19948419536785188884235299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298946357856792589490199 19948419536785188884235299)
          ·
            refine ⟨29922629305177783326352949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19948419536785188884235299 29922629305177783326352949)
            ·
              refine ⟨2805246497360417186845589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29922629305177783326352949 2805246497360417186845589)
              ·
                refine ⟨131495929563769555633387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2805246497360417186845589 131495929563769555633387)
                ·
                  rfl

theorem cell22_3457180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 6].length) (baseStart_3457180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457180 prefixEnd_3457180 := by exact prefixLift 3457180
  have htrace : WordTrace (prefixWord ++ tailWord_3457180) baseStart_3457180 baseEnd_3457180 := by
    simpa [prefixWord, tailWord_3457180, baseEnd_3457180] using wordTrace_append hprefix tailTrace_3457180
  have hstable : (prefixWord ++ tailWord_3457180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457180).length < 2 ^ (prefixWord ++ tailWord_3457180).sum := by decide
  have hdescent : baseEnd_3457180 < baseStart_3457180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457182 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3457182 : Nat := 118140960795 + 3457182 * 2 ^ 59
def prefixEnd_3457182 : Nat := 4983230072969 + 3 ^ 40 * 3457182 * 2
def baseEnd_3457182 : Nat := 1183464050714798662150477

theorem tailTrace_3457182 : CollatzResearch.WordTrace tailWord_3457182 prefixEnd_3457182 1183464050714798662150477 := by
  unfold tailWord_3457182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15761723320153441065425725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84062524374151685682270533 15761723320153441065425725)
  ·
    refine ⟨5910646245057540399534647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15761723320153441065425725 5910646245057540399534647)
    ·
      refine ⟨8865969367586310599301971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910646245057540399534647 8865969367586310599301971)
      ·
        refine ⟨13298954051379465898952957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865969367586310599301971 13298954051379465898952957)
        ·
          refine ⟨4987107769267299712107359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13298954051379465898952957 4987107769267299712107359)
          ·
            refine ⟨7480661653900949568161039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987107769267299712107359 7480661653900949568161039)
            ·
              refine ⟨11220992480851424352241559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7480661653900949568161039 11220992480851424352241559)
              ·
                refine ⟨16831488721277136528362339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11220992480851424352241559 16831488721277136528362339)
                ·
                  refine ⟨25247233081915704792543509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16831488721277136528362339 25247233081915704792543509)
                  ·
                    refine ⟨1183464050714798662150477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25247233081915704792543509 1183464050714798662150477)
                    ·
                      rfl

theorem cell22_3457182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3457182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457182 prefixEnd_3457182 := by exact prefixLift 3457182
  have htrace : WordTrace (prefixWord ++ tailWord_3457182) baseStart_3457182 baseEnd_3457182 := by
    simpa [prefixWord, tailWord_3457182, baseEnd_3457182] using wordTrace_append hprefix tailTrace_3457182
  have hstable : (prefixWord ++ tailWord_3457182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457182).length < 2 ^ (prefixWord ++ tailWord_3457182).sum := by decide
  have hdescent : baseEnd_3457182 < baseStart_3457182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457201 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 2, 3]
def baseStart_3457201 : Nat := 118140960795 + 3457201 * 2 ^ 59
def prefixEnd_3457201 : Nat := 4983230072969 + 3 ^ 40 * 3457201 * 2
def baseEnd_3457201 : Nat := 1183470554803088945925419

theorem tailTrace_3457201 : CollatzResearch.WordTrace tailWord_3457201 prefixEnd_3457201 1183470554803088945925419 := by
  unfold tailWord_3457201
  simp only [CollatzResearch.WordTrace]
  refine ⟨126094479548158694768347457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84062986365439129845564971 126094479548158694768347457)
  ·
    refine ⟨94570859661119021076260593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126094479548158694768347457 94570859661119021076260593)
    ·
      refine ⟨70928144745839265807195445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94570859661119021076260593 70928144745839265807195445)
      ·
        refine ⟨6649513569922431169424573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70928144745839265807195445 6649513569922431169424573)
        ·
          refine ⟨2493567588720911688534215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6649513569922431169424573 2493567588720911688534215)
          ·
            refine ⟨3740351383081367532801323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493567588720911688534215 3740351383081367532801323)
            ·
              refine ⟨5610527074622051299201985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740351383081367532801323 5610527074622051299201985)
              ·
                refine ⟨4207895305966538474401489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5610527074622051299201985 4207895305966538474401489)
                ·
                  refine ⟨3155921479474903855801117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207895305966538474401489 3155921479474903855801117)
                  ·
                    refine ⟨1183470554803088945925419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155921479474903855801117 1183470554803088945925419)
                    ·
                      rfl

theorem cell22_3457201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_3457201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457201 prefixEnd_3457201 := by exact prefixLift 3457201
  have htrace : WordTrace (prefixWord ++ tailWord_3457201) baseStart_3457201 baseEnd_3457201 := by
    simpa [prefixWord, tailWord_3457201, baseEnd_3457201] using wordTrace_append hprefix tailTrace_3457201
  have hstable : (prefixWord ++ tailWord_3457201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457201).length < 2 ^ (prefixWord ++ tailWord_3457201).sum := by decide
  have hdescent : baseEnd_3457201 < baseStart_3457201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457208 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 7]
def baseStart_3457208 : Nat := 118140960795 + 3457208 * 2 ^ 59
def prefixEnd_3457208 : Nat := 4983230072969 + 3 ^ 40 * 3457208 * 2
def baseEnd_3457208 : Nat := 394490983682047753666799

theorem tailTrace_3457208 : CollatzResearch.WordTrace tailWord_3457208 prefixEnd_3457208 394490983682047753666799 := by
  unfold tailWord_3457208
  simp only [CollatzResearch.WordTrace]
  refine ⟨63047367429566667481926139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84063156572755556642568185 63047367429566667481926139)
  ·
    refine ⟨94571051144350001222889209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63047367429566667481926139 94571051144350001222889209)
    ·
      refine ⟨70928288358262500917166907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94571051144350001222889209 70928288358262500917166907)
      ·
        refine ⟨106392432537393751375750361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70928288358262500917166907 106392432537393751375750361)
        ·
          refine ⟨79794324403045313531812771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106392432537393751375750361 79794324403045313531812771)
          ·
            refine ⟨119691486604567970297719157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79794324403045313531812771 119691486604567970297719157)
            ·
              refine ⟨11221076869178247215411171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119691486604567970297719157 11221076869178247215411171)
              ·
                refine ⟨16831615303767370823116757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11221076869178247215411171 16831615303767370823116757)
                ·
                  refine ⟨394490983682047753666799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16831615303767370823116757 394490983682047753666799)
                  ·
                    rfl

theorem cell22_3457208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_3457208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457208 prefixEnd_3457208 := by exact prefixLift 3457208
  have htrace : WordTrace (prefixWord ++ tailWord_3457208) baseStart_3457208 baseEnd_3457208 := by
    simpa [prefixWord, tailWord_3457208, baseEnd_3457208] using wordTrace_append hprefix tailTrace_3457208
  have hstable : (prefixWord ++ tailWord_3457208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457208).length < 2 ^ (prefixWord ++ tailWord_3457208).sum := by decide
  have hdescent : baseEnd_3457208 < baseStart_3457208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457218 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3457218 : Nat := 118140960795 + 3457218 * 2 ^ 59
def prefixEnd_3457218 : Nat := 4983230072969 + 3 ^ 40 * 3457218 * 2
def baseEnd_3457218 : Nat := 1183476374250506568250367

theorem tailTrace_3457218 : CollatzResearch.WordTrace tailWord_3457218 prefixEnd_3457218 1183476374250506568250367 := by
  unfold tailWord_3457218
  simp only [CollatzResearch.WordTrace]
  refine ⟨31523774897274276667929077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84063399726064737781144205 31523774897274276667929077)
  ·
    refine ⟨2955353896619463437618351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31523774897274276667929077 2955353896619463437618351)
    ·
      refine ⟨4433030844929195156427527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2955353896619463437618351 4433030844929195156427527)
      ·
        refine ⟨6649546267393792734641291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4433030844929195156427527 6649546267393792734641291)
        ·
          refine ⟨9974319401090689101961937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6649546267393792734641291 9974319401090689101961937)
          ·
            refine ⟨7480739550818016826471453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9974319401090689101961937 7480739550818016826471453)
            ·
              refine ⟨2805277331556756309926795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7480739550818016826471453 2805277331556756309926795)
              ·
                refine ⟨4207915997335134464890193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805277331556756309926795 4207915997335134464890193)
                ·
                  refine ⟨3155936998001350848667645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207915997335134464890193 3155936998001350848667645)
                  ·
                    refine ⟨1183476374250506568250367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155936998001350848667645 1183476374250506568250367)
                    ·
                      rfl

theorem cell22_3457218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3457218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457218 prefixEnd_3457218 := by exact prefixLift 3457218
  have htrace : WordTrace (prefixWord ++ tailWord_3457218) baseStart_3457218 baseEnd_3457218 := by
    simpa [prefixWord, tailWord_3457218, baseEnd_3457218] using wordTrace_append hprefix tailTrace_3457218
  have hstable : (prefixWord ++ tailWord_3457218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457218).length < 2 ^ (prefixWord ++ tailWord_3457218).sum := by decide
  have hdescent : baseEnd_3457218 < baseStart_3457218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457285 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_3457285 : Nat := 118140960795 + 3457285 * 2 ^ 59
def prefixEnd_3457285 : Nat := 4983230072969 + 3 ^ 40 * 3457285 * 2
def baseEnd_3457285 : Nat := 1183499309719740726825161

theorem tailTrace_3457285 : CollatzResearch.WordTrace tailWord_3457285 prefixEnd_3457285 1183499309719740726825161 := by
  unfold tailWord_3457285
  simp only [CollatzResearch.WordTrace]
  refine ⟨126097543279854377114405309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84065028853236251409603539 126097543279854377114405309)
  ·
    refine ⟨47286578729945391417901991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126097543279854377114405309 47286578729945391417901991)
    ·
      refine ⟨70929868094918087126852987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47286578729945391417901991 70929868094918087126852987)
      ·
        refine ⟨106394802142377130690279481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70929868094918087126852987 106394802142377130690279481)
        ·
          refine ⟨79796101606782848017709611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106394802142377130690279481 79796101606782848017709611)
          ·
            refine ⟨119694152410174272026564417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79796101606782848017709611 119694152410174272026564417)
            ·
              refine ⟨89770614307630704019923313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119694152410174272026564417 89770614307630704019923313)
              ·
                refine ⟨67327960730723028014942485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89770614307630704019923313 67327960730723028014942485)
                ·
                  refine ⟨3155998159252641938200429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67327960730723028014942485 3155998159252641938200429)
                  ·
                    refine ⟨1183499309719740726825161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3155998159252641938200429 1183499309719740726825161)
                    ·
                      rfl

theorem cell22_3457285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_3457285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457285 prefixEnd_3457285 := by exact prefixLift 3457285
  have htrace : WordTrace (prefixWord ++ tailWord_3457285) baseStart_3457285 baseEnd_3457285 := by
    simpa [prefixWord, tailWord_3457285, baseEnd_3457285] using wordTrace_append hprefix tailTrace_3457285
  have hstable : (prefixWord ++ tailWord_3457285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457285).length < 2 ^ (prefixWord ++ tailWord_3457285).sum := by decide
  have hdescent : baseEnd_3457285 < baseStart_3457285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457332 : List Nat := [2, 5, 1, 1, 1, 2, 3, 7]
def baseStart_3457332 : Nat := 118140960795 + 3457332 * 2 ^ 59
def prefixEnd_3457332 : Nat := 4983230072969 + 3 ^ 40 * 3457332 * 2
def baseEnd_3457332 : Nat := 131501710975583141211113

theorem tailTrace_3457332 : CollatzResearch.WordTrace tailWord_3457332 prefixEnd_3457332 131501710975583141211113 := by
  unfold tailWord_3457332
  simp only [CollatzResearch.WordTrace]
  refine ⟨63049628755342052070683125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84066171673789402760910833 63049628755342052070683125)
  ·
    refine ⟨5910902695813317381626543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63049628755342052070683125 5910902695813317381626543)
    ·
      refine ⟨8866354043719976072439815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910902695813317381626543 8866354043719976072439815)
      ·
        refine ⟨13299531065579964108659723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8866354043719976072439815 13299531065579964108659723)
        ·
          refine ⟨19949296598369946162989585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13299531065579964108659723 19949296598369946162989585)
          ·
            refine ⟨14961972448777459622242189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19949296598369946162989585 14961972448777459622242189)
            ·
              refine ⟨5610739668291547358340821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14961972448777459622242189 5610739668291547358340821)
              ·
                refine ⟨131501710975583141211113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5610739668291547358340821 131501710975583141211113)
                ·
                  rfl

theorem cell22_3457332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 7].length) (baseStart_3457332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457332 prefixEnd_3457332 := by exact prefixLift 3457332
  have htrace : WordTrace (prefixWord ++ tailWord_3457332) baseStart_3457332 baseEnd_3457332 := by
    simpa [prefixWord, tailWord_3457332, baseEnd_3457332] using wordTrace_append hprefix tailTrace_3457332
  have hstable : (prefixWord ++ tailWord_3457332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457332).length < 2 ^ (prefixWord ++ tailWord_3457332).sum := by decide
  have hdescent : baseEnd_3457332 < baseStart_3457332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457375 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 2, 5]
def baseStart_3457375 : Nat := 118140960795 + 3457375 * 2 ^ 59
def prefixEnd_3457375 : Nat := 4983230072969 + 3 ^ 40 * 3457375 * 2
def baseEnd_3457375 : Nat := 1183530118559010492074885

theorem tailTrace_3457375 : CollatzResearch.WordTrace tailWord_3457375 prefixEnd_3457375 1183530118559010492074885 := by
  unfold tailWord_3457375
  simp only [CollatzResearch.WordTrace]
  refine ⟨126100825849528322485181579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84067217233018881656787719 126100825849528322485181579)
  ·
    refine ⟨189151238774292483727772369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126100825849528322485181579 189151238774292483727772369)
    ·
      refine ⟨141863429080719362795829277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189151238774292483727772369 141863429080719362795829277)
      ·
        refine ⟨53198785905269761048435979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141863429080719362795829277 53198785905269761048435979)
        ·
          refine ⟨79798178857904641572653969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53198785905269761048435979 79798178857904641572653969)
          ·
            refine ⟨59848634143428481179490477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79798178857904641572653969 59848634143428481179490477)
            ·
              refine ⟨22443237803785680442308929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59848634143428481179490477 22443237803785680442308929)
              ·
                refine ⟨16832428352839260331731697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22443237803785680442308929 16832428352839260331731697)
                ·
                  refine ⟨12624321264629445248798773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16832428352839260331731697 12624321264629445248798773)
                  ·
                    refine ⟨1183530118559010492074885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12624321264629445248798773 1183530118559010492074885)
                    ·
                      rfl

theorem cell22_3457375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_3457375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457375 prefixEnd_3457375 := by exact prefixLift 3457375
  have htrace : WordTrace (prefixWord ++ tailWord_3457375) baseStart_3457375 baseEnd_3457375 := by
    simpa [prefixWord, tailWord_3457375, baseEnd_3457375] using wordTrace_append hprefix tailTrace_3457375
  have hstable : (prefixWord ++ tailWord_3457375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457375).length < 2 ^ (prefixWord ++ tailWord_3457375).sum := by decide
  have hdescent : baseEnd_3457375 < baseStart_3457375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457394 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_3457394 : Nat := 118140960795 + 3457394 * 2 ^ 59
def prefixEnd_3457394 : Nat := 4983230072969 + 3 ^ 40 * 3457394 * 2
def baseEnd_3457394 : Nat := 394512207549100258616609

theorem tailTrace_3457394 : CollatzResearch.WordTrace tailWord_3457394 prefixEnd_3457394 394512207549100258616609 := by
  unfold tailWord_3457394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31525379709114872182530809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84067679224306325820082157 31525379709114872182530809)
  ·
    refine ⟨23644034781836154136898107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31525379709114872182530809 23644034781836154136898107)
    ·
      refine ⟨35466052172754231205347161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23644034781836154136898107 35466052172754231205347161)
      ·
        refine ⟨26599539129565673404010371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35466052172754231205347161 26599539129565673404010371)
        ·
          refine ⟨39899308694348510106015557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26599539129565673404010371 39899308694348510106015557)
          ·
            refine ⟨7481120380190345644877917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39899308694348510106015557 7481120380190345644877917)
            ·
              refine ⟨2805420142571379616829219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7481120380190345644877917 2805420142571379616829219)
              ·
                refine ⟨4208130213857069425243829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805420142571379616829219 4208130213857069425243829)
                ·
                  refine ⟨394512207549100258616609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4208130213857069425243829 394512207549100258616609)
                  ·
                    rfl

theorem cell22_3457394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_3457394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457394 prefixEnd_3457394 := by exact prefixLift 3457394
  have htrace : WordTrace (prefixWord ++ tailWord_3457394) baseStart_3457394 baseEnd_3457394 := by
    simpa [prefixWord, tailWord_3457394, baseEnd_3457394] using wordTrace_append hprefix tailTrace_3457394
  have hstable : (prefixWord ++ tailWord_3457394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457394).length < 2 ^ (prefixWord ++ tailWord_3457394).sum := by decide
  have hdescent : baseEnd_3457394 < baseStart_3457394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457469 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_3457469 : Nat := 118140960795 + 3457469 * 2 ^ 59
def prefixEnd_3457469 : Nat := 4983230072969 + 3 ^ 40 * 3457469 * 2
def baseEnd_3457469 : Nat := 1183562296680025580224597

theorem tailTrace_3457469 : CollatzResearch.WordTrace tailWord_3457469 prefixEnd_3457469 1183562296680025580224597 := by
  unfold tailWord_3457469
  simp only [CollatzResearch.WordTrace]
  refine ⟨126104254311187776539103461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84069502874125184359402307 126104254311187776539103461)
  ·
    refine ⟨23644547683347708101081899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126104254311187776539103461 23644547683347708101081899)
    ·
      refine ⟨35466821525021562151622849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23644547683347708101081899 35466821525021562151622849)
      ·
        refine ⟨26600116143766171613717137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35466821525021562151622849 26600116143766171613717137)
        ·
          refine ⟨19950087107824628710287853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26600116143766171613717137 19950087107824628710287853)
          ·
            refine ⟨7481282665434235766357945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19950087107824628710287853 7481282665434235766357945)
            ·
              refine ⟨5610961999075676824768459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7481282665434235766357945 5610961999075676824768459)
              ·
                refine ⟨8416442998613515237152689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610961999075676824768459 8416442998613515237152689)
                ·
                  refine ⟨6312332248960136427864517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8416442998613515237152689 6312332248960136427864517)
                  ·
                    refine ⟨1183562296680025580224597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6312332248960136427864517 1183562296680025580224597)
                    ·
                      rfl

theorem cell22_3457469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_3457469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457469 prefixEnd_3457469 := by exact prefixLift 3457469
  have htrace : WordTrace (prefixWord ++ tailWord_3457469) baseStart_3457469 baseEnd_3457469 := by
    simpa [prefixWord, tailWord_3457469, baseEnd_3457469] using wordTrace_append hprefix tailTrace_3457469
  have hstable : (prefixWord ++ tailWord_3457469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457469).length < 2 ^ (prefixWord ++ tailWord_3457469).sum := by decide
  have hdescent : baseEnd_3457469 < baseStart_3457469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457490 : List Nat := [3, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_3457490 : Nat := 118140960795 + 3457490 * 2 ^ 59
def prefixEnd_3457490 : Nat := 4983230072969 + 3 ^ 40 * 3457490 * 2
def baseEnd_3457490 : Nat := 394523161803062841816511

theorem tailTrace_3457490 : CollatzResearch.WordTrace tailWord_3457490 prefixEnd_3457490 394523161803062841816511 := by
  unfold tailWord_3457490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31526255061027924281404481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84070013496074464750411949 31526255061027924281404481)
  ·
    refine ⟨23644691295770943211053361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31526255061027924281404481 23644691295770943211053361)
    ·
      refine ⟨17733518471828207408290021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23644691295770943211053361 17733518471828207408290021)
      ·
        refine ⟨3325034713467788889054379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17733518471828207408290021 3325034713467788889054379)
        ·
          refine ⟨4987552070201683333581569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325034713467788889054379 4987552070201683333581569)
          ·
            refine ⟨3740664052651262500186177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987552070201683333581569 3740664052651262500186177)
            ·
              refine ⟨2805498039488446875139633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3740664052651262500186177 2805498039488446875139633)
              ·
                refine ⟨2104123529616335156354725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805498039488446875139633 2104123529616335156354725)
                ·
                  refine ⟨394523161803062841816511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2104123529616335156354725 394523161803062841816511)
                  ·
                    rfl

theorem cell22_3457490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_3457490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457490 prefixEnd_3457490 := by exact prefixLift 3457490
  have htrace : WordTrace (prefixWord ++ tailWord_3457490) baseStart_3457490 baseEnd_3457490 := by
    simpa [prefixWord, tailWord_3457490, baseEnd_3457490] using wordTrace_append hprefix tailTrace_3457490
  have hstable : (prefixWord ++ tailWord_3457490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457490).length < 2 ^ (prefixWord ++ tailWord_3457490).sum := by decide
  have hdescent : baseEnd_3457490 < baseStart_3457490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457576 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3457576 : Nat := 118140960795 + 3457576 * 2 ^ 59
def prefixEnd_3457576 : Nat := 4983230072969 + 3 ^ 40 * 3457576 * 2
def baseEnd_3457576 : Nat := 1183598924966712967799269

theorem tailTrace_3457576 : CollatzResearch.WordTrace tailWord_3457576 prefixEnd_3457576 1183598924966712967799269 := by
  unfold tailWord_3457576
  simp only [CollatzResearch.WordTrace]
  refine ⟨63054078460900066906624291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84072104614533422542165721 63054078460900066906624291)
  ·
    refine ⟨94581117691350100359936437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63054078460900066906624291 94581117691350100359936437)
    ·
      refine ⟨8866979783564071908744041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94581117691350100359936437 8866979783564071908744041)
      ·
        refine ⟨6650234837673053931558031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8866979783564071908744041 6650234837673053931558031)
        ·
          refine ⟨9975352256509580897337047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6650234837673053931558031 9975352256509580897337047)
          ·
            refine ⟨14963028384764371346005571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9975352256509580897337047 14963028384764371346005571)
            ·
              refine ⟨22444542577146557019008357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14963028384764371346005571 22444542577146557019008357)
              ·
                refine ⟨4208351733214979441064067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22444542577146557019008357 4208351733214979441064067)
                ·
                  refine ⟨6312527599822469161596101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208351733214979441064067 6312527599822469161596101)
                  ·
                    refine ⟨1183598924966712967799269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6312527599822469161596101 1183598924966712967799269)
                    ·
                      rfl

theorem cell22_3457576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3457576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457576 prefixEnd_3457576 := by exact prefixLift 3457576
  have htrace : WordTrace (prefixWord ++ tailWord_3457576) baseStart_3457576 baseEnd_3457576 := by
    simpa [prefixWord, tailWord_3457576, baseEnd_3457576] using wordTrace_append hprefix tailTrace_3457576
  have hstable : (prefixWord ++ tailWord_3457576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457576).length < 2 ^ (prefixWord ++ tailWord_3457576).sum := by decide
  have hdescent : baseEnd_3457576 < baseStart_3457576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457587 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 1, 6]
def baseStart_3457587 : Nat := 118140960795 + 3457587 * 2 ^ 59
def prefixEnd_3457587 : Nat := 4983230072969 + 3 ^ 40 * 3457587 * 2
def baseEnd_3457587 : Nat := 1183602690491512605774235

theorem tailTrace_3457587 : CollatzResearch.WordTrace tailWord_3457587 prefixEnd_3457587 1183602690491512605774235 := by
  unfold tailWord_3457587
  simp only [CollatzResearch.WordTrace]
  refine ⟨126108558124760282691899015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84072372083173521794599343 126108558124760282691899015)
  ·
    refine ⟨189162837187140424037848523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126108558124760282691899015 189162837187140424037848523)
    ·
      refine ⟨283744255780710636056772785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189162837187140424037848523 283744255780710636056772785)
      ·
        refine ⟨212808191835532977042579589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283744255780710636056772785 212808191835532977042579589)
        ·
          refine ⟨39901535969162433195483673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212808191835532977042579589 39901535969162433195483673)
          ·
            refine ⟨29926151976871824896612755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39901535969162433195483673 29926151976871824896612755)
            ·
              refine ⟨44889227965307737344919133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29926151976871824896612755 44889227965307737344919133)
              ·
                refine ⟨16833460486990401504344675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44889227965307737344919133 16833460486990401504344675)
                ·
                  refine ⟨25250190730485602256517013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16833460486990401504344675 25250190730485602256517013)
                  ·
                    refine ⟨1183602690491512605774235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25250190730485602256517013 1183602690491512605774235)
                    ·
                      rfl

theorem cell22_3457587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_3457587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457587 prefixEnd_3457587 := by exact prefixLift 3457587
  have htrace : WordTrace (prefixWord ++ tailWord_3457587) baseStart_3457587 baseEnd_3457587 := by
    simpa [prefixWord, tailWord_3457587, baseEnd_3457587] using wordTrace_append hprefix tailTrace_3457587
  have hstable : (prefixWord ++ tailWord_3457587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457587).length < 2 ^ (prefixWord ++ tailWord_3457587).sum := by decide
  have hdescent : baseEnd_3457587 < baseStart_3457587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457589 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3457589 : Nat := 118140960795 + 3457589 * 2 ^ 59
def prefixEnd_3457589 : Nat := 4983230072969 + 3 ^ 40 * 3457589 * 2
def baseEnd_3457589 : Nat := 1183603375132385267224229

theorem tailTrace_3457589 : CollatzResearch.WordTrace tailWord_3457589 prefixEnd_3457589 1183603375132385267224229 := by
  unfold tailWord_3457589
  simp only [CollatzResearch.WordTrace]
  refine ⟨126108631070753037033471821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84072420713835358022314547 126108631070753037033471821)
  ·
    refine ⟨47290736651532388887551933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126108631070753037033471821 47290736651532388887551933)
    ·
      refine ⟨17734026244324645832831975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47290736651532388887551933 17734026244324645832831975)
      ·
        refine ⟨26601039366486968749247963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17734026244324645832831975 26601039366486968749247963)
        ·
          refine ⟨39901559049730453123871945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26601039366486968749247963 39901559049730453123871945)
          ·
            refine ⟨29926169287297839842903959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39901559049730453123871945 29926169287297839842903959)
            ·
              refine ⟨44889253930946759764355939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29926169287297839842903959 44889253930946759764355939)
              ·
                refine ⟨67333880896420139646533909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44889253930946759764355939 67333880896420139646533909)
                ·
                  refine ⟨3156275667019694045931277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67333880896420139646533909 3156275667019694045931277)
                  ·
                    refine ⟨1183603375132385267224229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3156275667019694045931277 1183603375132385267224229)
                    ·
                      rfl

theorem cell22_3457589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3457589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457589 prefixEnd_3457589 := by exact prefixLift 3457589
  have htrace : WordTrace (prefixWord ++ tailWord_3457589) baseStart_3457589 baseEnd_3457589 := by
    simpa [prefixWord, tailWord_3457589, baseEnd_3457589] using wordTrace_append hprefix tailTrace_3457589
  have hstable : (prefixWord ++ tailWord_3457589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457589).length < 2 ^ (prefixWord ++ tailWord_3457589).sum := by decide
  have hdescent : baseEnd_3457589 < baseStart_3457589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457647 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 9]
def baseStart_3457647 : Nat := 118140960795 + 3457647 * 2 ^ 59
def prefixEnd_3457647 : Nat := 4983230072969 + 3 ^ 40 * 3457647 * 2
def baseEnd_3457647 : Nat := 394541076572564149758017

theorem tailTrace_3457647 : CollatzResearch.WordTrace tailWord_3457647 prefixEnd_3457647 394541076572564149758017 := by
  unfold tailWord_3457647
  simp only [CollatzResearch.WordTrace]
  refine ⟨126110746504542912939083195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84073831003028608626055463 126110746504542912939083195)
  ·
    refine ⟨189166119756814369408624793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126110746504542912939083195 189166119756814369408624793)
    ·
      refine ⟨141874589817610777056468595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189166119756814369408624793 141874589817610777056468595)
      ·
        refine ⟨212811884726416165584702893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141874589817610777056468595 212811884726416165584702893)
        ·
          refine ⟨79804456772406062094263585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212811884726416165584702893 79804456772406062094263585)
          ·
            refine ⟨59853342579304546570697689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79804456772406062094263585 59853342579304546570697689)
            ·
              refine ⟨44890006934478409928023267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59853342579304546570697689 44890006934478409928023267)
              ·
                refine ⟨67335010401717614892034901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44890006934478409928023267 67335010401717614892034901)
                ·
                  refine ⟨394541076572564149758017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67335010401717614892034901 394541076572564149758017)
                  ·
                    rfl

theorem cell22_3457647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 9].length) (baseStart_3457647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457647 prefixEnd_3457647 := by exact prefixLift 3457647
  have htrace : WordTrace (prefixWord ++ tailWord_3457647) baseStart_3457647 baseEnd_3457647 := by
    simpa [prefixWord, tailWord_3457647, baseEnd_3457647] using wordTrace_append hprefix tailTrace_3457647
  have hstable : (prefixWord ++ tailWord_3457647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457647).length < 2 ^ (prefixWord ++ tailWord_3457647).sum := by decide
  have hdescent : baseEnd_3457647 < baseStart_3457647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457664 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 5]
def baseStart_3457664 : Nat := 118140960795 + 3457664 * 2 ^ 59
def prefixEnd_3457664 : Nat := 4983230072969 + 3 ^ 40 * 3457664 * 2
def baseEnd_3457664 : Nat := 394543016388370023866333

theorem tailTrace_3457664 : CollatzResearch.WordTrace tailWord_3457664 prefixEnd_3457664 394543016388370023866333 := by
  unfold tailWord_3457664
  simp only [CollatzResearch.WordTrace]
  refine ⟨63055683272740662421226023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84074244363654216561634697 63055683272740662421226023)
  ·
    refine ⟨94583524909110993631839035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63055683272740662421226023 94583524909110993631839035)
    ·
      refine ⟨141875287363666490447758553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94583524909110993631839035 141875287363666490447758553)
      ·
        refine ⟨106406465522749867835818915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141875287363666490447758553 106406465522749867835818915)
        ·
          refine ⟨159609698284124801753728373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106406465522749867835818915 159609698284124801753728373)
          ·
            refine ⟨14963409214136700164412035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159609698284124801753728373 14963409214136700164412035)
            ·
              refine ⟨22445113821205050246618053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14963409214136700164412035 22445113821205050246618053)
              ·
                refine ⟨4208458841475946921240885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22445113821205050246618053 4208458841475946921240885)
                ·
                  refine ⟨394543016388370023866333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4208458841475946921240885 394543016388370023866333)
                  ·
                    rfl

theorem cell22_3457664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_3457664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457664 prefixEnd_3457664 := by exact prefixLift 3457664
  have htrace : WordTrace (prefixWord ++ tailWord_3457664) baseStart_3457664 baseEnd_3457664 := by
    simpa [prefixWord, tailWord_3457664, baseEnd_3457664] using wordTrace_append hprefix tailTrace_3457664
  have hstable : (prefixWord ++ tailWord_3457664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457664).length < 2 ^ (prefixWord ++ tailWord_3457664).sum := by decide
  have hdescent : baseEnd_3457664 < baseStart_3457664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457711 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 1, 4]
def baseStart_3457711 : Nat := 118140960795 + 3457711 * 2 ^ 59
def prefixEnd_3457711 : Nat := 4983230072969 + 3 ^ 40 * 3457711 * 2
def baseEnd_3457711 : Nat := 1183645138225617615673855

theorem tailTrace_3457711 : CollatzResearch.WordTrace tailWord_3457711 prefixEnd_3457711 1183645138225617615673855 := by
  unfold tailWord_3457711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126113080776311051869412987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84075387184207367912941991 126113080776311051869412987)
  ·
    refine ⟨189169621164466577804119481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126113080776311051869412987 189169621164466577804119481)
    ·
      refine ⟨141877215873349933353089611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189169621164466577804119481 141877215873349933353089611)
      ·
        refine ⟨212815823810024900029634417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141877215873349933353089611 212815823810024900029634417)
        ·
          refine ⟨159611867857518675022225813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212815823810024900029634417 159611867857518675022225813)
          ·
            refine ⟨7481806305821187891666835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159611867857518675022225813 7481806305821187891666835)
            ·
              refine ⟨11222709458731781837500253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7481806305821187891666835 11222709458731781837500253)
              ·
                refine ⟨4208516047024418189062595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11222709458731781837500253 4208516047024418189062595)
                ·
                  refine ⟨6312774070536627283593893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208516047024418189062595 6312774070536627283593893)
                  ·
                    refine ⟨1183645138225617615673855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6312774070536627283593893 1183645138225617615673855)
                    ·
                      rfl

theorem cell22_3457711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_3457711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457711 prefixEnd_3457711 := by exact prefixLift 3457711
  have htrace : WordTrace (prefixWord ++ tailWord_3457711) baseStart_3457711 baseEnd_3457711 := by
    simpa [prefixWord, tailWord_3457711, baseEnd_3457711] using wordTrace_append hprefix tailTrace_3457711
  have hstable : (prefixWord ++ tailWord_3457711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457711).length < 2 ^ (prefixWord ++ tailWord_3457711).sum := by decide
  have hdescent : baseEnd_3457711 < baseStart_3457711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457726 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3457726 : Nat := 118140960795 + 3457726 * 2 ^ 59
def prefixEnd_3457726 : Nat := 4983230072969 + 3 ^ 40 * 3457726 * 2
def baseEnd_3457726 : Nat := 394550091010720858849603

theorem tailTrace_3457726 : CollatzResearch.WordTrace tailWord_3457726 prefixEnd_3457726 394550091010720858849603 := by
  unfold tailWord_3457726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15764203483907088678901129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84075751914171139620806021 15764203483907088678901129)
  ·
    refine ⟨11823152612930316509175847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15764203483907088678901129 11823152612930316509175847)
    ·
      refine ⟨17734728919395474763763771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823152612930316509175847 17734728919395474763763771)
      ·
        refine ⟨26602093379093212145645657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17734728919395474763763771 26602093379093212145645657)
        ·
          refine ⟨19951570034319909109234243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26602093379093212145645657 19951570034319909109234243)
          ·
            refine ⟨29927355051479863663851365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19951570034319909109234243 29927355051479863663851365)
            ·
              refine ⟨5611379072152474436972131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29927355051479863663851365 5611379072152474436972131)
              ·
                refine ⟨8417068608228711655458197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611379072152474436972131 8417068608228711655458197)
                ·
                  refine ⟨394550091010720858849603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8417068608228711655458197 394550091010720858849603)
                  ·
                    rfl

theorem cell22_3457726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3457726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457726 prefixEnd_3457726 := by exact prefixLift 3457726
  have htrace : WordTrace (prefixWord ++ tailWord_3457726) baseStart_3457726 baseEnd_3457726 := by
    simpa [prefixWord, tailWord_3457726, baseEnd_3457726] using wordTrace_append hprefix tailTrace_3457726
  have hstable : (prefixWord ++ tailWord_3457726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457726).length < 2 ^ (prefixWord ++ tailWord_3457726).sum := by decide
  have hdescent : baseEnd_3457726 < baseStart_3457726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457754 : List Nat := [3, 1, 1, 2, 2, 2, 3, 8]
def baseStart_3457754 : Nat := 118140960795 + 3457754 * 2 ^ 59
def prefixEnd_3457754 : Nat := 4983230072969 + 3 ^ 40 * 3457754 * 2
def baseEnd_3457754 : Nat := 131517762000486648538747

theorem tailTrace_3457754 : CollatzResearch.WordTrace tailWord_3457754 prefixEnd_3457754 131517762000486648538747 := by
  unfold tailWord_3457754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31528662278788817553307079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84076432743436846808818877 31528662278788817553307079)
  ·
    refine ⟨47292993418183226329960619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31528662278788817553307079 47292993418183226329960619)
    ·
      refine ⟨70939490127274839494940929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47292993418183226329960619 70939490127274839494940929)
      ·
        refine ⟨53204617595456129621205697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70939490127274839494940929 53204617595456129621205697)
        ·
          refine ⟨39903463196592097215904273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53204617595456129621205697 39903463196592097215904273)
          ·
            refine ⟨29927597397444072911928205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39903463196592097215904273 29927597397444072911928205)
            ·
              refine ⟨11222849024041527341973077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29927597397444072911928205 11222849024041527341973077)
              ·
                refine ⟨131517762000486648538747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11222849024041527341973077 131517762000486648538747)
                ·
                  rfl

theorem cell22_3457754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_3457754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457754 prefixEnd_3457754 := by exact prefixLift 3457754
  have htrace : WordTrace (prefixWord ++ tailWord_3457754) baseStart_3457754 baseEnd_3457754 := by
    simpa [prefixWord, tailWord_3457754, baseEnd_3457754] using wordTrace_append hprefix tailTrace_3457754
  have hstable : (prefixWord ++ tailWord_3457754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457754).length < 2 ^ (prefixWord ++ tailWord_3457754).sum := by decide
  have hdescent : baseEnd_3457754 < baseStart_3457754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457784 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_3457784 : Nat := 118140960795 + 3457784 * 2 ^ 59
def prefixEnd_3457784 : Nat := 4983230072969 + 3 ^ 40 * 3457784 * 2
def baseEnd_3457784 : Nat := 1183670127617469758598631

theorem tailTrace_3457784 : CollatzResearch.WordTrace tailWord_3457784 prefixEnd_3457784 1183670127617469758598631 := by
  unfold tailWord_3457784
  simp only [CollatzResearch.WordTrace]
  refine ⟨63057871652523292668410203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84077162203364390224546937 63057871652523292668410203)
  ·
    refine ⟨94586807478784939002615305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63057871652523292668410203 94586807478784939002615305)
    ·
      refine ⟨70940105609088704251961479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94586807478784939002615305 70940105609088704251961479)
      ·
        refine ⟨106410158413633056377942219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70940105609088704251961479 106410158413633056377942219)
        ·
          refine ⟨159615237620449584566913329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106410158413633056377942219 159615237620449584566913329)
          ·
            refine ⟨119711428215337188425184997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159615237620449584566913329 119711428215337188425184997)
            ·
              refine ⟨22445892790375722829722187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119711428215337188425184997 22445892790375722829722187)
              ·
                refine ⟨33668839185563584244583281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22445892790375722829722187 33668839185563584244583281)
                ·
                  refine ⟨25251629389172688183437461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33668839185563584244583281 25251629389172688183437461)
                  ·
                    refine ⟨1183670127617469758598631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25251629389172688183437461 1183670127617469758598631)
                    ·
                      rfl

theorem cell22_3457784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_3457784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457784 prefixEnd_3457784 := by exact prefixLift 3457784
  have htrace : WordTrace (prefixWord ++ tailWord_3457784) baseStart_3457784 baseEnd_3457784 := by
    simpa [prefixWord, tailWord_3457784, baseEnd_3457784] using wordTrace_append hprefix tailTrace_3457784
  have hstable : (prefixWord ++ tailWord_3457784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457784).length < 2 ^ (prefixWord ++ tailWord_3457784).sum := by decide
  have hdescent : baseEnd_3457784 < baseStart_3457784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457910 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3457910 : Nat := 118140960795 + 3457910 * 2 ^ 59
def prefixEnd_3457910 : Nat := 4983230072969 + 3 ^ 40 * 3457910 * 2
def baseEnd_3457910 : Nat := 1183713259992447429948245

theorem tailTrace_3457910 : CollatzResearch.WordTrace tailWord_3457910 prefixEnd_3457910 1183713259992447429948245 := by
  unfold tailWord_3457910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882521181411881803494199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84080225935060072570604789 7882521181411881803494199)
  ·
    refine ⟨11823781772117822705241299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7882521181411881803494199 11823781772117822705241299)
    ·
      refine ⟨17735672658176734057861949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823781772117822705241299 17735672658176734057861949)
      ·
        refine ⟨6650877246816275271698231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17735672658176734057861949 6650877246816275271698231)
        ·
          refine ⟨9976315870224412907547347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6650877246816275271698231 9976315870224412907547347)
          ·
            refine ⟨14964473805336619361321021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976315870224412907547347 14964473805336619361321021)
            ·
              refine ⟨5611677677001232260495383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14964473805336619361321021 5611677677001232260495383)
              ·
                refine ⟨8417516515501848390743075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611677677001232260495383 8417516515501848390743075)
                ·
                  refine ⟨12626274773252772586114613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8417516515501848390743075 12626274773252772586114613)
                  ·
                    refine ⟨1183713259992447429948245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12626274773252772586114613 1183713259992447429948245)
                    ·
                      rfl

theorem cell22_3457910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3457910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457910 prefixEnd_3457910 := by exact prefixLift 3457910
  have htrace : WordTrace (prefixWord ++ tailWord_3457910) baseStart_3457910 baseEnd_3457910 := by
    simpa [prefixWord, tailWord_3457910, baseEnd_3457910] using wordTrace_append hprefix tailTrace_3457910
  have hstable : (prefixWord ++ tailWord_3457910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457910).length < 2 ^ (prefixWord ++ tailWord_3457910).sum := by decide
  have hdescent : baseEnd_3457910 < baseStart_3457910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457942 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3457942 : Nat := 118140960795 + 3457942 * 2 ^ 59
def prefixEnd_3457942 : Nat := 4983230072969 + 3 ^ 40 * 3457942 * 2
def baseEnd_3457942 : Nat := 1183724214246410013148147

theorem tailTrace_3457942 : CollatzResearch.WordTrace tailWord_3457942 prefixEnd_3457942 1183724214246410013148147 := by
  unfold tailWord_3457942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882594127404636145067005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84081004025649452214048053 7882594127404636145067005)
  ·
    refine ⟨2955972797776738554400127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7882594127404636145067005 2955972797776738554400127)
    ·
      refine ⟨4433959196665107831600191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2955972797776738554400127 4433959196665107831600191)
      ·
        refine ⟨6650938794997661747400287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4433959196665107831600191 6650938794997661747400287)
        ·
          refine ⟨9976408192496492621100431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6650938794997661747400287 9976408192496492621100431)
          ·
            refine ⟨14964612288744738931650647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976408192496492621100431 14964612288744738931650647)
            ·
              refine ⟨22446918433117108397475971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14964612288744738931650647 22446918433117108397475971)
              ·
                refine ⟨33670377649675662596213957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22446918433117108397475971 33670377649675662596213957)
                ·
                  refine ⟨6313195809314186736790117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33670377649675662596213957 6313195809314186736790117)
                  ·
                    refine ⟨1183724214246410013148147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6313195809314186736790117 1183724214246410013148147)
                    ·
                      rfl

theorem cell22_3457942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3457942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457942 prefixEnd_3457942 := by exact prefixLift 3457942
  have htrace : WordTrace (prefixWord ++ tailWord_3457942) baseStart_3457942 baseEnd_3457942 := by
    simpa [prefixWord, tailWord_3457942, baseEnd_3457942] using wordTrace_append hprefix tailTrace_3457942
  have hstable : (prefixWord ++ tailWord_3457942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457942).length < 2 ^ (prefixWord ++ tailWord_3457942).sum := by decide
  have hdescent : baseEnd_3457942 < baseStart_3457942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3457955 : List Nat := [1, 1, 1, 4, 1, 2, 2, 6, 1, 3]
def baseStart_3457955 : Nat := 118140960795 + 3457955 * 2 ^ 59
def prefixEnd_3457955 : Nat := 4983230072969 + 3 ^ 40 * 3457955 * 2
def baseEnd_3457955 : Nat := 1183728664412082312573107

theorem tailTrace_3457955 : CollatzResearch.WordTrace tailWord_3457955 prefixEnd_3457955 1183728664412082312573107 := by
  unfold tailWord_3457955
  simp only [CollatzResearch.WordTrace]
  refine ⟨126121980187427081541295319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84081320124951387694196879 126121980187427081541295319)
  ·
    refine ⟨189182970281140622311942979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126121980187427081541295319 189182970281140622311942979)
    ·
      refine ⟨283774455421710933467914469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189182970281140622311942979 283774455421710933467914469)
      ·
        refine ⟨53207710391570800025233963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283774455421710933467914469 53207710391570800025233963)
        ·
          refine ⟨79811565587356200037850945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53207710391570800025233963 79811565587356200037850945)
          ·
            refine ⟨59858674190517150028388209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79811565587356200037850945 59858674190517150028388209)
            ·
              refine ⟨44894005642887862521291157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59858674190517150028388209 44894005642887862521291157)
              ·
                refine ⟨2104406514510368555685523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44894005642887862521291157 2104406514510368555685523)
                ·
                  refine ⟨3156609771765552833528285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104406514510368555685523 3156609771765552833528285)
                  ·
                    refine ⟨1183728664412082312573107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3156609771765552833528285 1183728664412082312573107)
                    ·
                      rfl

theorem cell22_3457955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 3].length) (baseStart_3457955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3457955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3457955 prefixEnd_3457955 := by exact prefixLift 3457955
  have htrace : WordTrace (prefixWord ++ tailWord_3457955) baseStart_3457955 baseEnd_3457955 := by
    simpa [prefixWord, tailWord_3457955, baseEnd_3457955] using wordTrace_append hprefix tailTrace_3457955
  have hstable : (prefixWord ++ tailWord_3457955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3457955).length < 2 ^ (prefixWord ++ tailWord_3457955).sum := by decide
  have hdescent : baseEnd_3457955 < baseStart_3457955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3457955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458006 : List Nat := [5, 2, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3458006 : Nat := 118140960795 + 3458006 * 2 ^ 59
def prefixEnd_3458006 : Nat := 4983230072969 + 3 ^ 40 * 3458006 * 2
def baseEnd_3458006 : Nat := 1183746122754335179547951

theorem tailTrace_3458006 : CollatzResearch.WordTrace tailWord_3458006 prefixEnd_3458006 1183746122754335179547951 := by
  unfold tailWord_3458006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882740019390144828212617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84082560206828211500934581 7882740019390144828212617)
  ·
    refine ⟨5912055014542608621159463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7882740019390144828212617 5912055014542608621159463)
    ·
      refine ⟨8868082521813912931739195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5912055014542608621159463 8868082521813912931739195)
      ·
        refine ⟨13302123782720869397608793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8868082521813912931739195 13302123782720869397608793)
        ·
          refine ⟨9976592837040652048206595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13302123782720869397608793 9976592837040652048206595)
          ·
            refine ⟨14964889255560978072309893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976592837040652048206595 14964889255560978072309893)
            ·
              refine ⟨2805916735417683388558105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14964889255560978072309893 2805916735417683388558105)
              ·
                refine ⟨2104437551563262541418579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805916735417683388558105 2104437551563262541418579)
                ·
                  refine ⟨3156656327344893812127869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104437551563262541418579 3156656327344893812127869)
                  ·
                    refine ⟨1183746122754335179547951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3156656327344893812127869 1183746122754335179547951)
                    ·
                      rfl

theorem cell22_3458006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3458006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458006 prefixEnd_3458006 := by exact prefixLift 3458006
  have htrace : WordTrace (prefixWord ++ tailWord_3458006) baseStart_3458006 baseEnd_3458006 := by
    simpa [prefixWord, tailWord_3458006, baseEnd_3458006] using wordTrace_append hprefix tailTrace_3458006
  have hstable : (prefixWord ++ tailWord_3458006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458006).length < 2 ^ (prefixWord ++ tailWord_3458006).sum := by decide
  have hdescent : baseEnd_3458006 < baseStart_3458006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458028 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_3458028 : Nat := 118140960795 + 3458028 * 2 ^ 59
def prefixEnd_3458028 : Nat := 4983230072969 + 3 ^ 40 * 3458028 * 2
def baseEnd_3458028 : Nat := 1183753653803934455497883

theorem tailTrace_3458028 : CollatzResearch.WordTrace tailWord_3458028 prefixEnd_3458028 1183753653803934455497883 := by
  unfold tailWord_3458028
  simp only [CollatzResearch.WordTrace]
  refine ⟨63062321358081307504351369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84083095144108410005801825 63062321358081307504351369)
  ·
    refine ⟨47296741018560980628263527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63062321358081307504351369 47296741018560980628263527)
    ·
      refine ⟨70945111527841470942395291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47296741018560980628263527 70945111527841470942395291)
      ·
        refine ⟨106417667291762206413592937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70945111527841470942395291 106417667291762206413592937)
        ·
          refine ⟨79813250468821654810194703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106417667291762206413592937 79813250468821654810194703)
          ·
            refine ⟨119719875703232482215292055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79813250468821654810194703 119719875703232482215292055)
            ·
              refine ⟨179579813554848723322938083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119719875703232482215292055 179579813554848723322938083)
              ·
                refine ⟨269369720332273084984407125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179579813554848723322938083 269369720332273084984407125)
                ·
                  refine ⟨3156676410143825214661021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 269369720332273084984407125 3156676410143825214661021)
                  ·
                    refine ⟨1183753653803934455497883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3156676410143825214661021 1183753653803934455497883)
                    ·
                      rfl

theorem cell22_3458028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_3458028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458028 prefixEnd_3458028 := by exact prefixLift 3458028
  have htrace : WordTrace (prefixWord ++ tailWord_3458028) baseStart_3458028 baseEnd_3458028 := by
    simpa [prefixWord, tailWord_3458028, baseEnd_3458028] using wordTrace_append hprefix tailTrace_3458028
  have hstable : (prefixWord ++ tailWord_3458028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458028).length < 2 ^ (prefixWord ++ tailWord_3458028).sum := by decide
  have hdescent : baseEnd_3458028 < baseStart_3458028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458030 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_3458030 : Nat := 118140960795 + 3458030 * 2 ^ 59
def prefixEnd_3458030 : Nat := 4983230072969 + 3 ^ 40 * 3458030 * 2
def baseEnd_3458030 : Nat := 394584779481602372315959

theorem tailTrace_3458030 : CollatzResearch.WordTrace tailWord_3458030 prefixEnd_3458030 394584779481602372315959 := by
  unfold tailWord_3458030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765589457769421168784443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84083143774770246233517029 15765589457769421168784443)
  ·
    refine ⟨23648384186654131753176665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15765589457769421168784443 23648384186654131753176665)
    ·
      refine ⟨17736288139990598814882499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23648384186654131753176665 17736288139990598814882499)
      ·
        refine ⟨26604432209985898222323749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17736288139990598814882499 26604432209985898222323749)
        ·
          refine ⟨4988331039372355916685703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26604432209985898222323749 4988331039372355916685703)
          ·
            refine ⟨7482496559058533875028555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988331039372355916685703 7482496559058533875028555)
            ·
              refine ⟨11223744838587800812542833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7482496559058533875028555 11223744838587800812542833)
              ·
                refine ⟨8417808628940850609407125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11223744838587800812542833 8417808628940850609407125)
                ·
                  refine ⟨394584779481602372315959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8417808628940850609407125 394584779481602372315959)
                  ·
                    rfl

theorem cell22_3458030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_3458030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458030 prefixEnd_3458030 := by exact prefixLift 3458030
  have htrace : WordTrace (prefixWord ++ tailWord_3458030) baseStart_3458030 baseEnd_3458030 := by
    simpa [prefixWord, tailWord_3458030, baseEnd_3458030] using wordTrace_append hprefix tailTrace_3458030
  have hstable : (prefixWord ++ tailWord_3458030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458030).length < 2 ^ (prefixWord ++ tailWord_3458030).sum := by decide
  have hdescent : baseEnd_3458030 < baseStart_3458030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458058 : List Nat := [3, 1, 2, 2, 3, 2, 9]
def baseStart_3458058 : Nat := 118140960795 + 3458058 * 2 ^ 59
def prefixEnd_3458058 : Nat := 4983230072969 + 3 ^ 40 * 3458058 * 2
def baseEnd_3458058 : Nat := 43843108274704606564733

theorem tailTrace_3458058 : CollatzResearch.WordTrace tailWord_3458058 prefixEnd_3458058 43843108274704606564733 := by
  unfold tailWord_3458058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31531434226513482533073707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84083824604035953421529885 31531434226513482533073707)
  ·
    refine ⟨47297151339770223799610561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31531434226513482533073707 47297151339770223799610561)
    ·
      refine ⟨35472863504827667849707921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47297151339770223799610561 35472863504827667849707921)
      ·
        refine ⟨26604647628620750887280941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35472863504827667849707921 26604647628620750887280941)
        ·
          refine ⟨9976742860732781582730353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26604647628620750887280941 9976742860732781582730353)
          ·
            refine ⟨7482557145549586187047765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9976742860732781582730353 7482557145549586187047765)
            ·
              refine ⟨43843108274704606564733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7482557145549586187047765 43843108274704606564733)
              ·
                rfl

theorem cell22_3458058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 9].length) (baseStart_3458058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458058 prefixEnd_3458058 := by exact prefixLift 3458058
  have htrace : WordTrace (prefixWord ++ tailWord_3458058) baseStart_3458058 baseEnd_3458058 := by
    simpa [prefixWord, tailWord_3458058, baseEnd_3458058] using wordTrace_append hprefix tailTrace_3458058
  have hstable : (prefixWord ++ tailWord_3458058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458058).length < 2 ^ (prefixWord ++ tailWord_3458058).sum := by decide
  have hdescent : baseEnd_3458058 < baseStart_3458058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458062 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3458062 : Nat := 118140960795 + 3458062 * 2 ^ 59
def prefixEnd_3458062 : Nat := 4983230072969 + 3 ^ 40 * 3458062 * 2
def baseEnd_3458062 : Nat := 1183765292698769700147779

theorem tailTrace_3458062 : CollatzResearch.WordTrace tailWord_3458062 prefixEnd_3458062 1183765292698769700147779 := by
  unfold tailWord_3458062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765735349754929851930055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84083921865359625876960293 15765735349754929851930055)
  ·
    refine ⟨23648603024632394777895083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15765735349754929851930055 23648603024632394777895083)
    ·
      refine ⟨35472904536948592166842625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23648603024632394777895083 35472904536948592166842625)
      ·
        refine ⟨26604678402711444125131969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35472904536948592166842625 26604678402711444125131969)
        ·
          refine ⟨19953508802033583093848977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26604678402711444125131969 19953508802033583093848977)
          ·
            refine ⟨14965131601525187320386733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19953508802033583093848977 14965131601525187320386733)
            ·
              refine ⟨5611924350571945245145025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14965131601525187320386733 5611924350571945245145025)
              ·
                refine ⟨4208943262928958933858769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5611924350571945245145025 4208943262928958933858769)
                ·
                  refine ⟨3156707447196719200394077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208943262928958933858769 3156707447196719200394077)
                  ·
                    refine ⟨1183765292698769700147779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3156707447196719200394077 1183765292698769700147779)
                    ·
                      rfl

theorem cell22_3458062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3458062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458062 prefixEnd_3458062 := by exact prefixLift 3458062
  have htrace : WordTrace (prefixWord ++ tailWord_3458062) baseStart_3458062 baseEnd_3458062 := by
    simpa [prefixWord, tailWord_3458062, baseEnd_3458062] using wordTrace_append hprefix tailTrace_3458062
  have hstable : (prefixWord ++ tailWord_3458062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458062).length < 2 ^ (prefixWord ++ tailWord_3458062).sum := by decide
  have hdescent : baseEnd_3458062 < baseStart_3458062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458148 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 8]
def baseStart_3458148 : Nat := 118140960795 + 3458148 * 2 ^ 59
def prefixEnd_3458148 : Nat := 4983230072969 + 3 ^ 40 * 3458148 * 2
def baseEnd_3458148 : Nat := 394598244085431380832505

theorem tailTrace_3458148 : CollatzResearch.WordTrace tailWord_3458148 prefixEnd_3458148 394598244085431380832505 := by
  unfold tailWord_3458148
  simp only [CollatzResearch.WordTrace]
  refine ⟨63064509737863937751535549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84086012983818583668714065 63064509737863937751535549)
  ·
    refine ⟨23649191151698976656825831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63064509737863937751535549 23649191151698976656825831)
    ·
      refine ⟨35473786727548464985238747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23649191151698976656825831 35473786727548464985238747)
      ·
        refine ⟨53210680091322697477858121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35473786727548464985238747 53210680091322697477858121)
        ·
          refine ⟨39908010068492023108393591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53210680091322697477858121 39908010068492023108393591)
          ·
            refine ⟨59862015102738034662590387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39908010068492023108393591 59862015102738034662590387)
            ·
              refine ⟨89793022654107051993885581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59862015102738034662590387 89793022654107051993885581)
              ·
                refine ⟨33672383495290144497707093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89793022654107051993885581 33672383495290144497707093)
                ·
                  refine ⟨394598244085431380832505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33672383495290144497707093 394598244085431380832505)
                  ·
                    rfl

theorem cell22_3458148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_3458148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458148 prefixEnd_3458148 := by exact prefixLift 3458148
  have htrace : WordTrace (prefixWord ++ tailWord_3458148) baseStart_3458148 baseEnd_3458148 := by
    simpa [prefixWord, tailWord_3458148, baseEnd_3458148] using wordTrace_append hprefix tailTrace_3458148
  have hstable : (prefixWord ++ tailWord_3458148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458148).length < 2 ^ (prefixWord ++ tailWord_3458148).sum := by decide
  have hdescent : baseEnd_3458148 < baseStart_3458148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458167 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 1, 4]
def baseStart_3458167 : Nat := 118140960795 + 3458167 * 2 ^ 59
def prefixEnd_3458167 : Nat := 4983230072969 + 3 ^ 40 * 3458167 * 2
def baseEnd_3458167 : Nat := 1183801236344584426272457

theorem tailTrace_3458167 : CollatzResearch.WordTrace tailWord_3458167 prefixEnd_3458167 1183801236344584426272457 := by
  unfold tailWord_3458167
  simp only [CollatzResearch.WordTrace]
  refine ⟨126129712462659041748012755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84086474975106027832008503 126129712462659041748012755)
  ·
    refine ⟨189194568693988562622019133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126129712462659041748012755 189194568693988562622019133)
    ·
      refine ⟨70947963260245710983257175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189194568693988562622019133 70947963260245710983257175)
      ·
        refine ⟨106421944890368566474885763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70947963260245710983257175 106421944890368566474885763)
        ·
          refine ⟨159632917335552849712328645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106421944890368566474885763 159632917335552849712328645)
          ·
            refine ⟨29931172000416159321061621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159632917335552849712328645 29931172000416159321061621)
            ·
              refine ⟨2806047375039014936349527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29931172000416159321061621 2806047375039014936349527)
              ·
                refine ⟨4209071062558522404524291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806047375039014936349527 4209071062558522404524291)
                ·
                  refine ⟨6313606593837783606786437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209071062558522404524291 6313606593837783606786437)
                  ·
                    refine ⟨1183801236344584426272457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6313606593837783606786437 1183801236344584426272457)
                    ·
                      rfl

theorem cell22_3458167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_3458167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458167 prefixEnd_3458167 := by exact prefixLift 3458167
  have htrace : WordTrace (prefixWord ++ tailWord_3458167) baseStart_3458167 baseEnd_3458167 := by
    simpa [prefixWord, tailWord_3458167, baseEnd_3458167] using wordTrace_append hprefix tailTrace_3458167
  have hstable : (prefixWord ++ tailWord_3458167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458167).length < 2 ^ (prefixWord ++ tailWord_3458167).sum := by decide
  have hdescent : baseEnd_3458167 < baseStart_3458167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458212 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_3458212 : Nat := 118140960795 + 3458212 * 2 ^ 59
def prefixEnd_3458212 : Nat := 4983230072969 + 3 ^ 40 * 3458212 * 2
def baseEnd_3458212 : Nat := 1183816640764219308897319

theorem tailTrace_3458212 : CollatzResearch.WordTrace tailWord_3458212 prefixEnd_3458212 1183816640764219308897319 := by
  unfold tailWord_3458212
  simp only [CollatzResearch.WordTrace]
  refine ⟨63065676873748007216700445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84087569164997342955600593 63065676873748007216700445)
  ·
    refine ⟨23649628827655502706262667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63065676873748007216700445 23649628827655502706262667)
    ·
      refine ⟨35474443241483254059394001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23649628827655502706262667 35474443241483254059394001)
      ·
        refine ⟨26605832431112440544545501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35474443241483254059394001 26605832431112440544545501)
        ·
          refine ⟨9977187161667165204204563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26605832431112440544545501 9977187161667165204204563)
          ·
            refine ⟨14965780742500747806306845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9977187161667165204204563 14965780742500747806306845)
            ·
              refine ⟨5612167778437780427365067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14965780742500747806306845 5612167778437780427365067)
              ·
                refine ⟨8418251667656670641047601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612167778437780427365067 8418251667656670641047601)
                ·
                  refine ⟨6313688750742502980785701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8418251667656670641047601 6313688750742502980785701)
                  ·
                    refine ⟨1183816640764219308897319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6313688750742502980785701 1183816640764219308897319)
                    ·
                      rfl

theorem cell22_3458212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_3458212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458212 prefixEnd_3458212 := by exact prefixLift 3458212
  have htrace : WordTrace (prefixWord ++ tailWord_3458212) baseStart_3458212 baseEnd_3458212 := by
    simpa [prefixWord, tailWord_3458212, baseEnd_3458212] using wordTrace_append hprefix tailTrace_3458212
  have hstable : (prefixWord ++ tailWord_3458212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458212).length < 2 ^ (prefixWord ++ tailWord_3458212).sum := by decide
  have hdescent : baseEnd_3458212 < baseStart_3458212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458332 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_3458332 : Nat := 118140960795 + 3458332 * 2 ^ 59
def prefixEnd_3458332 : Nat := 4983230072969 + 3 ^ 40 * 3458332 * 2
def baseEnd_3458332 : Nat := 1183857719216578995896951

theorem tailTrace_3458332 : CollatzResearch.WordTrace tailWord_3458332 prefixEnd_3458332 1183857719216578995896951 := by
  unfold tailWord_3458332
  simp only [CollatzResearch.WordTrace]
  refine ⟨63067865253530637463884625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84090487004707516618512833 63067865253530637463884625)
  ·
    refine ⟨47300898940147978097913469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63067865253530637463884625 47300898940147978097913469)
    ·
      refine ⟨17737837102555491786717551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47300898940147978097913469 17737837102555491786717551)
      ·
        refine ⟨26606755653833237680076327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17737837102555491786717551 26606755653833237680076327)
        ·
          refine ⟨39910133480749856520114491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26606755653833237680076327 39910133480749856520114491)
          ·
            refine ⟨59865200221124784780171737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39910133480749856520114491 59865200221124784780171737)
            ·
              refine ⟨44898900165843588585128803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59865200221124784780171737 44898900165843588585128803)
              ·
                refine ⟨67348350248765382877693205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44898900165843588585128803 67348350248765382877693205)
                ·
                  refine ⟨3156953917910877322391869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67348350248765382877693205 3156953917910877322391869)
                  ·
                    refine ⟨1183857719216578995896951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3156953917910877322391869 1183857719216578995896951)
                    ·
                      rfl

theorem cell22_3458332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_3458332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458332 prefixEnd_3458332 := by exact prefixLift 3458332
  have htrace : WordTrace (prefixWord ++ tailWord_3458332) baseStart_3458332 baseEnd_3458332 := by
    simpa [prefixWord, tailWord_3458332, baseEnd_3458332] using wordTrace_append hprefix tailTrace_3458332
  have hstable : (prefixWord ++ tailWord_3458332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458332).length < 2 ^ (prefixWord ++ tailWord_3458332).sum := by decide
  have hdescent : baseEnd_3458332 < baseStart_3458332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458336 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 1, 4]
def baseStart_3458336 : Nat := 118140960795 + 3458336 * 2 ^ 59
def prefixEnd_3458336 : Nat := 4983230072969 + 3 ^ 40 * 3458336 * 2
def baseEnd_3458336 : Nat := 1183859088498324318796939

theorem tailTrace_3458336 : CollatzResearch.WordTrace tailWord_3458336 prefixEnd_3458336 1183859088498324318796939 := by
  unfold tailWord_3458336
  simp only [CollatzResearch.WordTrace]
  refine ⟨63067938199523391805457431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84090584266031189073943241 63067938199523391805457431)
  ·
    refine ⟨94601907299285087708186147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63067938199523391805457431 94601907299285087708186147)
    ·
      refine ⟨141902860948927631562279221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94601907299285087708186147 141902860948927631562279221)
      ·
        refine ⟨13303393213961965458963677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141902860948927631562279221 13303393213961965458963677)
        ·
          refine ⟨4988772455235737047111379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13303393213961965458963677 4988772455235737047111379)
          ·
            refine ⟨7483158682853605570667069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988772455235737047111379 7483158682853605570667069)
            ·
              refine ⟨2806184506070102089000151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7483158682853605570667069 2806184506070102089000151)
              ·
                refine ⟨4209276759105153133500227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806184506070102089000151 4209276759105153133500227)
                ·
                  refine ⟨6313915138657729700250341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4209276759105153133500227 6313915138657729700250341)
                  ·
                    refine ⟨1183859088498324318796939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6313915138657729700250341 1183859088498324318796939)
                    ·
                      rfl

theorem cell22_3458336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_3458336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458336 prefixEnd_3458336 := by exact prefixLift 3458336
  have htrace : WordTrace (prefixWord ++ tailWord_3458336) baseStart_3458336 baseEnd_3458336 := by
    simpa [prefixWord, tailWord_3458336, baseEnd_3458336] using wordTrace_append hprefix tailTrace_3458336
  have hstable : (prefixWord ++ tailWord_3458336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458336).length < 2 ^ (prefixWord ++ tailWord_3458336).sum := by decide
  have hdescent : baseEnd_3458336 < baseStart_3458336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458360 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_3458360 : Nat := 118140960795 + 3458360 * 2 ^ 59
def prefixEnd_3458360 : Nat := 4983230072969 + 3 ^ 40 * 3458360 * 2
def baseEnd_3458360 : Nat := 1183867304188796256196865

theorem tailTrace_3458360 : CollatzResearch.WordTrace tailWord_3458360 prefixEnd_3458360 1183867304188796256196865 := by
  unfold tailWord_3458360
  simp only [CollatzResearch.WordTrace]
  refine ⟨63068375875479917854894267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84091167833973223806525689 63068375875479917854894267)
  ·
    refine ⟨94602563813219876782341401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63068375875479917854894267 94602563813219876782341401)
    ·
      refine ⟨70951922859914907586756051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94602563813219876782341401 70951922859914907586756051)
      ·
        refine ⟨106427884289872361380134077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70951922859914907586756051 106427884289872361380134077)
        ·
          refine ⟨39910456608702135517550279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106427884289872361380134077 39910456608702135517550279)
          ·
            refine ⟨59865684913053203276325419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39910456608702135517550279 59865684913053203276325419)
            ·
              refine ⟨89798527369579804914488129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59865684913053203276325419 89798527369579804914488129)
              ·
                refine ⟨67348895527184853685866097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89798527369579804914488129 67348895527184853685866097)
                ·
                  refine ⟨50511671645388640264399573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67348895527184853685866097 50511671645388640264399573)
                  ·
                    refine ⟨1183867304188796256196865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50511671645388640264399573 1183867304188796256196865)
                    ·
                      rfl

theorem cell22_3458360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_3458360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458360 prefixEnd_3458360 := by exact prefixLift 3458360
  have htrace : WordTrace (prefixWord ++ tailWord_3458360) baseStart_3458360 baseEnd_3458360 := by
    simpa [prefixWord, tailWord_3458360, baseEnd_3458360] using wordTrace_append hprefix tailTrace_3458360
  have hstable : (prefixWord ++ tailWord_3458360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458360).length < 2 ^ (prefixWord ++ tailWord_3458360).sum := by decide
  have hdescent : baseEnd_3458360 < baseStart_3458360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458377 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 5, 3]
def baseStart_3458377 : Nat := 118140960795 + 3458377 * 2 ^ 59
def prefixEnd_3458377 : Nat := 4983230072969 + 3 ^ 40 * 3458377 * 2
def baseEnd_3458377 : Nat := 1183873123636213878521813

theorem tailTrace_3458377 : CollatzResearch.WordTrace tailWord_3458377 prefixEnd_3458377 1183873123636213878521813 := by
  unfold tailWord_3458377
  simp only [CollatzResearch.WordTrace]
  refine ⟨126137371791898247613157385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84091581194598831742104923 126137371791898247613157385)
  ·
    refine ⟨94603028843923685709868039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126137371791898247613157385 94603028843923685709868039)
    ·
      refine ⟨141904543265885528564802059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94603028843923685709868039 141904543265885528564802059)
      ·
        refine ⟨212856814898828292847203089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141904543265885528564802059 212856814898828292847203089)
        ·
          refine ⟨159642611174121219635402317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212856814898828292847203089 159642611174121219635402317)
          ·
            refine ⟨59865979190295457363275869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159642611174121219635402317 59865979190295457363275869)
            ·
              refine ⟨22449742196360796511228451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59865979190295457363275869 22449742196360796511228451)
              ·
                refine ⟨33674613294541194766842677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22449742196360796511228451 33674613294541194766842677)
                ·
                  refine ⟨3156994996363237009391501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33674613294541194766842677 3156994996363237009391501)
                  ·
                    refine ⟨1183873123636213878521813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3156994996363237009391501 1183873123636213878521813)
                    ·
                      rfl

theorem cell22_3458377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_3458377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458377 prefixEnd_3458377 := by exact prefixLift 3458377
  have htrace : WordTrace (prefixWord ++ tailWord_3458377) baseStart_3458377 baseEnd_3458377 := by
    simpa [prefixWord, tailWord_3458377, baseEnd_3458377] using wordTrace_append hprefix tailTrace_3458377
  have hstable : (prefixWord ++ tailWord_3458377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458377).length < 2 ^ (prefixWord ++ tailWord_3458377).sum := by decide
  have hdescent : baseEnd_3458377 < baseStart_3458377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458381 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3458381 : Nat := 118140960795 + 3458381 * 2 ^ 59
def prefixEnd_3458381 : Nat := 4983230072969 + 3 ^ 40 * 3458381 * 2
def baseEnd_3458381 : Nat := 1183874492917959201421801

theorem tailTrace_3458381 : CollatzResearch.WordTrace tailWord_3458381 prefixEnd_3458381 1183874492917959201421801 := by
  unfold tailWord_3458381
  simp only [CollatzResearch.WordTrace]
  refine ⟨126137517683883756296302997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84091678455922504197535331 126137517683883756296302997)
  ·
    refine ⟨5912696141432051076389203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126137517683883756296302997 5912696141432051076389203)
    ·
      refine ⟨8869044212148076614583805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5912696141432051076389203 8869044212148076614583805)
      ·
        refine ⟨3325891579555528730468927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8869044212148076614583805 3325891579555528730468927)
        ·
          refine ⟨4988837369333293095703391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325891579555528730468927 4988837369333293095703391)
          ·
            refine ⟨7483256053999939643555087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988837369333293095703391 7483256053999939643555087)
            ·
              refine ⟨11224884080999909465332631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483256053999939643555087 11224884080999909465332631)
              ·
                refine ⟨16837326121499864197998947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11224884080999909465332631 16837326121499864197998947)
                ·
                  refine ⟨25255989182249796296998421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16837326121499864197998947 25255989182249796296998421)
                  ·
                    refine ⟨1183874492917959201421801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25255989182249796296998421 1183874492917959201421801)
                    ·
                      rfl

theorem cell22_3458381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3458381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458381 prefixEnd_3458381 := by exact prefixLift 3458381
  have htrace : WordTrace (prefixWord ++ tailWord_3458381) baseStart_3458381 baseEnd_3458381 := by
    simpa [prefixWord, tailWord_3458381, baseEnd_3458381] using wordTrace_append hprefix tailTrace_3458381
  have hstable : (prefixWord ++ tailWord_3458381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458381).length < 2 ^ (prefixWord ++ tailWord_3458381).sum := by decide
  have hdescent : baseEnd_3458381 < baseStart_3458381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458430 : List Nat := [4, 2, 3, 2, 2, 1, 2, 6]
def baseStart_3458430 : Nat := 118140960795 + 3458430 * 2 ^ 59
def prefixEnd_3458430 : Nat := 4983230072969 + 3 ^ 40 * 3458430 * 2
def baseEnd_3458430 : Nat := 131543474068815489660739

theorem tailTrace_3458430 : CollatzResearch.WordTrace tailWord_3458430 prefixEnd_3458430 131543474068815489660739 := by
  unfold tailWord_3458430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767413107588279708104593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84092869907137491776557829 15767413107588279708104593)
  ·
    refine ⟨11825559830691209781078445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15767413107588279708104593 11825559830691209781078445)
    ·
      refine ⟨4434584936509203667904417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11825559830691209781078445 4434584936509203667904417)
      ·
        refine ⟨3325938702381902750928313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4434584936509203667904417 3325938702381902750928313)
        ·
          refine ⟨2494454026786427063196235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3325938702381902750928313 2494454026786427063196235)
          ·
            refine ⟨3741681040179640594794353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494454026786427063196235 3741681040179640594794353)
            ·
              refine ⟨2806260780134730446095765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3741681040179640594794353 2806260780134730446095765)
              ·
                refine ⟨131543474068815489660739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2806260780134730446095765 131543474068815489660739)
                ·
                  rfl

theorem cell22_3458430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_3458430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458430 prefixEnd_3458430 := by exact prefixLift 3458430
  have htrace : WordTrace (prefixWord ++ tailWord_3458430) baseStart_3458430 baseEnd_3458430 := by
    simpa [prefixWord, tailWord_3458430, baseEnd_3458430] using wordTrace_append hprefix tailTrace_3458430
  have hstable : (prefixWord ++ tailWord_3458430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458430).length < 2 ^ (prefixWord ++ tailWord_3458430).sum := by decide
  have hdescent : baseEnd_3458430 < baseStart_3458430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458437 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3458437 : Nat := 118140960795 + 3458437 * 2 ^ 59
def prefixEnd_3458437 : Nat := 4983230072969 + 3 ^ 40 * 3458437 * 2
def baseEnd_3458437 : Nat := 1183893662862393722021629

theorem tailTrace_3458437 : CollatzResearch.WordTrace tailWord_3458437 prefixEnd_3458437 1183893662862393722021629 := by
  unfold tailWord_3458437
  simp only [CollatzResearch.WordTrace]
  refine ⟨126139560171680877860341565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84093040114453918573561043 126139560171680877860341565)
  ·
    refine ⟨47302335064380329197628087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126139560171680877860341565 47302335064380329197628087)
    ·
      refine ⟨70953502596570493796442131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47302335064380329197628087 70953502596570493796442131)
      ·
        refine ⟨106430253894855740694663197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70953502596570493796442131 106430253894855740694663197)
        ·
          refine ⟨39911345210570902760498699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106430253894855740694663197 39911345210570902760498699)
          ·
            refine ⟨59867017815856354140748049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39911345210570902760498699 59867017815856354140748049)
            ·
              refine ⟨44900263361892265605561037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59867017815856354140748049 44900263361892265605561037)
              ·
                refine ⟨16837598760709599602085389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44900263361892265605561037 16837598760709599602085389)
                ·
                  refine ⟨6314099535266099850782021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16837598760709599602085389 6314099535266099850782021)
                  ·
                    refine ⟨1183893662862393722021629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6314099535266099850782021 1183893662862393722021629)
                    ·
                      rfl

theorem cell22_3458437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3458437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458437 prefixEnd_3458437 := by exact prefixLift 3458437
  have htrace : WordTrace (prefixWord ++ tailWord_3458437) baseStart_3458437 baseEnd_3458437 := by
    simpa [prefixWord, tailWord_3458437, baseEnd_3458437] using wordTrace_append hprefix tailTrace_3458437
  have hstable : (prefixWord ++ tailWord_3458437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458437).length < 2 ^ (prefixWord ++ tailWord_3458437).sum := by decide
  have hdescent : baseEnd_3458437 < baseStart_3458437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458462 : List Nat := [4, 3, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3458462 : Nat := 118140960795 + 3458462 * 2 ^ 59
def prefixEnd_3458462 : Nat := 4983230072969 + 3 ^ 40 * 3458462 * 2
def baseEnd_3458462 : Nat := 1183902220873301990146553

theorem tailTrace_3458462 : CollatzResearch.WordTrace tailWord_3458462 prefixEnd_3458462 1183902220873301990146553 := by
  unfold tailWord_3458462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767558999573788391250205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84093647997726871420001093 15767558999573788391250205)
  ·
    refine ⟨5912834624840170646718827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15767558999573788391250205 5912834624840170646718827)
    ·
      refine ⟨8869251937260255970078241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5912834624840170646718827 8869251937260255970078241)
      ·
        refine ⟨6651938952945191977558681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8869251937260255970078241 6651938952945191977558681)
        ·
          refine ⟨4988954214708893983169011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6651938952945191977558681 4988954214708893983169011)
          ·
            refine ⟨7483431322063340974753517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988954214708893983169011 7483431322063340974753517)
            ·
              refine ⟨2806286745773752865532569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7483431322063340974753517 2806286745773752865532569)
              ·
                refine ⟨2104715059330314649149427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806286745773752865532569 2104715059330314649149427)
                ·
                  refine ⟨3157072588995471973724141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104715059330314649149427 3157072588995471973724141)
                  ·
                    refine ⟨1183902220873301990146553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157072588995471973724141 1183902220873301990146553)
                    ·
                      rfl

theorem cell22_3458462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3458462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458462 prefixEnd_3458462 := by exact prefixLift 3458462
  have htrace : WordTrace (prefixWord ++ tailWord_3458462) baseStart_3458462 baseEnd_3458462 := by
    simpa [prefixWord, tailWord_3458462, baseEnd_3458462] using wordTrace_append hprefix tailTrace_3458462
  have hstable : (prefixWord ++ tailWord_3458462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458462).length < 2 ^ (prefixWord ++ tailWord_3458462).sum := by decide
  have hdescent : baseEnd_3458462 < baseStart_3458462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458482 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3458482 : Nat := 118140960795 + 3458482 * 2 ^ 59
def prefixEnd_3458482 : Nat := 4983230072969 + 3 ^ 40 * 3458482 * 2
def baseEnd_3458482 : Nat := 1183909067282028604646491

theorem tailTrace_3458482 : CollatzResearch.WordTrace tailWord_3458482 prefixEnd_3458482 1183909067282028604646491 := by
  unfold tailWord_3458482
  simp only [CollatzResearch.WordTrace]
  refine ⟨31535300364129462636432425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84094134304345233697153133 31535300364129462636432425)
  ·
    refine ⟨23651475273097096977324319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31535300364129462636432425 23651475273097096977324319)
    ·
      refine ⟨35477212909645645465986479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651475273097096977324319 35477212909645645465986479)
      ·
        refine ⟨53215819364468468198979719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35477212909645645465986479 53215819364468468198979719)
        ·
          refine ⟨79823729046702702298469579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53215819364468468198979719 79823729046702702298469579)
          ·
            refine ⟨119735593570054053447704369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79823729046702702298469579 119735593570054053447704369)
            ·
              refine ⟨89801695177540540085778277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119735593570054053447704369 89801695177540540085778277)
              ·
                refine ⟨16837817845788851266083427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89801695177540540085778277 16837817845788851266083427)
                ·
                  refine ⟨25256726768683276899125141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16837817845788851266083427 25256726768683276899125141)
                  ·
                    refine ⟨1183909067282028604646491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25256726768683276899125141 1183909067282028604646491)
                    ·
                      rfl

theorem cell22_3458482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3458482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458482 prefixEnd_3458482 := by exact prefixLift 3458482
  have htrace : WordTrace (prefixWord ++ tailWord_3458482) baseStart_3458482 baseEnd_3458482 := by
    simpa [prefixWord, tailWord_3458482, baseEnd_3458482] using wordTrace_append hprefix tailTrace_3458482
  have hstable : (prefixWord ++ tailWord_3458482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458482).length < 2 ^ (prefixWord ++ tailWord_3458482).sum := by decide
  have hdescent : baseEnd_3458482 < baseStart_3458482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458518 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3458518 : Nat := 118140960795 + 3458518 * 2 ^ 59
def prefixEnd_3458518 : Nat := 4983230072969 + 3 ^ 40 * 3458518 * 2
def baseEnd_3458518 : Nat := 1183921390817736510746381

theorem tailTrace_3458518 : CollatzResearch.WordTrace tailWord_3458518 prefixEnd_3458518 1183921390817736510746381 := by
  unfold tailWord_3458518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7883907155274214293377513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84095009656258285796026805 7883907155274214293377513)
  ·
    refine ⟨5912930366455660720033135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7883907155274214293377513 5912930366455660720033135)
    ·
      refine ⟨8869395549683491080049703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5912930366455660720033135 8869395549683491080049703)
      ·
        refine ⟨13304093324525236620074555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869395549683491080049703 13304093324525236620074555)
        ·
          refine ⟨19956139986787854930111833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13304093324525236620074555 19956139986787854930111833)
          ·
            refine ⟨14967104990090891197583875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19956139986787854930111833 14967104990090891197583875)
            ·
              refine ⟨22450657485136336796375813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14967104990090891197583875 22450657485136336796375813)
              ·
                refine ⟨4209498278463063149320465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22450657485136336796375813 4209498278463063149320465)
                ·
                  refine ⟨3157123708847297361990349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4209498278463063149320465 3157123708847297361990349)
                  ·
                    refine ⟨1183921390817736510746381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157123708847297361990349 1183921390817736510746381)
                    ·
                      rfl

theorem cell22_3458518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3458518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458518 prefixEnd_3458518 := by exact prefixLift 3458518
  have htrace : WordTrace (prefixWord ++ tailWord_3458518) baseStart_3458518 baseEnd_3458518 := by
    simpa [prefixWord, tailWord_3458518, baseEnd_3458518] using wordTrace_append hprefix tailTrace_3458518
  have hstable : (prefixWord ++ tailWord_3458518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458518).length < 2 ^ (prefixWord ++ tailWord_3458518).sum := by decide
  have hdescent : baseEnd_3458518 < baseStart_3458518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458527 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 8]
def baseStart_3458527 : Nat := 118140960795 + 3458527 * 2 ^ 59
def prefixEnd_3458527 : Nat := 4983230072969 + 3 ^ 40 * 3458527 * 2
def baseEnd_3458527 : Nat := 1183924471701663487271353

theorem tailTrace_3458527 : CollatzResearch.WordTrace tailWord_3458527 prefixEnd_3458527 1183924471701663487271353 := by
  unfold tailWord_3458527
  simp only [CollatzResearch.WordTrace]
  refine ⟨126142842741354823231117835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84095228494236548820745223 126142842741354823231117835)
  ·
    refine ⟨189214264112032234846676753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126142842741354823231117835 189214264112032234846676753)
    ·
      refine ⟨141910698084024176135007565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189214264112032234846676753 141910698084024176135007565)
      ·
        refine ⟨53216511781509066050627837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141910698084024176135007565 53216511781509066050627837)
        ·
          refine ⟨19956191918065899768985439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53216511781509066050627837 19956191918065899768985439)
          ·
            refine ⟨29934287877098849653478159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19956191918065899768985439 29934287877098849653478159)
            ·
              refine ⟨44901431815648274480217239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29934287877098849653478159 44901431815648274480217239)
              ·
                refine ⟨67352147723472411720325859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44901431815648274480217239 67352147723472411720325859)
                ·
                  refine ⟨101028221585208617580488789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67352147723472411720325859 101028221585208617580488789)
                  ·
                    refine ⟨1183924471701663487271353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101028221585208617580488789 1183924471701663487271353)
                    ·
                      rfl

theorem cell22_3458527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_3458527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458527 prefixEnd_3458527 := by exact prefixLift 3458527
  have htrace : WordTrace (prefixWord ++ tailWord_3458527) baseStart_3458527 baseEnd_3458527 := by
    simpa [prefixWord, tailWord_3458527, baseEnd_3458527] using wordTrace_append hprefix tailTrace_3458527
  have hstable : (prefixWord ++ tailWord_3458527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458527).length < 2 ^ (prefixWord ++ tailWord_3458527).sum := by decide
  have hdescent : baseEnd_3458527 < baseStart_3458527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458546 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_3458546 : Nat := 118140960795 + 3458546 * 2 ^ 59
def prefixEnd_3458546 : Nat := 4983230072969 + 3 ^ 40 * 3458546 * 2
def baseEnd_3458546 : Nat := 1183930975789953771046295

theorem tailTrace_3458546 : CollatzResearch.WordTrace tailWord_3458546 prefixEnd_3458546 1183930975789953771046295 := by
  unfold tailWord_3458546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31535883932071497369014873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84095690485523992984039661 31535883932071497369014873)
  ·
    refine ⟨23651912949053623026761155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31535883932071497369014873 23651912949053623026761155)
    ·
      refine ⟨35477869423580434540141733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651912949053623026761155 35477869423580434540141733)
      ·
        refine ⟨6652100516921331476276575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35477869423580434540141733 6652100516921331476276575)
        ·
          refine ⟨9978150775381997214414863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6652100516921331476276575 9978150775381997214414863)
          ·
            refine ⟨14967226163072995821622295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9978150775381997214414863 14967226163072995821622295)
            ·
              refine ⟨22450839244609493732433443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14967226163072995821622295 22450839244609493732433443)
              ·
                refine ⟨33676258866914240598650165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22450839244609493732433443 33676258866914240598650165)
                ·
                  refine ⟨3157149268773210056123453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33676258866914240598650165 3157149268773210056123453)
                  ·
                    refine ⟨1183930975789953771046295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157149268773210056123453 1183930975789953771046295)
                    ·
                      rfl

theorem cell22_3458546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_3458546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458546 prefixEnd_3458546 := by exact prefixLift 3458546
  have htrace : WordTrace (prefixWord ++ tailWord_3458546) baseStart_3458546 baseEnd_3458546 := by
    simpa [prefixWord, tailWord_3458546, baseEnd_3458546] using wordTrace_append hprefix tailTrace_3458546
  have hstable : (prefixWord ++ tailWord_3458546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458546).length < 2 ^ (prefixWord ++ tailWord_3458546).sum := by decide
  have hdescent : baseEnd_3458546 < baseStart_3458546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458580 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3458580 : Nat := 118140960795 + 3458580 * 2 ^ 59
def prefixEnd_3458580 : Nat := 4983230072969 + 3 ^ 40 * 3458580 * 2
def baseEnd_3458580 : Nat := 1183942614684789015696191

theorem tailTrace_3458580 : CollatzResearch.WordTrace tailWord_3458580 prefixEnd_3458580 1183942614684789015696191 := by
  unfold tailWord_3458580
  simp only [CollatzResearch.WordTrace]
  refine ⟨63072387905081406641398597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84096517206775208855198129 63072387905081406641398597)
  ·
    refine ⟨11826072732202763745262237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63072387905081406641398597 11826072732202763745262237)
    ·
      refine ⟨4434777274576036404473339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11826072732202763745262237 4434777274576036404473339)
      ·
        refine ⟨6652165911864054606710009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434777274576036404473339 6652165911864054606710009)
        ·
          refine ⟨4989124433898040955032507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6652165911864054606710009 4989124433898040955032507)
          ·
            refine ⟨7483686650847061432548761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989124433898040955032507 7483686650847061432548761)
            ·
              refine ⟨5612764988135296074411571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7483686650847061432548761 5612764988135296074411571)
              ·
                refine ⟨8419147482202944111617357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5612764988135296074411571 8419147482202944111617357)
                ·
                  refine ⟨3157180305826104041856509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8419147482202944111617357 3157180305826104041856509)
                  ·
                    refine ⟨1183942614684789015696191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157180305826104041856509 1183942614684789015696191)
                    ·
                      rfl

theorem cell22_3458580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3458580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458580 prefixEnd_3458580 := by exact prefixLift 3458580
  have htrace : WordTrace (prefixWord ++ tailWord_3458580) baseStart_3458580 baseEnd_3458580 := by
    simpa [prefixWord, tailWord_3458580, baseEnd_3458580] using wordTrace_append hprefix tailTrace_3458580
  have hstable : (prefixWord ++ tailWord_3458580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458580).length < 2 ^ (prefixWord ++ tailWord_3458580).sum := by decide
  have hdescent : baseEnd_3458580 < baseStart_3458580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458614 : List Nat := [5, 1, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3458614 : Nat := 118140960795 + 3458614 * 2 ^ 59
def prefixEnd_3458614 : Nat := 4983230072969 + 3 ^ 40 * 3458614 * 2
def baseEnd_3458614 : Nat := 1183954253579624260346087

theorem tailTrace_3458614 : CollatzResearch.WordTrace tailWord_3458614 prefixEnd_3458614 1183954253579624260346087 := by
  unfold tailWord_3458614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884125993252477318095931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84097343928026424726356597 7884125993252477318095931)
  ·
    refine ⟨11826188989878715977143897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7884125993252477318095931 11826188989878715977143897)
    ·
      refine ⟨8869641742409036982857923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11826188989878715977143897 8869641742409036982857923)
      ·
        refine ⟨13304462613613555474286885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869641742409036982857923 13304462613613555474286885)
        ·
          refine ⟨2494586740052541651428791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13304462613613555474286885 2494586740052541651428791)
          ·
            refine ⟨3741880110078812477143187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494586740052541651428791 3741880110078812477143187)
            ·
              refine ⟨5612820165118218715714781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3741880110078812477143187 5612820165118218715714781)
              ·
                refine ⟨2104807561919332018393043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5612820165118218715714781 2104807561919332018393043)
                ·
                  refine ⟨3157211342878998027589565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104807561919332018393043 3157211342878998027589565)
                  ·
                    refine ⟨1183954253579624260346087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157211342878998027589565 1183954253579624260346087)
                    ·
                      rfl

theorem cell22_3458614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3458614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458614 prefixEnd_3458614 := by exact prefixLift 3458614
  have htrace : WordTrace (prefixWord ++ tailWord_3458614) baseStart_3458614 baseEnd_3458614 := by
    simpa [prefixWord, tailWord_3458614, baseEnd_3458614] using wordTrace_append hprefix tailTrace_3458614
  have hstable : (prefixWord ++ tailWord_3458614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458614).length < 2 ^ (prefixWord ++ tailWord_3458614).sum := by decide
  have hdescent : baseEnd_3458614 < baseStart_3458614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458636 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_3458636 : Nat := 118140960795 + 3458636 * 2 ^ 59
def prefixEnd_3458636 : Nat := 4983230072969 + 3 ^ 40 * 3458636 * 2
def baseEnd_3458636 : Nat := 1183961784629223536296019

theorem tailTrace_3458636 : CollatzResearch.WordTrace tailWord_3458636 prefixEnd_3458636 1183961784629223536296019 := by
  unfold tailWord_3458636
  simp only [CollatzResearch.WordTrace]
  refine ⟨63073409148979967423417881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84097878865306623231223841 63073409148979967423417881)
  ·
    refine ⟨47305056861734975567563411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63073409148979967423417881 47305056861734975567563411)
    ·
      refine ⟨70957585292602463351345117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47305056861734975567563411 70957585292602463351345117)
      ·
        refine ⟨26609094484725923756754419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70957585292602463351345117 26609094484725923756754419)
        ·
          refine ⟨39913641727088885635131629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26609094484725923756754419 39913641727088885635131629)
          ·
            refine ⟨14967615647658332113174361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39913641727088885635131629 14967615647658332113174361)
            ·
              refine ⟨11225711735743749084880771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14967615647658332113174361 11225711735743749084880771)
              ·
                refine ⟨16838567603615623627321157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11225711735743749084880771 16838567603615623627321157)
                ·
                  refine ⟨3157231425677929430122717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16838567603615623627321157 3157231425677929430122717)
                  ·
                    refine ⟨1183961784629223536296019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157231425677929430122717 1183961784629223536296019)
                    ·
                      rfl

theorem cell22_3458636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_3458636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458636 prefixEnd_3458636 := by exact prefixLift 3458636
  have htrace : WordTrace (prefixWord ++ tailWord_3458636) baseStart_3458636 baseEnd_3458636 := by
    simpa [prefixWord, tailWord_3458636, baseEnd_3458636] using wordTrace_append hprefix tailTrace_3458636
  have hstable : (prefixWord ++ tailWord_3458636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458636).length < 2 ^ (prefixWord ++ tailWord_3458636).sum := by decide
  have hdescent : baseEnd_3458636 < baseStart_3458636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458711 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 5]
def baseStart_3458711 : Nat := 118140960795 + 3458711 * 2 ^ 59
def prefixEnd_3458711 : Nat := 4983230072969 + 3 ^ 40 * 3458711 * 2
def baseEnd_3458711 : Nat := 394662486220649446890263

theorem tailTrace_3458711 : CollatzResearch.WordTrace tailWord_3458711 prefixEnd_3458711 394662486220649446890263 := by
  unfold tailWord_3458711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126149553772688222655815987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84099702515125481770543991 126149553772688222655815987)
  ·
    refine ⟨189224330659032333983723981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126149553772688222655815987 189224330659032333983723981)
    ·
      refine ⟨70959123997137125243896493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189224330659032333983723981 70959123997137125243896493)
      ·
        refine ⟨26609671498926421966461185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70959123997137125243896493 26609671498926421966461185)
        ·
          refine ⟨19957253624194816474845889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26609671498926421966461185 19957253624194816474845889)
          ·
            refine ⟨14967940218146112356134417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19957253624194816474845889 14967940218146112356134417)
            ·
              refine ⟨11225955163609584267100813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14967940218146112356134417 11225955163609584267100813)
              ·
                refine ⟨4209733186353594100162805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11225955163609584267100813 4209733186353594100162805)
                ·
                  refine ⟨394662486220649446890263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4209733186353594100162805 394662486220649446890263)
                  ·
                    rfl

theorem cell22_3458711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 5].length) (baseStart_3458711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458711 prefixEnd_3458711 := by exact prefixLift 3458711
  have htrace : WordTrace (prefixWord ++ tailWord_3458711) baseStart_3458711 baseEnd_3458711 := by
    simpa [prefixWord, tailWord_3458711, baseEnd_3458711] using wordTrace_append hprefix tailTrace_3458711
  have hstable : (prefixWord ++ tailWord_3458711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458711).length < 2 ^ (prefixWord ++ tailWord_3458711).sum := by decide
  have hdescent : baseEnd_3458711 < baseStart_3458711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458739 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 8]
def baseStart_3458739 : Nat := 118140960795 + 3458739 * 2 ^ 59
def prefixEnd_3458739 : Nat := 4983230072969 + 3 ^ 40 * 3458739 * 2
def baseEnd_3458739 : Nat := 394665681211388533656901

theorem tailTrace_3458739 : CollatzResearch.WordTrace tailWord_3458739 prefixEnd_3458739 394665681211388533656901 := by
  unfold tailWord_3458739
  simp only [CollatzResearch.WordTrace]
  refine ⟨126150575016586783437835271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84100383344391188958556847 126150575016586783437835271)
  ·
    refine ⟨189225862524880175156752907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126150575016586783437835271 189225862524880175156752907)
    ·
      refine ⟨283838793787320262735129361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189225862524880175156752907 283838793787320262735129361)
      ·
        refine ⟨212879095340490197051347021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283838793787320262735129361 212879095340490197051347021)
        ·
          refine ⟨79829660752683823894255133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212879095340490197051347021 79829660752683823894255133)
          ·
            refine ⟨29936122782256433960345675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79829660752683823894255133 29936122782256433960345675)
            ·
              refine ⟨44904184173384650940518513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29936122782256433960345675 44904184173384650940518513)
              ·
                refine ⟨33678138130038488205388885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44904184173384650940518513 33678138130038488205388885)
                ·
                  refine ⟨394665681211388533656901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33678138130038488205388885 394665681211388533656901)
                  ·
                    rfl

theorem cell22_3458739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_3458739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458739 prefixEnd_3458739 := by exact prefixLift 3458739
  have htrace : WordTrace (prefixWord ++ tailWord_3458739) baseStart_3458739 baseEnd_3458739 := by
    simpa [prefixWord, tailWord_3458739, baseEnd_3458739] using wordTrace_append hprefix tailTrace_3458739
  have hstable : (prefixWord ++ tailWord_3458739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458739).length < 2 ^ (prefixWord ++ tailWord_3458739).sum := by decide
  have hdescent : baseEnd_3458739 < baseStart_3458739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458801 : List Nat := [1, 2, 2, 2, 2, 5, 8]
def baseStart_3458801 : Nat := 118140960795 + 3458801 * 2 ^ 59
def prefixEnd_3458801 : Nat := 4983230072969 + 3 ^ 40 * 3458801 * 2
def baseEnd_3458801 : Nat := 43852528425971040960019

theorem tailTrace_3458801 : CollatzResearch.WordTrace tailWord_3458801 prefixEnd_3458801 43852528425971040960019 := by
  unfold tailWord_3458801
  simp only [CollatzResearch.WordTrace]
  refine ⟨126152836342362168026592257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84101890894908112017728171 126152836342362168026592257)
  ·
    refine ⟨94614627256771626019944193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126152836342362168026592257 94614627256771626019944193)
    ·
      refine ⟨70960970442578719514958145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94614627256771626019944193 70960970442578719514958145)
      ·
        refine ⟨53220727831934039636218609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70960970442578719514958145 53220727831934039636218609)
        ·
          refine ⟨39915545873950529727163957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53220727831934039636218609 39915545873950529727163957)
          ·
            refine ⟨3742082425682862161921621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39915545873950529727163957 3742082425682862161921621)
            ·
              refine ⟨43852528425971040960019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3742082425682862161921621 43852528425971040960019)
              ·
                rfl

theorem cell22_3458801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 8].length) (baseStart_3458801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458801 prefixEnd_3458801 := by exact prefixLift 3458801
  have htrace : WordTrace (prefixWord ++ tailWord_3458801) baseStart_3458801 baseEnd_3458801 := by
    simpa [prefixWord, tailWord_3458801, baseEnd_3458801] using wordTrace_append hprefix tailTrace_3458801
  have hstable : (prefixWord ++ tailWord_3458801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458801).length < 2 ^ (prefixWord ++ tailWord_3458801).sum := by decide
  have hdescent : baseEnd_3458801 < baseStart_3458801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458818 : List Nat := [3, 4, 1, 1, 1, 1, 4, 7]
def baseStart_3458818 : Nat := 118140960795 + 3458818 * 2 ^ 59
def prefixEnd_3458818 : Nat := 4983230072969 + 3 ^ 40 * 3458818 * 2
def baseEnd_3458818 : Nat := 131558231883181747582829

theorem tailTrace_3458818 : CollatzResearch.WordTrace tailWord_3458818 prefixEnd_3458818 131558231883181747582829 := by
  unfold tailWord_3458818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31538364095825144982490277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84102304255533719953307405 31538364095825144982490277)
  ·
    refine ⟨5913443267967214684216927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31538364095825144982490277 5913443267967214684216927)
    ·
      refine ⟨8870164901950822026325391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5913443267967214684216927 8870164901950822026325391)
      ·
        refine ⟨13305247352926233039488087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8870164901950822026325391 13305247352926233039488087)
        ·
          refine ⟨19957871029389349559232131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13305247352926233039488087 19957871029389349559232131)
          ·
            refine ⟨29936806544084024338848197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19957871029389349559232131 29936806544084024338848197)
            ·
              refine ⟨5613151227015754563534037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29936806544084024338848197 5613151227015754563534037)
              ·
                refine ⟨131558231883181747582829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5613151227015754563534037 131558231883181747582829)
                ·
                  rfl

theorem cell22_3458818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_3458818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458818 prefixEnd_3458818 := by exact prefixLift 3458818
  have htrace : WordTrace (prefixWord ++ tailWord_3458818) baseStart_3458818 baseEnd_3458818 := by
    simpa [prefixWord, tailWord_3458818, baseEnd_3458818] using wordTrace_append hprefix tailTrace_3458818
  have hstable : (prefixWord ++ tailWord_3458818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458818).length < 2 ^ (prefixWord ++ tailWord_3458818).sum := by decide
  have hdescent : baseEnd_3458818 < baseStart_3458818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458867 : List Nat := [1, 1, 1, 2, 7, 1, 1, 4, 1, 3]
def baseStart_3458867 : Nat := 118140960795 + 3458867 * 2 ^ 59
def prefixEnd_3458867 : Nat := 4983230072969 + 3 ^ 40 * 3458867 * 2
def baseEnd_3458867 : Nat := 1184040860650015933770311

theorem tailTrace_3458867 : CollatzResearch.WordTrace tailWord_3458867 prefixEnd_3458867 1184040860650015933770311 := by
  unfold tailWord_3458867
  simp only [CollatzResearch.WordTrace]
  refine ⟨126155243560123061298494855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84103495706748707532329903 126155243560123061298494855)
  ·
    refine ⟨189232865340184591947742283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126155243560123061298494855 189232865340184591947742283)
    ·
      refine ⟨283849298010276887921613425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189232865340184591947742283 283849298010276887921613425)
      ·
        refine ⟨212886973507707665941210069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283849298010276887921613425 212886973507707665941210069)
        ·
          refine ⟨4989538441586898420497111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 212886973507707665941210069 4989538441586898420497111)
          ·
            refine ⟨7484307662380347630745667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989538441586898420497111 7484307662380347630745667)
            ·
              refine ⟨11226461493570521446118501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484307662380347630745667 11226461493570521446118501)
              ·
                refine ⟨2104961530044472771147219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11226461493570521446118501 2104961530044472771147219)
                ·
                  refine ⟨3157442295066709156720829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2104961530044472771147219 3157442295066709156720829)
                  ·
                    refine ⟨1184040860650015933770311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157442295066709156720829 1184040860650015933770311)
                    ·
                      rfl

theorem cell22_3458867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 3].length) (baseStart_3458867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458867 prefixEnd_3458867 := by exact prefixLift 3458867
  have htrace : WordTrace (prefixWord ++ tailWord_3458867) baseStart_3458867 baseEnd_3458867 := by
    simpa [prefixWord, tailWord_3458867, baseEnd_3458867] using wordTrace_append hprefix tailTrace_3458867
  have hstable : (prefixWord ++ tailWord_3458867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458867).length < 2 ^ (prefixWord ++ tailWord_3458867).sum := by decide
  have hdescent : baseEnd_3458867 < baseStart_3458867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458878 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3458878 : Nat := 118140960795 + 3458878 * 2 ^ 59
def prefixEnd_3458878 : Nat := 4983230072969 + 3 ^ 40 * 3458878 * 2
def baseEnd_3458878 : Nat := 1184044626174815571745277

theorem tailTrace_3458878 : CollatzResearch.WordTrace tailWord_3458878 prefixEnd_3458878 1184044626174815571745277 := by
  unfold tailWord_3458878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15769455595385401272143161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84103763175388806784763525 15769455595385401272143161)
  ·
    refine ⟨11827091696539050954107371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15769455595385401272143161 11827091696539050954107371)
    ·
      refine ⟨17740637544808576431161057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827091696539050954107371 17740637544808576431161057)
      ·
        refine ⟨13305478158606432323370793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17740637544808576431161057 13305478158606432323370793)
        ·
          refine ⟨9979108618954824242528095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13305478158606432323370793 9979108618954824242528095)
          ·
            refine ⟨14968662928432236363792143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9979108618954824242528095 14968662928432236363792143)
            ·
              refine ⟨22452994392648354545688215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14968662928432236363792143 22452994392648354545688215)
              ·
                refine ⟨33679491588972531818532323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22452994392648354545688215 33679491588972531818532323)
                ·
                  refine ⟨50519237383458797727798485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33679491588972531818532323 50519237383458797727798485)
                  ·
                    refine ⟨1184044626174815571745277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50519237383458797727798485 1184044626174815571745277)
                    ·
                      rfl

theorem cell22_3458878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3458878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458878 prefixEnd_3458878 := by exact prefixLift 3458878
  have htrace : WordTrace (prefixWord ++ tailWord_3458878) baseStart_3458878 baseEnd_3458878 := by
    simpa [prefixWord, tailWord_3458878, baseEnd_3458878] using wordTrace_append hprefix tailTrace_3458878
  have hstable : (prefixWord ++ tailWord_3458878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458878).length < 2 ^ (prefixWord ++ tailWord_3458878).sum := by decide
  have hdescent : baseEnd_3458878 < baseStart_3458878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3458925 : List Nat := [1, 5, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3458925 : Nat := 118140960795 + 3458925 * 2 ^ 59
def prefixEnd_3458925 : Nat := 4983230072969 + 3 ^ 40 * 3458925 * 2
def baseEnd_3458925 : Nat := 394686905078441038606711

theorem tailTrace_3458925 : CollatzResearch.WordTrace tailWord_3458925 prefixEnd_3458925 394686905078441038606711 := by
  unfold tailWord_3458925
  simp only [CollatzResearch.WordTrace]
  refine ⟨126157358993912937204106229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84104905995941958136070819 126157358993912937204106229)
  ·
    refine ⟨11827252405679337862884959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126157358993912937204106229 11827252405679337862884959)
    ·
      refine ⟨17740878608519006794327439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827252405679337862884959 17740878608519006794327439)
      ·
        refine ⟨26611317912778510191491159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17740878608519006794327439 26611317912778510191491159)
        ·
          refine ⟨39916976869167765287236739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26611317912778510191491159 39916976869167765287236739)
          ·
            refine ⟨59875465303751647930855109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39916976869167765287236739 59875465303751647930855109)
            ·
              refine ⟨11226649744453433987035333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59875465303751647930855109 11226649744453433987035333)
              ·
                refine ⟨2104996827085018872569125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11226649744453433987035333 2104996827085018872569125)
                ·
                  refine ⟨394686905078441038606711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2104996827085018872569125 394686905078441038606711)
                  ·
                    rfl

theorem cell22_3458925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3458925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3458925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3458925 prefixEnd_3458925 := by exact prefixLift 3458925
  have htrace : WordTrace (prefixWord ++ tailWord_3458925) baseStart_3458925 baseEnd_3458925 := by
    simpa [prefixWord, tailWord_3458925, baseEnd_3458925] using wordTrace_append hprefix tailTrace_3458925
  have hstable : (prefixWord ++ tailWord_3458925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3458925).length < 2 ^ (prefixWord ++ tailWord_3458925).sum := by decide
  have hdescent : baseEnd_3458925 < baseStart_3458925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3458925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459077 : List Nat := [1, 3, 1, 1, 2, 5, 2, 3, 4]
def baseStart_3459077 : Nat := 118140960795 + 3459077 * 2 ^ 59
def prefixEnd_3459077 : Nat := 4983230072969 + 3 ^ 40 * 3459077 * 2
def baseEnd_3459077 : Nat := 394704249313881795339889

theorem tailTrace_3459077 : CollatzResearch.WordTrace tailWord_3459077 prefixEnd_3459077 394704249313881795339889 := by
  unfold tailWord_3459077
  simp only [CollatzResearch.WordTrace]
  refine ⟨126162902889362267163639485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84108601926241511442426323 126162902889362267163639485)
  ·
    refine ⟨47311088583510850186364807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126162902889362267163639485 47311088583510850186364807)
    ·
      refine ⟨70966632875266275279547211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47311088583510850186364807 70966632875266275279547211)
      ·
        refine ⟨106449949312899412919320817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70966632875266275279547211 106449949312899412919320817)
        ·
          refine ⟨79837461984674559689490613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106449949312899412919320817 79837461984674559689490613)
          ·
            refine ⟨7484762061063239970889745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79837461984674559689490613 7484762061063239970889745)
            ·
              refine ⟨5613571545797429978167309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7484762061063239970889745 5613571545797429978167309)
              ·
                refine ⟨2105089329674036241812741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5613571545797429978167309 2105089329674036241812741)
                ·
                  refine ⟨394704249313881795339889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105089329674036241812741 394704249313881795339889)
                  ·
                    rfl

theorem cell22_3459077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_3459077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459077 prefixEnd_3459077 := by exact prefixLift 3459077
  have htrace : WordTrace (prefixWord ++ tailWord_3459077) baseStart_3459077 baseEnd_3459077 := by
    simpa [prefixWord, tailWord_3459077, baseEnd_3459077] using wordTrace_append hprefix tailTrace_3459077
  have hstable : (prefixWord ++ tailWord_3459077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459077).length < 2 ^ (prefixWord ++ tailWord_3459077).sum := by decide
  have hdescent : baseEnd_3459077 < baseStart_3459077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459079 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3459079 : Nat := 118140960795 + 3459079 * 2 ^ 59
def prefixEnd_3459079 : Nat := 4983230072969 + 3 ^ 40 * 3459079 * 2
def baseEnd_3459079 : Nat := 1184113432582518047469661

theorem tailTrace_3459079 : CollatzResearch.WordTrace tailWord_3459079 prefixEnd_3459079 1184113432582518047469661 := by
  unfold tailWord_3459079
  simp only [CollatzResearch.WordTrace]
  refine ⟨126162975835355021505212291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84108650556903347670141527 126162975835355021505212291)
  ·
    refine ⟨189244463753032532257818437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126162975835355021505212291 189244463753032532257818437)
    ·
      refine ⟨35483336953693599798340957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189244463753032532257818437 35483336953693599798340957)
      ·
        refine ⟨13306251357635099924377859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35483336953693599798340957 13306251357635099924377859)
        ·
          refine ⟨19959377036452649886566789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306251357635099924377859 19959377036452649886566789)
          ·
            refine ⟨3742383194334871853731273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19959377036452649886566789 3742383194334871853731273)
            ·
              refine ⟨2806787395751153890298455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742383194334871853731273 2806787395751153890298455)
              ·
                refine ⟨4210181093626730835447683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806787395751153890298455 4210181093626730835447683)
                ·
                  refine ⟨6315271640440096253171525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210181093626730835447683 6315271640440096253171525)
                  ·
                    refine ⟨1184113432582518047469661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6315271640440096253171525 1184113432582518047469661)
                    ·
                      rfl

theorem cell22_3459079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3459079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459079 prefixEnd_3459079 := by exact prefixLift 3459079
  have htrace : WordTrace (prefixWord ++ tailWord_3459079) baseStart_3459079 baseEnd_3459079 := by
    simpa [prefixWord, tailWord_3459079, baseEnd_3459079] using wordTrace_append hprefix tailTrace_3459079
  have hstable : (prefixWord ++ tailWord_3459079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459079).length < 2 ^ (prefixWord ++ tailWord_3459079).sum := by decide
  have hdescent : baseEnd_3459079 < baseStart_3459079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459109 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_3459109 : Nat := 118140960795 + 3459109 * 2 ^ 59
def prefixEnd_3459109 : Nat := 4983230072969 + 3 ^ 40 * 3459109 * 2
def baseEnd_3459109 : Nat := 1184123702195607969219569

theorem tailTrace_3459109 : CollatzResearch.WordTrace tailWord_3459109 prefixEnd_3459109 1184123702195607969219569 := by
  unfold tailWord_3459109
  simp only [CollatzResearch.WordTrace]
  refine ⟨126164070025246336628804381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84109380016830891085869587 126164070025246336628804381)
  ·
    refine ⟨47311526259467376235801643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126164070025246336628804381 47311526259467376235801643)
    ·
      refine ⟨70967289389201064353702465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47311526259467376235801643 70967289389201064353702465)
      ·
        refine ⟨53225467041900798265276849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70967289389201064353702465 53225467041900798265276849)
        ·
          refine ⟨39919100281425598698957637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53225467041900798265276849 39919100281425598698957637)
          ·
            refine ⟨7484831302767299756054557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39919100281425598698957637 7484831302767299756054557)
            ·
              refine ⟨2806811738537737408520459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7484831302767299756054557 2806811738537737408520459)
              ·
                refine ⟨4210217607806606112780689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806811738537737408520459 4210217607806606112780689)
                ·
                  refine ⟨3157663205854954584585517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210217607806606112780689 3157663205854954584585517)
                  ·
                    refine ⟨1184123702195607969219569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157663205854954584585517 1184123702195607969219569)
                    ·
                      rfl

theorem cell22_3459109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_3459109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459109 prefixEnd_3459109 := by exact prefixLift 3459109
  have htrace : WordTrace (prefixWord ++ tailWord_3459109) baseStart_3459109 baseEnd_3459109 := by
    simpa [prefixWord, tailWord_3459109, baseEnd_3459109] using wordTrace_append hprefix tailTrace_3459109
  have hstable : (prefixWord ++ tailWord_3459109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459109).length < 2 ^ (prefixWord ++ tailWord_3459109).sum := by decide
  have hdescent : baseEnd_3459109 < baseStart_3459109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459122 : List Nat := [3, 2, 1, 1, 2, 5, 2, 6]
def baseStart_3459122 : Nat := 118140960795 + 3459122 * 2 ^ 59
def prefixEnd_3459122 : Nat := 4983230072969 + 3 ^ 40 * 3459122 * 2
def baseEnd_3459122 : Nat := 131569794706808918738281

theorem tailTrace_3459122 : CollatzResearch.WordTrace tailWord_3459122 prefixEnd_3459122 131569794706808918738281 := by
  unfold tailWord_3459122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31541136043549809962256905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84109696116132826566018413 31541136043549809962256905)
  ·
    refine ⟨23655852032662357471692679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31541136043549809962256905 23655852032662357471692679)
    ·
      refine ⟨35483778048993536207539019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23655852032662357471692679 35483778048993536207539019)
      ·
        refine ⟨53225667073490304311308529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35483778048993536207539019 53225667073490304311308529)
        ·
          refine ⟨39919250305117728233481397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53225667073490304311308529 39919250305117728233481397)
          ·
            refine ⟨3742429716104787021888881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39919250305117728233481397 3742429716104787021888881)
            ·
              refine ⟨2806822287078590266416661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742429716104787021888881 2806822287078590266416661)
              ·
                refine ⟨131569794706808918738281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2806822287078590266416661 131569794706808918738281)
                ·
                  rfl

theorem cell22_3459122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_3459122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459122 prefixEnd_3459122 := by exact prefixLift 3459122
  have htrace : WordTrace (prefixWord ++ tailWord_3459122) baseStart_3459122 baseEnd_3459122 := by
    simpa [prefixWord, tailWord_3459122, baseEnd_3459122] using wordTrace_append hprefix tailTrace_3459122
  have hstable : (prefixWord ++ tailWord_3459122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459122).length < 2 ^ (prefixWord ++ tailWord_3459122).sum := by decide
  have hdescent : baseEnd_3459122 < baseStart_3459122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459150 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_3459150 : Nat := 118140960795 + 3459150 * 2 ^ 59
def prefixEnd_3459150 : Nat := 4983230072969 + 3 ^ 40 * 3459150 * 2
def baseEnd_3459150 : Nat := 394712579111165842981481

theorem tailTrace_3459150 : CollatzResearch.WordTrace tailWord_3459150 prefixEnd_3459150 394712579111165842981481 := by
  unfold tailWord_3459150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15770695677262225078880863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84110376945398533754031269 15770695677262225078880863)
  ·
    refine ⟨23656043515893337618321295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15770695677262225078880863 23656043515893337618321295)
    ·
      refine ⟨35484065273840006427481943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23656043515893337618321295 35484065273840006427481943)
      ·
        refine ⟨53226097910760009641222915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35484065273840006427481943 53226097910760009641222915)
        ·
          refine ⟨79839146866140014461834373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53226097910760009641222915 79839146866140014461834373)
          ·
            refine ⟨14969840037401252711593945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79839146866140014461834373 14969840037401252711593945)
            ·
              refine ⟨11227380028050939533695459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14969840037401252711593945 11227380028050939533695459)
              ·
                refine ⟨16841070042076409300543189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11227380028050939533695459 16841070042076409300543189)
                ·
                  refine ⟨394712579111165842981481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16841070042076409300543189 394712579111165842981481)
                  ·
                    rfl

theorem cell22_3459150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_3459150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459150 prefixEnd_3459150 := by exact prefixLift 3459150
  have htrace : WordTrace (prefixWord ++ tailWord_3459150) baseStart_3459150 baseEnd_3459150 := by
    simpa [prefixWord, tailWord_3459150, baseEnd_3459150] using wordTrace_append hprefix tailTrace_3459150
  have hstable : (prefixWord ++ tailWord_3459150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459150).length < 2 ^ (prefixWord ++ tailWord_3459150).sum := by decide
  have hdescent : baseEnd_3459150 < baseStart_3459150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459225 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_3459225 : Nat := 118140960795 + 3459225 * 2 ^ 59
def prefixEnd_3459225 : Nat := 4983230072969 + 3 ^ 40 * 3459225 * 2
def baseEnd_3459225 : Nat := 1184163411366222333319213

theorem tailTrace_3459225 : CollatzResearch.WordTrace tailWord_3459225 prefixEnd_3459225 1184163411366222333319213 := by
  unfold tailWord_3459225
  simp only [CollatzResearch.WordTrace]
  refine ⟨126168300892826088440027129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84112200595217392293351419 126168300892826088440027129)
  ·
    refine ⟨94626225669619566330020347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126168300892826088440027129 94626225669619566330020347)
    ·
      refine ⟨141939338504429349495030521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94626225669619566330020347 141939338504429349495030521)
      ·
        refine ⟨106454503878322012121272891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141939338504429349495030521 106454503878322012121272891)
        ·
          refine ⟨159681755817483018181909337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106454503878322012121272891 159681755817483018181909337)
          ·
            refine ⟨119761316863112263636432003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159681755817483018181909337 119761316863112263636432003)
            ·
              refine ⟨179641975294668395454648005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119761316863112263636432003 179641975294668395454648005)
              ·
                refine ⟨33682870367750324147746501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179641975294668395454648005 33682870367750324147746501)
                ·
                  refine ⟨6315538193953185777702469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33682870367750324147746501 6315538193953185777702469)
                  ·
                    refine ⟨1184163411366222333319213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6315538193953185777702469 1184163411366222333319213)
                    ·
                      rfl

theorem cell22_3459225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_3459225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459225 prefixEnd_3459225 := by exact prefixLift 3459225
  have htrace : WordTrace (prefixWord ++ tailWord_3459225) baseStart_3459225 baseEnd_3459225 := by
    simpa [prefixWord, tailWord_3459225, baseEnd_3459225] using wordTrace_append hprefix tailTrace_3459225
  have hstable : (prefixWord ++ tailWord_3459225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459225).length < 2 ^ (prefixWord ++ tailWord_3459225).sum := by decide
  have hdescent : baseEnd_3459225 < baseStart_3459225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459227 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 2, 3]
def baseStart_3459227 : Nat := 118140960795 + 3459227 * 2 ^ 59
def prefixEnd_3459227 : Nat := 4983230072969 + 3 ^ 40 * 3459227 * 2
def baseEnd_3459227 : Nat := 1184164096007094994769207

theorem tailTrace_3459227 : CollatzResearch.WordTrace tailWord_3459227 prefixEnd_3459227 1184164096007094994769207 := by
  unfold tailWord_3459227
  simp only [CollatzResearch.WordTrace]
  refine ⟨126168373838818842781599935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84112249225879228521066623 126168373838818842781599935)
  ·
    refine ⟨189252560758228264172399903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126168373838818842781599935 189252560758228264172399903)
    ·
      refine ⟨283878841137342396258599855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189252560758228264172399903 283878841137342396258599855)
      ·
        refine ⟨425818261706013594387899783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283878841137342396258599855 425818261706013594387899783)
        ·
          refine ⟨638727392559020391581849675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425818261706013594387899783 638727392559020391581849675)
          ·
            refine ⟨958091088838530587372774513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638727392559020391581849675 958091088838530587372774513)
            ·
              refine ⟨718568316628897940529580885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958091088838530587372774513 718568316628897940529580885)
              ·
                refine ⟨4210361230247448870290513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 718568316628897940529580885 4210361230247448870290513)
                ·
                  refine ⟨3157770922685586652717885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210361230247448870290513 3157770922685586652717885)
                  ·
                    refine ⟨1184164096007094994769207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157770922685586652717885 1184164096007094994769207)
                    ·
                      rfl

theorem cell22_3459227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 3].length) (baseStart_3459227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459227 prefixEnd_3459227 := by exact prefixLift 3459227
  have htrace : WordTrace (prefixWord ++ tailWord_3459227) baseStart_3459227 baseEnd_3459227 := by
    simpa [prefixWord, tailWord_3459227, baseEnd_3459227] using wordTrace_append hprefix tailTrace_3459227
  have hstable : (prefixWord ++ tailWord_3459227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459227).length < 2 ^ (prefixWord ++ tailWord_3459227).sum := by decide
  have hdescent : baseEnd_3459227 < baseStart_3459227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459336 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 5]
def baseStart_3459336 : Nat := 118140960795 + 3459336 * 2 ^ 59
def prefixEnd_3459336 : Nat := 4983230072969 + 3 ^ 40 * 3459336 * 2
def baseEnd_3459336 : Nat := 394733802978218347931291

theorem tailTrace_3459336 : CollatzResearch.WordTrace tailWord_3459336 prefixEnd_3459336 394733802978218347931291 := by
  unfold tailWord_3459336
  simp only [CollatzResearch.WordTrace]
  refine ⟨63086174697711977198658931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84114899596949302931545241 63086174697711977198658931)
  ·
    refine ⟨94629262046567965797988397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63086174697711977198658931 94629262046567965797988397)
    ·
      refine ⟨35485973267462987174245649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94629262046567965797988397 35485973267462987174245649)
      ·
        refine ⟨26614479950597240380684237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35485973267462987174245649 26614479950597240380684237)
        ·
          refine ⟨9980429981473965142756589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26614479950597240380684237 9980429981473965142756589)
          ·
            refine ⟨3742661243052736928533721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9980429981473965142756589 3742661243052736928533721)
            ·
              refine ⟨2806995932289552696400291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742661243052736928533721 2806995932289552696400291)
              ·
                refine ⟨4210493898434329044600437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806995932289552696400291 4210493898434329044600437)
                ·
                  refine ⟨394733802978218347931291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4210493898434329044600437 394733802978218347931291)
                  ·
                    rfl

theorem cell22_3459336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_3459336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459336 prefixEnd_3459336 := by exact prefixLift 3459336
  have htrace : WordTrace (prefixWord ++ tailWord_3459336) baseStart_3459336 baseEnd_3459336 := by
    simpa [prefixWord, tailWord_3459336, baseEnd_3459336] using wordTrace_append hprefix tailTrace_3459336
  have hstable : (prefixWord ++ tailWord_3459336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459336).length < 2 ^ (prefixWord ++ tailWord_3459336).sum := by decide
  have hdescent : baseEnd_3459336 < baseStart_3459336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459349 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3459349 : Nat := 118140960795 + 3459349 * 2 ^ 59
def prefixEnd_3459349 : Nat := 4983230072969 + 3 ^ 40 * 3459349 * 2
def baseEnd_3459349 : Nat := 1184205859100327343218833

theorem tailTrace_3459349 : CollatzResearch.WordTrace tailWord_3459349 prefixEnd_3459349 1184205859100327343218833 := by
  unfold tailWord_3459349
  simp only [CollatzResearch.WordTrace]
  refine ⟨126172823544376857617541101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84115215696251238411694067 126172823544376857617541101)
  ·
    refine ⟨47314808829141321606577913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126172823544376857617541101 47314808829141321606577913)
    ·
      refine ⟨35486106621855991204933435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47314808829141321606577913 35486106621855991204933435)
      ·
        refine ⟨53229159932783986807400153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35486106621855991204933435 53229159932783986807400153)
        ·
          refine ⟨39921869949587990105550115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53229159932783986807400153 39921869949587990105550115)
          ·
            refine ⟨59882804924381985158325173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39921869949587990105550115 59882804924381985158325173)
            ·
              refine ⟨5614012961660811108592985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59882804924381985158325173 5614012961660811108592985)
              ·
                refine ⟨4210509721245608331444739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5614012961660811108592985 4210509721245608331444739)
                ·
                  refine ⟨6315764581868412497167109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4210509721245608331444739 6315764581868412497167109)
                  ·
                    refine ⟨1184205859100327343218833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6315764581868412497167109 1184205859100327343218833)
                    ·
                      rfl

theorem cell22_3459349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3459349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459349 prefixEnd_3459349 := by exact prefixLift 3459349
  have htrace : WordTrace (prefixWord ++ tailWord_3459349) baseStart_3459349 baseEnd_3459349 := by
    simpa [prefixWord, tailWord_3459349, baseEnd_3459349] using wordTrace_append hprefix tailTrace_3459349
  have hstable : (prefixWord ++ tailWord_3459349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459349).length < 2 ^ (prefixWord ++ tailWord_3459349).sum := by decide
  have hdescent : baseEnd_3459349 < baseStart_3459349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459374 : List Nat := [4, 1, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3459374 : Nat := 118140960795 + 3459374 * 2 ^ 59
def prefixEnd_3459374 : Nat := 4983230072969 + 3 ^ 40 * 3459374 * 2
def baseEnd_3459374 : Nat := 1184214417111235611343757

theorem tailTrace_3459374 : CollatzResearch.WordTrace tailWord_3459374 prefixEnd_3459374 1184214417111235611343757 := by
  unfold tailWord_3459374
  simp only [CollatzResearch.WordTrace]
  refine ⟨15771716921160785860900147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84115823579524191258134117 15771716921160785860900147)
  ·
    refine ⟨23657575381741178791350221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15771716921160785860900147 23657575381741178791350221)
    ·
      refine ⟨8871590768152942046756333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23657575381741178791350221 8871590768152942046756333)
      ·
        refine ⟨3326846538057353267533625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8871590768152942046756333 3326846538057353267533625)
        ·
          refine ⟨2495134903543014950650219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3326846538057353267533625 2495134903543014950650219)
          ·
            refine ⟨3742702355314522425975329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495134903543014950650219 3742702355314522425975329)
            ·
              refine ⟨2807026766485891819481497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742702355314522425975329 2807026766485891819481497)
              ·
                refine ⟨2105270074864418864611123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2807026766485891819481497 2105270074864418864611123)
                ·
                  refine ⟨3157905112296628296916685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2105270074864418864611123 3157905112296628296916685)
                  ·
                    refine ⟨1184214417111235611343757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3157905112296628296916685 1184214417111235611343757)
                    ·
                      rfl

theorem cell22_3459374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3459374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459374 prefixEnd_3459374 := by exact prefixLift 3459374
  have htrace : WordTrace (prefixWord ++ tailWord_3459374) baseStart_3459374 baseEnd_3459374 := by
    simpa [prefixWord, tailWord_3459374, baseEnd_3459374] using wordTrace_append hprefix tailTrace_3459374
  have hstable : (prefixWord ++ tailWord_3459374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459374).length < 2 ^ (prefixWord ++ tailWord_3459374).sum := by decide
  have hdescent : baseEnd_3459374 < baseStart_3459374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459409 : List Nat := [1, 2, 2, 1, 4, 3, 3, 6]
def baseStart_3459409 : Nat := 118140960795 + 3459409 * 2 ^ 59
def prefixEnd_3459409 : Nat := 4983230072969 + 3 ^ 40 * 3459409 * 2
def baseEnd_3459409 : Nat := 131580710925167465190961

theorem tailTrace_3459409 : CollatzResearch.WordTrace tailWord_3459409 prefixEnd_3459409 131580710925167465190961 := by
  unfold tailWord_3459409
  simp only [CollatzResearch.WordTrace]
  refine ⟨126175011924159487864725281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84116674616106325243150187 126175011924159487864725281)
  ·
    refine ⟨94631258943119615898543961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126175011924159487864725281 94631258943119615898543961)
    ·
      refine ⟨70973444207339711923907971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94631258943119615898543961 70973444207339711923907971)
      ·
        refine ⟨106460166311009567885861957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70973444207339711923907971 106460166311009567885861957)
        ·
          refine ⟨19961281183314293978599117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106460166311009567885861957 19961281183314293978599117)
          ·
            refine ⟨7485480443742860241974669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19961281183314293978599117 7485480443742860241974669)
            ·
              refine ⟨2807055166403572590740501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7485480443742860241974669 2807055166403572590740501)
              ·
                refine ⟨131580710925167465190961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2807055166403572590740501 131580710925167465190961)
                ·
                  rfl

theorem cell22_3459409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 6].length) (baseStart_3459409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459409 prefixEnd_3459409 := by exact prefixLift 3459409
  have htrace : WordTrace (prefixWord ++ tailWord_3459409) baseStart_3459409 baseEnd_3459409 := by
    simpa [prefixWord, tailWord_3459409, baseEnd_3459409] using wordTrace_append hprefix tailTrace_3459409
  have hstable : (prefixWord ++ tailWord_3459409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459409).length < 2 ^ (prefixWord ++ tailWord_3459409).sum := by decide
  have hdescent : baseEnd_3459409 < baseStart_3459409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459452 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_3459452 : Nat := 118140960795 + 3459452 * 2 ^ 59
def prefixEnd_3459452 : Nat := 4983230072969 + 3 ^ 40 * 3459452 * 2
def baseEnd_3459452 : Nat := 1184241118105269407893517

theorem tailTrace_3459452 : CollatzResearch.WordTrace tailWord_3459452 prefixEnd_3459452 1184241118105269407893517 := by
  unfold tailWord_3459452
  simp only [CollatzResearch.WordTrace]
  refine ⟨63088290131501853104270305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84117720175335804139027073 63088290131501853104270305)
  ·
    refine ⟨47316217598626389828202729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63088290131501853104270305 47316217598626389828202729)
    ·
      refine ⟨35487163198969792371152047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47316217598626389828202729 35487163198969792371152047)
      ·
        refine ⟨53230744798454688556728071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35487163198969792371152047 53230744798454688556728071)
        ·
          refine ⟨79846117197682032835092107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53230744798454688556728071 79846117197682032835092107)
          ·
            refine ⟨119769175796523049252638161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79846117197682032835092107 119769175796523049252638161)
            ·
              refine ⟨89826881847392286939478621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119769175796523049252638161 89826881847392286939478621)
              ·
                refine ⟨33685080692772107602304483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89826881847392286939478621 33685080692772107602304483)
                ·
                  refine ⟨50527621039158161403456725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33685080692772107602304483 50527621039158161403456725)
                  ·
                    refine ⟨1184241118105269407893517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50527621039158161403456725 1184241118105269407893517)
                    ·
                      rfl

theorem cell22_3459452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_3459452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459452 prefixEnd_3459452 := by exact prefixLift 3459452
  have htrace : WordTrace (prefixWord ++ tailWord_3459452) baseStart_3459452 baseEnd_3459452 := by
    simpa [prefixWord, tailWord_3459452, baseEnd_3459452] using wordTrace_append hprefix tailTrace_3459452
  have hstable : (prefixWord ++ tailWord_3459452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459452).length < 2 ^ (prefixWord ++ tailWord_3459452).sum := by decide
  have hdescent : baseEnd_3459452 < baseStart_3459452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459529 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_3459529 : Nat := 118140960795 + 3459529 * 2 ^ 59
def prefixEnd_3459529 : Nat := 4983230072969 + 3 ^ 40 * 3459529 * 2
def baseEnd_3459529 : Nat := 1184267476778866873718281

theorem tailTrace_3459529 : CollatzResearch.WordTrace tailWord_3459529 prefixEnd_3459529 1184267476778866873718281 := by
  unfold tailWord_3459529
  simp only [CollatzResearch.WordTrace]
  refine ⟨126179388683724748359093641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84119592455816498906062427 126179388683724748359093641)
  ·
    refine ⟨94634541512793561269320231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126179388683724748359093641 94634541512793561269320231)
    ·
      refine ⟨141951812269190341903980347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94634541512793561269320231 141951812269190341903980347)
      ·
        refine ⟨212927718403785512855970521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141951812269190341903980347 212927718403785512855970521)
        ·
          refine ⟨159695788802839134641977891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212927718403785512855970521 159695788802839134641977891)
          ·
            refine ⟨239543683204258701962966837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159695788802839134641977891 239543683204258701962966837)
            ·
              refine ⟨22457220300399253309028141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239543683204258701962966837 22457220300399253309028141)
              ·
                refine ⟨8421457612649719990885553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22457220300399253309028141 8421457612649719990885553)
                ·
                  refine ⟨6316093209487289993164165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8421457612649719990885553 6316093209487289993164165)
                  ·
                    refine ⟨1184267476778866873718281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6316093209487289993164165 1184267476778866873718281)
                    ·
                      rfl

theorem cell22_3459529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_3459529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459529 prefixEnd_3459529 := by exact prefixLift 3459529
  have htrace : WordTrace (prefixWord ++ tailWord_3459529) baseStart_3459529 baseEnd_3459529 := by
    simpa [prefixWord, tailWord_3459529, baseEnd_3459529] using wordTrace_append hprefix tailTrace_3459529
  have hstable : (prefixWord ++ tailWord_3459529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459529).length < 2 ^ (prefixWord ++ tailWord_3459529).sum := by decide
  have hdescent : baseEnd_3459529 < baseStart_3459529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459576 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 3, 3]
def baseStart_3459576 : Nat := 118140960795 + 3459576 * 2 ^ 59
def prefixEnd_3459576 : Nat := 4983230072969 + 3 ^ 40 * 3459576 * 2
def baseEnd_3459576 : Nat := 1184283565839374417793137

theorem tailTrace_3459576 : CollatzResearch.WordTrace tailWord_3459576 prefixEnd_3459576 1184283565839374417793137 := by
  unfold tailWord_3459576
  simp only [CollatzResearch.WordTrace]
  refine ⟨63090551457277237693027291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84120735276369650257369721 63090551457277237693027291)
  ·
    refine ⟨94635827185915856539540937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63090551457277237693027291 94635827185915856539540937)
    ·
      refine ⟨70976870389436892404655703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94635827185915856539540937 70976870389436892404655703)
      ·
        refine ⟨106465305584155338606983555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70976870389436892404655703 106465305584155338606983555)
        ·
          refine ⟨159697958376233007910475333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106465305584155338606983555 159697958376233007910475333)
          ·
            refine ⟨29943367195543688983214125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159697958376233007910475333 29943367195543688983214125)
            ·
              refine ⟨11228762698328883368705297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29943367195543688983214125 11228762698328883368705297)
              ·
                refine ⟨8421572023746662526528973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11228762698328883368705297 8421572023746662526528973)
                ·
                  refine ⟨3158089508904998447448365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8421572023746662526528973 3158089508904998447448365)
                  ·
                    refine ⟨1184283565839374417793137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158089508904998447448365 1184283565839374417793137)
                    ·
                      rfl

theorem cell22_3459576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_3459576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459576 prefixEnd_3459576 := by exact prefixLift 3459576
  have htrace : WordTrace (prefixWord ++ tailWord_3459576) baseStart_3459576 baseEnd_3459576 := by
    simpa [prefixWord, tailWord_3459576, baseEnd_3459576] using wordTrace_append hprefix tailTrace_3459576
  have hstable : (prefixWord ++ tailWord_3459576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459576).length < 2 ^ (prefixWord ++ tailWord_3459576).sum := by decide
  have hdescent : baseEnd_3459576 < baseStart_3459576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459629 : List Nat := [1, 5, 4, 1, 2, 1, 2, 6]
def baseStart_3459629 : Nat := 118140960795 + 3459629 * 2 ^ 59
def prefixEnd_3459629 : Nat := 4983230072969 + 3 ^ 40 * 3459629 * 2
def baseEnd_3459629 : Nat := 131589078758055549579775

theorem tailTrace_3459629 : CollatzResearch.WordTrace tailWord_3459629 prefixEnd_3459629 131589078758055549579775 := by
  unfold tailWord_3459629
  simp only [CollatzResearch.WordTrace]
  refine ⟨126183035983362465437733941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84122023988908310291822627 126183035983362465437733941)
  ·
    refine ⟨11829659623440231134787557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126183035983362465437733941 11829659623440231134787557)
    ·
      refine ⟨2218061179395043337772667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11829659623440231134787557 2218061179395043337772667)
      ·
        refine ⟨3327091769092565006659001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218061179395043337772667 3327091769092565006659001)
        ·
          refine ⟨2495318826819423754994251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3327091769092565006659001 2495318826819423754994251)
          ·
            refine ⟨3742978240229135632491377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2495318826819423754994251 3742978240229135632491377)
            ·
              refine ⟨2807233680171851724368533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742978240229135632491377 2807233680171851724368533)
              ·
                refine ⟨131589078758055549579775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2807233680171851724368533 131589078758055549579775)
                ·
                  rfl

theorem cell22_3459629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 6].length) (baseStart_3459629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459629 prefixEnd_3459629 := by exact prefixLift 3459629
  have htrace : WordTrace (prefixWord ++ tailWord_3459629) baseStart_3459629 baseEnd_3459629 := by
    simpa [prefixWord, tailWord_3459629, baseEnd_3459629] using wordTrace_append hprefix tailTrace_3459629
  have hstable : (prefixWord ++ tailWord_3459629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459629).length < 2 ^ (prefixWord ++ tailWord_3459629).sum := by decide
  have hdescent : baseEnd_3459629 < baseStart_3459629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459664 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_3459664 : Nat := 118140960795 + 3459664 * 2 ^ 59
def prefixEnd_3459664 : Nat := 4983230072969 + 3 ^ 40 * 3459664 * 2
def baseEnd_3459664 : Nat := 1184313690037771521592867

theorem tailTrace_3459664 : CollatzResearch.WordTrace tailWord_3459664 prefixEnd_3459664 1184313690037771521592867 := by
  unfold tailWord_3459664
  simp only [CollatzResearch.WordTrace]
  refine ⟨63092156269117833207629023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84122875025490444276838697 63092156269117833207629023)
  ·
    refine ⟨94638234403676749811443535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63092156269117833207629023 94638234403676749811443535)
    ·
      refine ⟨141957351605515124717165303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94638234403676749811443535 141957351605515124717165303)
      ·
        refine ⟨212936027408272687075747955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141957351605515124717165303 212936027408272687075747955)
        ·
          refine ⟨319404041112409030613621933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212936027408272687075747955 319404041112409030613621933)
          ·
            refine ⟨119776515417153386480108225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319404041112409030613621933 119776515417153386480108225)
            ·
              refine ⟨89832386562865039860081169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119776515417153386480108225 89832386562865039860081169)
              ·
                refine ⟨67374289922148779895060877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89832386562865039860081169 67374289922148779895060877)
                ·
                  refine ⟨25265358720805792460647829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67374289922148779895060877 25265358720805792460647829)
                  ·
                    refine ⟨1184313690037771521592867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25265358720805792460647829 1184313690037771521592867)
                    ·
                      rfl

theorem cell22_3459664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_3459664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459664 prefixEnd_3459664 := by exact prefixLift 3459664
  have htrace : WordTrace (prefixWord ++ tailWord_3459664) baseStart_3459664 baseEnd_3459664 := by
    simpa [prefixWord, tailWord_3459664, baseEnd_3459664] using wordTrace_append hprefix tailTrace_3459664
  have hstable : (prefixWord ++ tailWord_3459664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459664).length < 2 ^ (prefixWord ++ tailWord_3459664).sum := by decide
  have hdescent : baseEnd_3459664 < baseStart_3459664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459668 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 6]
def baseStart_3459668 : Nat := 118140960795 + 3459668 * 2 ^ 59
def prefixEnd_3459668 : Nat := 4983230072969 + 3 ^ 40 * 3459668 * 2
def baseEnd_3459668 : Nat := 394771686439838948164285

theorem tailTrace_3459668 : CollatzResearch.WordTrace tailWord_3459668 prefixEnd_3459668 394771686439838948164285 := by
  unfold tailWord_3459668
  simp only [CollatzResearch.WordTrace]
  refine ⟨63092229215110587549201829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84122972286814116732269105 63092229215110587549201829)
  ·
    refine ⟨11829792977833235165475343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63092229215110587549201829 11829792977833235165475343)
    ·
      refine ⟨17744689466749852748213015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11829792977833235165475343 17744689466749852748213015)
      ·
        refine ⟨26617034200124779122319523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17744689466749852748213015 26617034200124779122319523)
        ·
          refine ⟨39925551300187168683479285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26617034200124779122319523 39925551300187168683479285)
          ·
            refine ⟨3743020434392547064076183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39925551300187168683479285 3743020434392547064076183)
            ·
              refine ⟨5614530651588820596114275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3743020434392547064076183 5614530651588820596114275)
              ·
                refine ⟨8421795977383230894171413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5614530651588820596114275 8421795977383230894171413)
                ·
                  refine ⟨394771686439838948164285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8421795977383230894171413 394771686439838948164285)
                  ·
                    rfl

theorem cell22_3459668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_3459668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459668 prefixEnd_3459668 := by exact prefixLift 3459668
  have htrace : WordTrace (prefixWord ++ tailWord_3459668) baseStart_3459668 baseEnd_3459668 := by
    simpa [prefixWord, tailWord_3459668, baseEnd_3459668] using wordTrace_append hprefix tailTrace_3459668
  have hstable : (prefixWord ++ tailWord_3459668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459668).length < 2 ^ (prefixWord ++ tailWord_3459668).sum := by decide
  have hdescent : baseEnd_3459668 < baseStart_3459668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459683 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 2, 3]
def baseStart_3459683 : Nat := 118140960795 + 3459683 * 2 ^ 59
def prefixEnd_3459683 : Nat := 4983230072969 + 3 ^ 40 * 3459683 * 2
def baseEnd_3459683 : Nat := 1184320194126061805367809

theorem tailTrace_3459683 : CollatzResearch.WordTrace tailWord_3459683 prefixEnd_3459683 1184320194126061805367809 := by
  unfold tailWord_3459683
  simp only [CollatzResearch.WordTrace]
  refine ⟨126185005525166832660199703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84123337016777888440133135 126185005525166832660199703)
  ·
    refine ⟨189277508287750248990299555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126185005525166832660199703 189277508287750248990299555)
    ·
      refine ⟨283916262431625373485449333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189277508287750248990299555 283916262431625373485449333)
      ·
        refine ⟨26617149602964878764260875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283916262431625373485449333 26617149602964878764260875)
        ·
          refine ⟨39925724404447318146391313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26617149602964878764260875 39925724404447318146391313)
          ·
            refine ⟨29944293303335488609793485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39925724404447318146391313 29944293303335488609793485)
            ·
              refine ⟨11229109988750808228672557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29944293303335488609793485 11229109988750808228672557)
              ·
                refine ⟨4210916245781553085752209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11229109988750808228672557 4210916245781553085752209)
                ·
                  refine ⟨3158187184336164814314157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4210916245781553085752209 3158187184336164814314157)
                  ·
                    refine ⟨1184320194126061805367809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158187184336164814314157 1184320194126061805367809)
                    ·
                      rfl

theorem cell22_3459683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 3].length) (baseStart_3459683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459683 prefixEnd_3459683 := by exact prefixLift 3459683
  have htrace : WordTrace (prefixWord ++ tailWord_3459683) baseStart_3459683 baseEnd_3459683 := by
    simpa [prefixWord, tailWord_3459683, baseEnd_3459683] using wordTrace_append hprefix tailTrace_3459683
  have hstable : (prefixWord ++ tailWord_3459683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459683).length < 2 ^ (prefixWord ++ tailWord_3459683).sum := by decide
  have hdescent : baseEnd_3459683 < baseStart_3459683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3459711 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 7, 3]
def baseStart_3459711 : Nat := 118140960795 + 3459711 * 2 ^ 59
def prefixEnd_3459711 : Nat := 4983230072969 + 3 ^ 40 * 3459711 * 2
def baseEnd_3459711 : Nat := 1184329779098279065667723

theorem tailTrace_3459711 : CollatzResearch.WordTrace tailWord_3459711 prefixEnd_3459711 1184329779098279065667723 := by
  unfold tailWord_3459711
  simp only [CollatzResearch.WordTrace]
  refine ⟨126186026769065393442218987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84124017846043595628145991 126186026769065393442218987)
  ·
    refine ⟨189279040153598090163328481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126186026769065393442218987 189279040153598090163328481)
    ·
      refine ⟨141959280115198567622496361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189279040153598090163328481 141959280115198567622496361)
      ·
        refine ⟨106469460086398925716872271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141959280115198567622496361 106469460086398925716872271)
        ·
          refine ⟨159704190129598388575308407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106469460086398925716872271 159704190129598388575308407)
          ·
            refine ⟨239556285194397582862962611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159704190129598388575308407 239556285194397582862962611)
            ·
              refine ⟨359334427791596374294443917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239556285194397582862962611 359334427791596374294443917)
              ·
                refine ⟨134750410421848640360416469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359334427791596374294443917 134750410421848640360416469)
                ·
                  refine ⟨3158212744262077508447261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 134750410421848640360416469 3158212744262077508447261)
                  ·
                    refine ⟨1184329779098279065667723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158212744262077508447261 1184329779098279065667723)
                    ·
                      rfl

theorem cell22_3459711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_3459711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3459711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3459711 prefixEnd_3459711 := by exact prefixLift 3459711
  have htrace : WordTrace (prefixWord ++ tailWord_3459711) baseStart_3459711 baseEnd_3459711 := by
    simpa [prefixWord, tailWord_3459711, baseEnd_3459711] using wordTrace_append hprefix tailTrace_3459711
  have hstable : (prefixWord ++ tailWord_3459711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3459711).length < 2 ^ (prefixWord ++ tailWord_3459711).sum := by decide
  have hdescent : baseEnd_3459711 < baseStart_3459711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3459711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
