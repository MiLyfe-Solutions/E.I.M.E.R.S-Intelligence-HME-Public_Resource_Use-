import V185TrunkScan21Chunk080

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_983093 : List Nat := [1, 3, 3, 1, 1, 1, 11]
def baseStart_983093 : Nat := 118140960795 + 983093 * 2 ^ 59
def prefixEnd_983093 : Nat := 4983230072969 + 3 ^ 40 * 983093 * 2
def baseEnd_983093 : Nat := 24928357386203821126733

theorem tailTrace_983093 : CollatzResearch.WordTrace tailWord_983093 prefixEnd_983093 24928357386203821126733 := by
  unfold tailWord_983093
  simp only [CollatzResearch.WordTrace]
  refine ⟨35856347427429434762393933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23904231618286289841595955 35856347427429434762393933)
  ·
    refine ⟨13446130285286038035897725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35856347427429434762393933 13446130285286038035897725)
    ·
      refine ⟨5042298856982264263461647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13446130285286038035897725 5042298856982264263461647)
      ·
        refine ⟨7563448285473396395192471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042298856982264263461647 7563448285473396395192471)
        ·
          refine ⟨11345172428210094592788707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563448285473396395192471 11345172428210094592788707)
          ·
            refine ⟨17017758642315141889183061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345172428210094592788707 17017758642315141889183061)
            ·
              refine ⟨24928357386203821126733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17017758642315141889183061 24928357386203821126733)
              ·
                rfl

theorem cell21_983093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 11].length) (baseStart_983093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983093 prefixEnd_983093 := by exact prefixLift 983093
  have htrace : WordTrace (prefixWord ++ tailWord_983093) baseStart_983093 baseEnd_983093 := by
    simpa [prefixWord, tailWord_983093, baseEnd_983093] using wordTrace_append hprefix tailTrace_983093
  have hstable : (prefixWord ++ tailWord_983093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983093).length < 2 ^ (prefixWord ++ tailWord_983093).sum := by decide
  have hdescent : baseEnd_983093 < baseStart_983093 := by decide
  rcases family_descends (prefixWord ++ tailWord_983093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983124 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_983124 : Nat := 118140960795 + 983124 * 2 ^ 59
def prefixEnd_983124 : Nat := 4983230072969 + 3 ^ 40 * 983124 * 2
def baseEnd_983124 : Nat := 224362291098185225123867

theorem tailTrace_983124 : CollatzResearch.WordTrace tailWord_983124 prefixEnd_983124 224362291098185225123867 := by
  unfold tailWord_983124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928739045158563528386213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23904985393544751371181617 17928739045158563528386213)
  ·
    refine ⟨3361638570967230661572415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17928739045158563528386213 3361638570967230661572415)
    ·
      refine ⟨5042457856450845992358623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3361638570967230661572415 5042457856450845992358623)
      ·
        refine ⟨7563686784676268988537935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042457856450845992358623 7563686784676268988537935)
        ·
          refine ⟨11345530177014403482806903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563686784676268988537935 11345530177014403482806903)
          ·
            refine ⟨17018295265521605224210355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345530177014403482806903 17018295265521605224210355)
            ·
              refine ⟨25527442898282407836315533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17018295265521605224210355 25527442898282407836315533)
              ·
                refine ⟨9572791086855902938618325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25527442898282407836315533 9572791086855902938618325)
                ·
                  refine ⟨224362291098185225123867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9572791086855902938618325 224362291098185225123867)
                  ·
                    rfl

theorem cell21_983124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_983124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983124 prefixEnd_983124 := by exact prefixLift 983124
  have htrace : WordTrace (prefixWord ++ tailWord_983124) baseStart_983124 baseEnd_983124 := by
    simpa [prefixWord, tailWord_983124, baseEnd_983124] using wordTrace_append hprefix tailTrace_983124
  have hstable : (prefixWord ++ tailWord_983124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983124).length < 2 ^ (prefixWord ++ tailWord_983124).sum := by decide
  have hdescent : baseEnd_983124 < baseStart_983124 := by decide
  rcases family_descends (prefixWord ++ tailWord_983124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983259 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 9]
def baseStart_983259 : Nat := 118140960795 + 983259 * 2 ^ 59
def prefixEnd_983259 : Nat := 4983230072969 + 3 ^ 40 * 983259 * 2
def baseEnd_983259 : Nat := 224393099937454990373591

theorem tailTrace_983259 : CollatzResearch.WordTrace tailWord_983259 prefixEnd_983259 224393099937454990373591 := by
  unfold tailWord_983259
  simp only [CollatzResearch.WordTrace]
  refine ⟨35862401944828045112936831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23908267963218696741957887 35862401944828045112936831)
  ·
    refine ⟨53793602917242067669405247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35862401944828045112936831 53793602917242067669405247)
    ·
      refine ⟨80690404375863101504107871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53793602917242067669405247 80690404375863101504107871)
      ·
        refine ⟨121035606563794652256161807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80690404375863101504107871 121035606563794652256161807)
        ·
          refine ⟨181553409845691978384242711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121035606563794652256161807 181553409845691978384242711)
          ·
            refine ⟨272330114768537967576364067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181553409845691978384242711 272330114768537967576364067)
            ·
              refine ⟨408495172152806951364546101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272330114768537967576364067 408495172152806951364546101)
              ·
                refine ⟨38296422389325651690426197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 408495172152806951364546101 38296422389325651690426197)
                ·
                  refine ⟨224393099937454990373591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38296422389325651690426197 224393099937454990373591)
                  ·
                    rfl

theorem cell21_983259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_983259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983259 prefixEnd_983259 := by exact prefixLift 983259
  have htrace : WordTrace (prefixWord ++ tailWord_983259) baseStart_983259 baseEnd_983259 := by
    simpa [prefixWord, tailWord_983259, baseEnd_983259] using wordTrace_append hprefix tailTrace_983259
  have hstable : (prefixWord ++ tailWord_983259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983259).length < 2 ^ (prefixWord ++ tailWord_983259).sum := by decide
  have hdescent : baseEnd_983259 < baseStart_983259 := by decide
  rcases family_descends (prefixWord ++ tailWord_983259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983327 : List Nat := [1, 1, 2, 4, 3, 3, 2, 2, 3]
def baseStart_983327 : Nat := 118140960795 + 983327 * 2 ^ 59
def prefixEnd_983327 : Nat := 4983230072969 + 3 ^ 40 * 983327 * 2
def baseEnd_983327 : Nat := 224408618463901983240119

theorem tailTrace_983327 : CollatzResearch.WordTrace tailWord_983327 prefixEnd_983327 224408618463901983240119 := by
  unfold tailWord_983327
  simp only [CollatzResearch.WordTrace]
  refine ⟨35864882108581692726412235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23909921405721128484274823 35864882108581692726412235)
  ·
    refine ⟨53797323162872539089618353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35864882108581692726412235 53797323162872539089618353)
    ·
      refine ⟨40347992372154404317213765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53797323162872539089618353 40347992372154404317213765)
      ·
        refine ⟨7565248569778950809477581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40347992372154404317213765 7565248569778950809477581)
        ·
          refine ⟨2836968213667106553554093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7565248569778950809477581 2836968213667106553554093)
          ·
            refine ⟨1063863080125164957582785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2836968213667106553554093 1063863080125164957582785)
            ·
              refine ⟨797897310093873718187089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063863080125164957582785 797897310093873718187089)
              ·
                refine ⟨598422982570405288640317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797897310093873718187089 598422982570405288640317)
                ·
                  refine ⟨224408618463901983240119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598422982570405288640317 224408618463901983240119)
                  ·
                    rfl

theorem cell21_983327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 3].length) (baseStart_983327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983327 prefixEnd_983327 := by exact prefixLift 983327
  have htrace : WordTrace (prefixWord ++ tailWord_983327) baseStart_983327 baseEnd_983327 := by
    simpa [prefixWord, tailWord_983327, baseEnd_983327] using wordTrace_append hprefix tailTrace_983327
  have hstable : (prefixWord ++ tailWord_983327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983327).length < 2 ^ (prefixWord ++ tailWord_983327).sum := by decide
  have hdescent : baseEnd_983327 < baseStart_983327 := by decide
  rcases family_descends (prefixWord ++ tailWord_983327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983459 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 4]
def baseStart_983459 : Nat := 118140960795 + 983459 * 2 ^ 59
def prefixEnd_983459 : Nat := 4983230072969 + 3 ^ 40 * 983459 * 2
def baseEnd_983459 : Nat := 224438742662299087039849

theorem tailTrace_983459 : CollatzResearch.WordTrace tailWord_983459 prefixEnd_983459 224438742662299087039849 := by
  unfold tailWord_983459
  simp only [CollatzResearch.WordTrace]
  refine ⟨35869696544103479270217431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23913131029402319513478287 35869696544103479270217431)
  ·
    refine ⟨53804544816155218905326147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35869696544103479270217431 53804544816155218905326147)
    ·
      refine ⟨80706817224232828357989221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53804544816155218905326147 80706817224232828357989221)
      ·
        refine ⟨15132528229543655317122979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80706817224232828357989221 15132528229543655317122979)
        ·
          refine ⟨22698792344315482975684469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15132528229543655317122979 22698792344315482975684469)
          ·
            refine ⟨2128011782279576528970419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22698792344315482975684469 2128011782279576528970419)
            ·
              refine ⟨3192017673419364793455629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128011782279576528970419 3192017673419364793455629)
              ·
                refine ⟨1197006627532261797545861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3192017673419364793455629 1197006627532261797545861)
                ·
                  refine ⟨224438742662299087039849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197006627532261797545861 224438742662299087039849)
                  ·
                    rfl

theorem cell21_983459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_983459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983459 prefixEnd_983459 := by exact prefixLift 983459
  have htrace : WordTrace (prefixWord ++ tailWord_983459) baseStart_983459 baseEnd_983459 := by
    simpa [prefixWord, tailWord_983459, baseEnd_983459] using wordTrace_append hprefix tailTrace_983459
  have hstable : (prefixWord ++ tailWord_983459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983459).length < 2 ^ (prefixWord ++ tailWord_983459).sum := by decide
  have hdescent : baseEnd_983459 < baseStart_983459 := by decide
  rcases family_descends (prefixWord ++ tailWord_983459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983473 : List Nat := [1, 2, 2, 4, 1, 2, 2, 7]
def baseStart_983473 : Nat := 118140960795 + 983473 * 2 ^ 59
def prefixEnd_983473 : Nat := 4983230072969 + 3 ^ 40 * 983473 * 2
def baseEnd_983473 : Nat := 74813979217679391268829

theorem tailTrace_983473 : CollatzResearch.WordTrace tailWord_983473 prefixEnd_983473 74813979217679391268829 := by
  unfold tailWord_983473
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870207166052759661227073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23913471444035173107484715 35870207166052759661227073)
  ·
    refine ⟨26902655374539569745920305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35870207166052759661227073 26902655374539569745920305)
    ·
      refine ⟨20176991530904677309440229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26902655374539569745920305 20176991530904677309440229)
      ·
        refine ⟨3783185912044626995520043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20176991530904677309440229 3783185912044626995520043)
        ·
          refine ⟨5674778868066940493280065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783185912044626995520043 5674778868066940493280065)
          ·
            refine ⟨4256084151050205369960049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5674778868066940493280065 4256084151050205369960049)
            ·
              refine ⟨3192063113287654027470037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4256084151050205369960049 3192063113287654027470037)
              ·
                refine ⟨74813979217679391268829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3192063113287654027470037 74813979217679391268829)
                ·
                  rfl

theorem cell21_983473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 7].length) (baseStart_983473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983473 prefixEnd_983473 := by exact prefixLift 983473
  have htrace : WordTrace (prefixWord ++ tailWord_983473) baseStart_983473 baseEnd_983473 := by
    simpa [prefixWord, tailWord_983473, baseEnd_983473] using wordTrace_append hprefix tailTrace_983473
  have hstable : (prefixWord ++ tailWord_983473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983473).length < 2 ^ (prefixWord ++ tailWord_983473).sum := by decide
  have hdescent : baseEnd_983473 < baseStart_983473 := by decide
  rcases family_descends (prefixWord ++ tailWord_983473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983580 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_983580 : Nat := 118140960795 + 983580 * 2 ^ 59
def prefixEnd_983580 : Nat := 4983230072969 + 3 ^ 40 * 983580 * 2
def baseEnd_983580 : Nat := 224466356510829765522935

theorem tailTrace_983580 : CollatzResearch.WordTrace tailWord_983580 prefixEnd_983580 224466356510829765522935 := by
  unfold tailWord_983580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937054888332558467686097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23916073184443411290248129 17937054888332558467686097)
  ·
    refine ⟨13452791166249418850764573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17937054888332558467686097 13452791166249418850764573)
    ·
      refine ⟨5044796687343532069036715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13452791166249418850764573 5044796687343532069036715)
      ·
        refine ⟨7567195031015298103555073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5044796687343532069036715 7567195031015298103555073)
        ·
          refine ⟨5675396273261473577666305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7567195031015298103555073 5675396273261473577666305)
          ·
            refine ⟨4256547204946105183249729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5675396273261473577666305 4256547204946105183249729)
            ·
              refine ⟨3192410403709578887437297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4256547204946105183249729 3192410403709578887437297)
              ·
                refine ⟨2394307802782184165577973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192410403709578887437297 2394307802782184165577973)
                ·
                  refine ⟨224466356510829765522935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2394307802782184165577973 224466356510829765522935)
                  ·
                    rfl

theorem cell21_983580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_983580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983580 prefixEnd_983580 := by exact prefixLift 983580
  have htrace : WordTrace (prefixWord ++ tailWord_983580) baseStart_983580 baseEnd_983580 := by
    simpa [prefixWord, tailWord_983580, baseEnd_983580] using wordTrace_append hprefix tailTrace_983580
  have hstable : (prefixWord ++ tailWord_983580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983580).length < 2 ^ (prefixWord ++ tailWord_983580).sum := by decide
  have hdescent : baseEnd_983580 < baseStart_983580 := by decide
  rcases family_descends (prefixWord ++ tailWord_983580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983620 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 4]
def baseStart_983620 : Nat := 118140960795 + 983620 * 2 ^ 59
def prefixEnd_983620 : Nat := 4983230072969 + 3 ^ 40 * 983620 * 2
def baseEnd_983620 : Nat := 224475485055798584856187

theorem tailTrace_983620 : CollatzResearch.WordTrace tailWord_983620 prefixEnd_983620 224475485055798584856187 := by
  unfold tailWord_983620
  simp only [CollatzResearch.WordTrace]
  refine ⟨17937784348260101883414157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23917045797680135844552209 17937784348260101883414157)
  ·
    refine ⟨6726669130597538206280309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17937784348260101883414157 6726669130597538206280309)
    ·
      refine ⟨630625230993519206838779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6726669130597538206280309 630625230993519206838779)
      ·
        refine ⟨945937846490278810258169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630625230993519206838779 945937846490278810258169)
        ·
          refine ⟨709453384867709107693627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945937846490278810258169 709453384867709107693627)
          ·
            refine ⟨1064180077301563661540441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709453384867709107693627 1064180077301563661540441)
            ·
              refine ⟨798135057976172746155331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064180077301563661540441 798135057976172746155331)
              ·
                refine ⟨1197202586964259119232997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798135057976172746155331 1197202586964259119232997)
                ·
                  refine ⟨224475485055798584856187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197202586964259119232997 224475485055798584856187)
                  ·
                    rfl

theorem cell21_983620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_983620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983620 prefixEnd_983620 := by exact prefixLift 983620
  have htrace : WordTrace (prefixWord ++ tailWord_983620) baseStart_983620 baseEnd_983620 := by
    simpa [prefixWord, tailWord_983620, baseEnd_983620] using wordTrace_append hprefix tailTrace_983620
  have hstable : (prefixWord ++ tailWord_983620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983620).length < 2 ^ (prefixWord ++ tailWord_983620).sum := by decide
  have hdescent : baseEnd_983620 < baseStart_983620 := by decide
  rcases family_descends (prefixWord ++ tailWord_983620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983639 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 7]
def baseStart_983639 : Nat := 118140960795 + 983639 * 2 ^ 59
def prefixEnd_983639 : Nat := 4983230072969 + 3 ^ 40 * 983639 * 2
def baseEnd_983639 : Nat := 224479821114658774039481

theorem tailTrace_983639 : CollatzResearch.WordTrace tailWord_983639 prefixEnd_983639 224479821114658774039481 := by
  unfold tailWord_983639
  simp only [CollatzResearch.WordTrace]
  refine ⟨35876261683451370011769971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23917507788967580007846647 35876261683451370011769971)
  ·
    refine ⟨53814392525177055017654957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35876261683451370011769971 53814392525177055017654957)
    ·
      refine ⟨20180397196941395631620609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53814392525177055017654957 20180397196941395631620609)
      ·
        refine ⟨15135297897706046723715457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20180397196941395631620609 15135297897706046723715457)
        ·
          refine ⟨11351473423279535042786593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15135297897706046723715457 11351473423279535042786593)
          ·
            refine ⟨8513605067459651282089945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11351473423279535042786593 8513605067459651282089945)
            ·
              refine ⟨6385203800594738461567459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8513605067459651282089945 6385203800594738461567459)
              ·
                refine ⟨9577805700892107692351189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6385203800594738461567459 9577805700892107692351189)
                ·
                  refine ⟨224479821114658774039481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9577805700892107692351189 224479821114658774039481)
                  ·
                    rfl

theorem cell21_983639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_983639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983639 prefixEnd_983639 := by exact prefixLift 983639
  have htrace : WordTrace (prefixWord ++ tailWord_983639) baseStart_983639 baseEnd_983639 := by
    simpa [prefixWord, tailWord_983639, baseEnd_983639] using wordTrace_append hprefix tailTrace_983639
  have hstable : (prefixWord ++ tailWord_983639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983639).length < 2 ^ (prefixWord ++ tailWord_983639).sum := by decide
  have hdescent : baseEnd_983639 < baseStart_983639 := by decide
  rcases family_descends (prefixWord ++ tailWord_983639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983673 : List Nat := [1, 2, 1, 3, 3, 3, 1, 4, 3]
def baseStart_983673 : Nat := 118140960795 + 983673 * 2 ^ 59
def prefixEnd_983673 : Nat := 4983230072969 + 3 ^ 40 * 983673 * 2
def baseEnd_983673 : Nat := 224487580377882270472745

theorem tailTrace_983673 : CollatzResearch.WordTrace tailWord_983673 prefixEnd_983673 224487580377882270472745 := by
  unfold tailWord_983673
  simp only [CollatzResearch.WordTrace]
  refine ⟨35877501765328193818507673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23918334510218795879005115 35877501765328193818507673)
  ·
    refine ⟨26908126323996145363880755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35877501765328193818507673 26908126323996145363880755)
    ·
      refine ⟨40362189485994218045821133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26908126323996145363880755 40362189485994218045821133)
      ·
        refine ⟨15135821057247831767182925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40362189485994218045821133 15135821057247831767182925)
        ·
          refine ⟨5675932896467936912693597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15135821057247831767182925 5675932896467936912693597)
          ·
            refine ⟨2128474836175476342260099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5675932896467936912693597 2128474836175476342260099)
            ·
              refine ⟨3192712254263214513390149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128474836175476342260099 3192712254263214513390149)
              ·
                refine ⟨598633547674352721260653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3192712254263214513390149 598633547674352721260653)
                ·
                  refine ⟨224487580377882270472745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598633547674352721260653 224487580377882270472745)
                  ·
                    rfl

theorem cell21_983673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_983673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983673 prefixEnd_983673 := by exact prefixLift 983673
  have htrace : WordTrace (prefixWord ++ tailWord_983673) baseStart_983673 baseEnd_983673 := by
    simpa [prefixWord, tailWord_983673, baseEnd_983673] using wordTrace_append hprefix tailTrace_983673
  have hstable : (prefixWord ++ tailWord_983673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983673).length < 2 ^ (prefixWord ++ tailWord_983673).sum := by decide
  have hdescent : baseEnd_983673 < baseStart_983673 := by decide
  rcases family_descends (prefixWord ++ tailWord_983673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983777 : List Nat := [1, 2, 3, 1, 4, 3, 7]
def baseStart_983777 : Nat := 118140960795 + 983777 * 2 ^ 59
def prefixEnd_983777 : Nat := 4983230072969 + 3 ^ 40 * 983777 * 2
def baseEnd_983777 : Nat := 24945701621644577859911

theorem tailTrace_983777 : CollatzResearch.WordTrace tailWord_983777 prefixEnd_983777 24945701621644577859911 := by
  unfold tailWord_983777
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881294956951419580293585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23920863304634279720195723 35881294956951419580293585)
  ·
    refine ⟨26910971217713564685220189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35881294956951419580293585 26910971217713564685220189)
    ·
      refine ⟨10091614206642586756957571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26910971217713564685220189 10091614206642586756957571)
      ·
        refine ⟨15137421309963880135436357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10091614206642586756957571 15137421309963880135436357)
        ·
          refine ⟨2838266495618227525394317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15137421309963880135436357 2838266495618227525394317)
          ·
            refine ⟨1064349935856835322022869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2838266495618227525394317 1064349935856835322022869)
            ·
              refine ⟨24945701621644577859911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1064349935856835322022869 24945701621644577859911)
              ·
                rfl

theorem cell21_983777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 7].length) (baseStart_983777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983777 prefixEnd_983777 := by exact prefixLift 983777
  have htrace : WordTrace (prefixWord ++ tailWord_983777) baseStart_983777 baseEnd_983777 := by
    simpa [prefixWord, tailWord_983777, baseEnd_983777] using wordTrace_append hprefix tailTrace_983777
  have hstable : (prefixWord ++ tailWord_983777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983777).length < 2 ^ (prefixWord ++ tailWord_983777).sum := by decide
  have hdescent : baseEnd_983777 < baseStart_983777 := by decide
  rcases family_descends (prefixWord ++ tailWord_983777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983836 : List Nat := [2, 2, 3, 1, 1, 12]
def baseStart_983836 : Nat := 118140960795 + 983836 * 2 ^ 59
def prefixEnd_983836 : Nat := 4983230072969 + 3 ^ 40 * 983836 * 2
def baseEnd_983836 : Nat := 8315732562912229972435

theorem tailTrace_983836 : CollatzResearch.WordTrace tailWord_983836 prefixEnd_983836 8315732562912229972435 := by
  unfold tailWord_983836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17941723431868836328345681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23922297909158448437794241 17941723431868836328345681)
  ·
    refine ⟨13456292573901627246259261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17941723431868836328345681 13456292573901627246259261)
    ·
      refine ⟨5046109715213110217347223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13456292573901627246259261 5046109715213110217347223)
      ·
        refine ⟨7569164572819665326020835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5046109715213110217347223 7569164572819665326020835)
        ·
          refine ⟨11353746859229497989031253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7569164572819665326020835 11353746859229497989031253)
          ·
            refine ⟨8315732562912229972435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11353746859229497989031253 8315732562912229972435)
            ·
              rfl

theorem cell21_983836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 12].length) (baseStart_983836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983836 prefixEnd_983836 := by exact prefixLift 983836
  have htrace : WordTrace (prefixWord ++ tailWord_983836) baseStart_983836 baseEnd_983836 := by
    simpa [prefixWord, tailWord_983836, baseEnd_983836] using wordTrace_append hprefix tailTrace_983836
  have hstable : (prefixWord ++ tailWord_983836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983836).length < 2 ^ (prefixWord ++ tailWord_983836).sum := by decide
  have hdescent : baseEnd_983836 < baseStart_983836 := by decide
  rcases family_descends (prefixWord ++ tailWord_983836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983839 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 4]
def baseStart_983839 : Nat := 118140960795 + 983839 * 2 ^ 59
def prefixEnd_983839 : Nat := 4983230072969 + 3 ^ 40 * 983839 * 2
def baseEnd_983839 : Nat := 224525463839502870705739

theorem tailTrace_983839 : CollatzResearch.WordTrace tailWord_983839 prefixEnd_983839 224525463839502870705739 := by
  unfold tailWord_983839
  simp only [CollatzResearch.WordTrace]
  refine ⟨35883556282726804169050571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23922370855151202779367047 35883556282726804169050571)
  ·
    refine ⟨53825334424090206253575857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35883556282726804169050571 53825334424090206253575857)
    ·
      refine ⟨40369000818067654690181893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53825334424090206253575857 40369000818067654690181893)
      ·
        refine ⟨7569187653387685254409105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40369000818067654690181893 7569187653387685254409105)
        ·
          refine ⟨5676890740040763940806829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7569187653387685254409105 5676890740040763940806829)
          ·
            refine ⟨2128834027515286477802561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5676890740040763940806829 2128834027515286477802561)
            ·
              refine ⟨1596625520636464858351921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128834027515286477802561 1596625520636464858351921)
              ·
                refine ⟨1197469140477348643763941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596625520636464858351921 1197469140477348643763941)
                ·
                  refine ⟨224525463839502870705739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197469140477348643763941 224525463839502870705739)
                  ·
                    rfl

theorem cell21_983839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_983839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983839 prefixEnd_983839 := by exact prefixLift 983839
  have htrace : WordTrace (prefixWord ++ tailWord_983839) baseStart_983839 baseEnd_983839 := by
    simpa [prefixWord, tailWord_983839, baseEnd_983839] using wordTrace_append hprefix tailTrace_983839
  have hstable : (prefixWord ++ tailWord_983839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983839).length < 2 ^ (prefixWord ++ tailWord_983839).sum := by decide
  have hdescent : baseEnd_983839 < baseStart_983839 := by decide
  rcases family_descends (prefixWord ++ tailWord_983839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983842 : List Nat := [3, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_983842 : Nat := 118140960795 + 983842 * 2 ^ 59
def prefixEnd_983842 : Nat := 4983230072969 + 3 ^ 40 * 983842 * 2
def baseEnd_983842 : Nat := 224526148480375532155733

theorem tailTrace_983842 : CollatzResearch.WordTrace tailWord_983842 prefixEnd_983842 224526148480375532155733 := by
  unfold tailWord_983842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8970916425428983920352445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23922443801143957120939853 8970916425428983920352445)
  ·
    refine ⟨3364093659535868970132167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8970916425428983920352445 3364093659535868970132167)
    ·
      refine ⟨5046140489303803455198251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3364093659535868970132167 5046140489303803455198251)
      ·
        refine ⟨7569210733955705182797377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5046140489303803455198251 7569210733955705182797377)
        ·
          refine ⟨5676908050466778887098033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7569210733955705182797377 5676908050466778887098033)
          ·
            refine ⟨4257681037850084165323525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5676908050466778887098033 4257681037850084165323525)
            ·
              refine ⟨798315194596890780998161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4257681037850084165323525 798315194596890780998161)
              ·
                refine ⟨598736395947668085748621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798315194596890780998161 598736395947668085748621)
                ·
                  refine ⟨224526148480375532155733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598736395947668085748621 224526148480375532155733)
                  ·
                    rfl

theorem cell21_983842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_983842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983842 prefixEnd_983842 := by exact prefixLift 983842
  have htrace : WordTrace (prefixWord ++ tailWord_983842) baseStart_983842 baseEnd_983842 := by
    simpa [prefixWord, tailWord_983842, baseEnd_983842] using wordTrace_append hprefix tailTrace_983842
  have hstable : (prefixWord ++ tailWord_983842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983842).length < 2 ^ (prefixWord ++ tailWord_983842).sum := by decide
  have hdescent : baseEnd_983842 < baseStart_983842 := by decide
  rcases family_descends (prefixWord ++ tailWord_983842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983898 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_983898 : Nat := 118140960795 + 983898 * 2 ^ 59
def prefixEnd_983898 : Nat := 4983230072969 + 3 ^ 40 * 983898 * 2
def baseEnd_983898 : Nat := 224538928443331879222285

theorem tailTrace_983898 : CollatzResearch.WordTrace tailWord_983898 prefixEnd_983898 224538928443331879222285 := by
  unfold tailWord_983898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971427047378264311362087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23923805459675371496965565 8971427047378264311362087)
  ·
    refine ⟨13457140571067396467043131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8971427047378264311362087 13457140571067396467043131)
    ·
      refine ⟨20185710856601094700564697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13457140571067396467043131 20185710856601094700564697)
      ·
        refine ⟨15139283142450821025423523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20185710856601094700564697 15139283142450821025423523)
        ·
          refine ⟨22708924713676231538135285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15139283142450821025423523 22708924713676231538135285)
          ·
            refine ⟨2128961691907146706700183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22708924713676231538135285 2128961691907146706700183)
            ·
              refine ⟨3193442537860720060050275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128961691907146706700183 3193442537860720060050275)
              ·
                refine ⟨4790163806791080090075413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193442537860720060050275 4790163806791080090075413)
                ·
                  refine ⟨224538928443331879222285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4790163806791080090075413 224538928443331879222285)
                  ·
                    rfl

theorem cell21_983898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_983898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983898 prefixEnd_983898 := by exact prefixLift 983898
  have htrace : WordTrace (prefixWord ++ tailWord_983898) baseStart_983898 baseEnd_983898 := by
    simpa [prefixWord, tailWord_983898, baseEnd_983898] using wordTrace_append hprefix tailTrace_983898
  have hstable : (prefixWord ++ tailWord_983898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983898).length < 2 ^ (prefixWord ++ tailWord_983898).sum := by decide
  have hdescent : baseEnd_983898 < baseStart_983898 := by decide
  rcases family_descends (prefixWord ++ tailWord_983898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983929 : List Nat := [1, 2, 1, 3, 2, 3, 4, 5]
def baseStart_983929 : Nat := 118140960795 + 983929 * 2 ^ 59
def prefixEnd_983929 : Nat := 4983230072969 + 3 ^ 40 * 983929 * 2
def baseEnd_983929 : Nat := 74848667688560904735185

theorem tailTrace_983929 : CollatzResearch.WordTrace tailWord_983929 prefixEnd_983929 74848667688560904735185 := by
  unfold tailWord_983929
  simp only [CollatzResearch.WordTrace]
  refine ⟨35886838852400749539826841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23924559234933833026551227 35886838852400749539826841)
  ·
    refine ⟨26915129139300562154870131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35886838852400749539826841 26915129139300562154870131)
    ·
      refine ⟨40372693708950843232305197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26915129139300562154870131 40372693708950843232305197)
      ·
        refine ⟨15139760140856566212114449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40372693708950843232305197 15139760140856566212114449)
        ·
          refine ⟨11354820105642424659085837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15139760140856566212114449 11354820105642424659085837)
          ·
            refine ⟨4258057539615909247157189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11354820105642424659085837 4258057539615909247157189)
            ·
              refine ⟨798385788677982983841973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4258057539615909247157189 798385788677982983841973)
              ·
                refine ⟨74848667688560904735185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 798385788677982983841973 74848667688560904735185)
                ·
                  rfl

theorem cell21_983929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 5].length) (baseStart_983929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_983929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_983929 prefixEnd_983929 := by exact prefixLift 983929
  have htrace : WordTrace (prefixWord ++ tailWord_983929) baseStart_983929 baseEnd_983929 := by
    simpa [prefixWord, tailWord_983929, baseEnd_983929] using wordTrace_append hprefix tailTrace_983929
  have hstable : (prefixWord ++ tailWord_983929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983929).length < 2 ^ (prefixWord ++ tailWord_983929).sum := by decide
  have hdescent : baseEnd_983929 < baseStart_983929 := by decide
  rcases family_descends (prefixWord ++ tailWord_983929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984022 : List Nat := [5, 2, 1, 1, 2, 1, 3, 6]
def baseStart_984022 : Nat := 118140960795 + 984022 * 2 ^ 59
def prefixEnd_984022 : Nat := 4983230072969 + 3 ^ 40 * 984022 * 2
def baseEnd_984022 : Nat := 74855742310911739718455

theorem tailTrace_984022 : CollatzResearch.WordTrace tailWord_984022 prefixEnd_984022 74855742310911739718455 := by
  unfold tailWord_984022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2243139427566489151435145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23926820560709217615308213 2243139427566489151435145)
  ·
    refine ⟨1682354570674866863576359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2243139427566489151435145 1682354570674866863576359)
    ·
      refine ⟨2523531856012300295364539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682354570674866863576359 2523531856012300295364539)
      ·
        refine ⟨3785297784018450443046809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523531856012300295364539 3785297784018450443046809)
        ·
          refine ⟨2838973338013837832285107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3785297784018450443046809 2838973338013837832285107)
          ·
            refine ⟨4258460007020756748427661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838973338013837832285107 4258460007020756748427661)
            ·
              refine ⟨1596922502632783780660373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4258460007020756748427661 1596922502632783780660373)
              ·
                refine ⟨74855742310911739718455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1596922502632783780660373 74855742310911739718455)
                ·
                  rfl

theorem cell21_984022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_984022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984022 prefixEnd_984022 := by exact prefixLift 984022
  have htrace : WordTrace (prefixWord ++ tailWord_984022) baseStart_984022 baseEnd_984022 := by
    simpa [prefixWord, tailWord_984022, baseEnd_984022] using wordTrace_append hprefix tailTrace_984022
  have hstable : (prefixWord ++ tailWord_984022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984022).length < 2 ^ (prefixWord ++ tailWord_984022).sum := by decide
  have hdescent : baseEnd_984022 < baseStart_984022 := by decide
  rcases family_descends (prefixWord ++ tailWord_984022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984033 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 8]
def baseStart_984033 : Nat := 118140960795 + 984033 * 2 ^ 59
def prefixEnd_984033 : Nat := 4983230072969 + 3 ^ 40 * 984033 * 2
def baseEnd_984033 : Nat := 224569737282601644472009

theorem tailTrace_984033 : CollatzResearch.WordTrace tailWord_984033 prefixEnd_984033 224569737282601644472009 := by
  unfold tailWord_984033
  simp only [CollatzResearch.WordTrace]
  refine ⟨35890632044023975301612753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23927088029349316867741835 35890632044023975301612753)
  ·
    refine ⟨26917974033017981476209565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35890632044023975301612753 26917974033017981476209565)
    ·
      refine ⟨10094240262381743053578587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26917974033017981476209565 10094240262381743053578587)
      ·
        refine ⟨15141360393572614580367881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094240262381743053578587 15141360393572614580367881)
        ·
          refine ⟨11356020295179460935275911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15141360393572614580367881 11356020295179460935275911)
          ·
            refine ⟨17034030442769191402913867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11356020295179460935275911 17034030442769191402913867)
            ·
              refine ⟨25551045664153787104370801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17034030442769191402913867 25551045664153787104370801)
              ·
                refine ⟨19163284248115340328278101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25551045664153787104370801 19163284248115340328278101)
                ·
                  refine ⟨224569737282601644472009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19163284248115340328278101 224569737282601644472009)
                  ·
                    rfl

theorem cell21_984033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_984033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984033 prefixEnd_984033 := by exact prefixLift 984033
  have htrace : WordTrace (prefixWord ++ tailWord_984033) baseStart_984033 baseEnd_984033 := by
    simpa [prefixWord, tailWord_984033, baseEnd_984033] using wordTrace_append hprefix tailTrace_984033
  have hstable : (prefixWord ++ tailWord_984033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984033).length < 2 ^ (prefixWord ++ tailWord_984033).sum := by decide
  have hdescent : baseEnd_984033 < baseStart_984033 := by decide
  rcases family_descends (prefixWord ++ tailWord_984033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984095 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 5]
def baseStart_984095 : Nat := 118140960795 + 984095 * 2 ^ 59
def prefixEnd_984095 : Nat := 4983230072969 + 3 ^ 40 * 984095 * 2
def baseEnd_984095 : Nat := 224583886527303314438549

theorem tailTrace_984095 : CollatzResearch.WordTrace tailWord_984095 prefixEnd_984095 224583886527303314438549 := by
  unfold tailWord_984095
  simp only [CollatzResearch.WordTrace]
  refine ⟨35892893369799359890369739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23928595579866239926913159 35892893369799359890369739)
  ·
    refine ⟨53839340054699039835554609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35892893369799359890369739 53839340054699039835554609)
    ·
      refine ⟨40379505041024279876665957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53839340054699039835554609 40379505041024279876665957)
      ·
        refine ⟨7571157195192052476874867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40379505041024279876665957 7571157195192052476874867)
        ·
          refine ⟨11356735792788078715312301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7571157195192052476874867 11356735792788078715312301)
          ·
            refine ⟨4258775922295529518242113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11356735792788078715312301 4258775922295529518242113)
            ·
              refine ⟨3194081941721647138681585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4258775922295529518242113 3194081941721647138681585)
              ·
                refine ⟨2395561456291235354011189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194081941721647138681585 2395561456291235354011189)
                ·
                  refine ⟨224583886527303314438549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2395561456291235354011189 224583886527303314438549)
                  ·
                    rfl

theorem cell21_984095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_984095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984095 prefixEnd_984095 := by exact prefixLift 984095
  have htrace : WordTrace (prefixWord ++ tailWord_984095) baseStart_984095 baseEnd_984095 := by
    simpa [prefixWord, tailWord_984095, baseEnd_984095] using wordTrace_append hprefix tailTrace_984095
  have hstable : (prefixWord ++ tailWord_984095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984095).length < 2 ^ (prefixWord ++ tailWord_984095).sum := by decide
  have hdescent : baseEnd_984095 < baseStart_984095 := by decide
  rcases family_descends (prefixWord ++ tailWord_984095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984098 : List Nat := [3, 3, 1, 1, 1, 5, 2, 5]
def baseStart_984098 : Nat := 118140960795 + 984098 * 2 ^ 59
def prefixEnd_984098 : Nat := 4983230072969 + 3 ^ 40 * 984098 * 2
def baseEnd_984098 : Nat := 74861523722725325296181

theorem tailTrace_984098 : CollatzResearch.WordTrace tailWord_984098 prefixEnd_984098 74861523722725325296181 := by
  unfold tailWord_984098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973250697197122850682237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23928668525858994268485965 8973250697197122850682237)
  ·
    refine ⟨3364969011448921069005839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8973250697197122850682237 3364969011448921069005839)
    ·
      refine ⟨5047453517173381603508759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3364969011448921069005839 5047453517173381603508759)
      ·
        refine ⟨7571180275760072405263139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5047453517173381603508759 7571180275760072405263139)
        ·
          refine ⟨11356770413640108607894709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7571180275760072405263139 11356770413640108607894709)
          ·
            refine ⟨1064697226278760181990129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11356770413640108607894709 1064697226278760181990129)
            ·
              refine ⟨798522919709070136492597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064697226278760181990129 798522919709070136492597)
              ·
                refine ⟨74861523722725325296181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 798522919709070136492597 74861523722725325296181)
                ·
                  rfl

theorem cell21_984098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_984098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984098 prefixEnd_984098 := by exact prefixLift 984098
  have htrace : WordTrace (prefixWord ++ tailWord_984098) baseStart_984098 baseEnd_984098 := by
    simpa [prefixWord, tailWord_984098, baseEnd_984098] using wordTrace_append hprefix tailTrace_984098
  have hstable : (prefixWord ++ tailWord_984098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984098).length < 2 ^ (prefixWord ++ tailWord_984098).sum := by decide
  have hdescent : baseEnd_984098 < baseStart_984098 := by decide
  rcases family_descends (prefixWord ++ tailWord_984098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984129 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 5]
def baseStart_984129 : Nat := 118140960795 + 984129 * 2 ^ 59
def prefixEnd_984129 : Nat := 4983230072969 + 3 ^ 40 * 984129 * 2
def baseEnd_984129 : Nat := 224591645790526810871813

theorem tailTrace_984129 : CollatzResearch.WordTrace tailWord_984129 prefixEnd_984129 224591645790526810871813 := by
  unfold tailWord_984129
  simp only [CollatzResearch.WordTrace]
  refine ⟨35894133451676183697107441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23929422301117455798071627 35894133451676183697107441)
  ·
    refine ⟨26920600088757137772830581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35894133451676183697107441 26920600088757137772830581)
    ·
      refine ⟨2523806258320981666202867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26920600088757137772830581 2523806258320981666202867)
      ·
        refine ⟨3785709387481472499304301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523806258320981666202867 3785709387481472499304301)
        ·
          refine ⟨1419641020305552187239113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3785709387481472499304301 1419641020305552187239113)
          ·
            refine ⟨1064730765229164140429335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419641020305552187239113 1064730765229164140429335)
            ·
              refine ⟨1597096147843746210644003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064730765229164140429335 1597096147843746210644003)
              ·
                refine ⟨2395644221765619315966005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597096147843746210644003 2395644221765619315966005)
                ·
                  refine ⟨224591645790526810871813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2395644221765619315966005 224591645790526810871813)
                  ·
                    rfl

theorem cell21_984129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_984129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984129 prefixEnd_984129 := by exact prefixLift 984129
  have htrace : WordTrace (prefixWord ++ tailWord_984129) baseStart_984129 baseEnd_984129 := by
    simpa [prefixWord, tailWord_984129, baseEnd_984129] using wordTrace_append hprefix tailTrace_984129
  have hstable : (prefixWord ++ tailWord_984129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984129).length < 2 ^ (prefixWord ++ tailWord_984129).sum := by decide
  have hdescent : baseEnd_984129 < baseStart_984129 := by decide
  rcases family_descends (prefixWord ++ tailWord_984129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984188 : List Nat := [2, 2, 2, 1, 1, 3, 3, 4, 3]
def baseStart_984188 : Nat := 118140960795 + 984188 * 2 ^ 59
def prefixEnd_984188 : Nat := 4983230072969 + 3 ^ 40 * 984188 * 2
def baseEnd_984188 : Nat := 224605110394355819388359

theorem tailTrace_984188 : CollatzResearch.WordTrace tailWord_984188 prefixEnd_984188 224605110394355819388359 := by
  unfold tailWord_984188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948142679231218386752609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23930856905641624515670145 17948142679231218386752609)
  ·
    refine ⟨13461107009423413790064457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17948142679231218386752609 13461107009423413790064457)
    ·
      refine ⟨10095830257067560342548343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13461107009423413790064457 10095830257067560342548343)
      ·
        refine ⟨15143745385601340513822515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10095830257067560342548343 15143745385601340513822515)
        ·
          refine ⟨22715618078402010770733773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15143745385601340513822515 22715618078402010770733773)
          ·
            refine ⟨8518356779400754039025165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22715618078402010770733773 8518356779400754039025165)
            ·
              refine ⟨3194383792275282764634437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8518356779400754039025165 3194383792275282764634437)
              ·
                refine ⟨598946961051615518368957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3194383792275282764634437 598946961051615518368957)
                ·
                  refine ⟨224605110394355819388359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598946961051615518368957 224605110394355819388359)
                  ·
                    rfl

theorem cell21_984188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_984188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984188 prefixEnd_984188 := by exact prefixLift 984188
  have htrace : WordTrace (prefixWord ++ tailWord_984188) baseStart_984188 baseEnd_984188 := by
    simpa [prefixWord, tailWord_984188, baseEnd_984188] using wordTrace_append hprefix tailTrace_984188
  have hstable : (prefixWord ++ tailWord_984188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984188).length < 2 ^ (prefixWord ++ tailWord_984188).sum := by decide
  have hdescent : baseEnd_984188 < baseStart_984188 := by decide
  rcases family_descends (prefixWord ++ tailWord_984188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984202 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_984202 : Nat := 118140960795 + 984202 * 2 ^ 59
def prefixEnd_984202 : Nat := 4983230072969 + 3 ^ 40 * 984202 * 2
def baseEnd_984202 : Nat := 224608305385094906154997

theorem tailTrace_984202 : CollatzResearch.WordTrace tailWord_984202 prefixEnd_984202 224608305385094906154997 := by
  unfold tailWord_984202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8974198995102929291128715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23931197320274478109676573 8974198995102929291128715)
  ·
    refine ⟨13461298492654393936693073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8974198995102929291128715 13461298492654393936693073)
    ·
      refine ⟨10095973869490795452519805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13461298492654393936693073 10095973869490795452519805)
      ·
        refine ⟨3785990201059048294694927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10095973869490795452519805 3785990201059048294694927)
        ·
          refine ⟨5678985301588572442042391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3785990201059048294694927 5678985301588572442042391)
          ·
            refine ⟨8518477952382858663063587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678985301588572442042391 8518477952382858663063587)
            ·
              refine ⟨12777716928574287994595381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8518477952382858663063587 12777716928574287994595381)
              ·
                refine ⟨1197910962053839499493317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12777716928574287994595381 1197910962053839499493317)
                ·
                  refine ⟨224608305385094906154997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197910962053839499493317 224608305385094906154997)
                  ·
                    rfl

theorem cell21_984202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_984202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984202 prefixEnd_984202 := by exact prefixLift 984202
  have htrace : WordTrace (prefixWord ++ tailWord_984202) baseStart_984202 baseEnd_984202 := by
    simpa [prefixWord, tailWord_984202, baseEnd_984202] using wordTrace_append hprefix tailTrace_984202
  have hstable : (prefixWord ++ tailWord_984202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984202).length < 2 ^ (prefixWord ++ tailWord_984202).sum := by decide
  have hdescent : baseEnd_984202 < baseStart_984202 := by decide
  rcases family_descends (prefixWord ++ tailWord_984202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984222 : List Nat := [4, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_984222 : Nat := 118140960795 + 984222 * 2 ^ 59
def prefixEnd_984222 : Nat := 4983230072969 + 3 ^ 40 * 984222 * 2
def baseEnd_984222 : Nat := 224612869657579315821623

theorem tailTrace_984222 : CollatzResearch.WordTrace tailWord_984222 prefixEnd_984222 224612869657579315821623 := by
  unfold tailWord_984222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487190680042407572530365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23931683626892840386828613 4487190680042407572530365)
  ·
    refine ⟨1682696505015902839698887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4487190680042407572530365 1682696505015902839698887)
    ·
      refine ⟨2524044757523854259548331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682696505015902839698887 2524044757523854259548331)
      ·
        refine ⟨3786067136285781389322497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524044757523854259548331 3786067136285781389322497)
        ·
          refine ⟨2839550352214336041991873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3786067136285781389322497 2839550352214336041991873)
          ·
            refine ⟨2129662764160752031493905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2839550352214336041991873 2129662764160752031493905)
            ·
              refine ⟨1597247073120564023620429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2129662764160752031493905 1597247073120564023620429)
              ·
                refine ⟨598967652420211508857661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597247073120564023620429 598967652420211508857661)
                ·
                  refine ⟨224612869657579315821623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598967652420211508857661 224612869657579315821623)
                  ·
                    rfl

theorem cell21_984222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_984222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984222 prefixEnd_984222 := by exact prefixLift 984222
  have htrace : WordTrace (prefixWord ++ tailWord_984222) baseStart_984222 baseEnd_984222 := by
    simpa [prefixWord, tailWord_984222, baseEnd_984222] using wordTrace_append hprefix tailTrace_984222
  have hstable : (prefixWord ++ tailWord_984222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984222).length < 2 ^ (prefixWord ++ tailWord_984222).sum := by decide
  have hdescent : baseEnd_984222 < baseStart_984222 := by decide
  rcases family_descends (prefixWord ++ tailWord_984222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984247 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 5]
def baseStart_984247 : Nat := 118140960795 + 984247 * 2 ^ 59
def prefixEnd_984247 : Nat := 4983230072969 + 3 ^ 40 * 984247 * 2
def baseEnd_984247 : Nat := 224618574998184827904905

theorem tailTrace_984247 : CollatzResearch.WordTrace tailWord_984247 prefixEnd_984247 224618574998184827904905 := by
  unfold tailWord_984247
  simp only [CollatzResearch.WordTrace]
  refine ⟨35898437265248689849902995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23932291510165793233268663 35898437265248689849902995)
  ·
    refine ⟨53847655897873034774854493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35898437265248689849902995 53847655897873034774854493)
    ·
      refine ⟨20192870961702388040570435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53847655897873034774854493 20192870961702388040570435)
      ·
        refine ⟨30289306442553582060855653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20192870961702388040570435 30289306442553582060855653)
        ·
          refine ⟨5679244957978796636410435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30289306442553582060855653 5679244957978796636410435)
          ·
            refine ⟨8518867436968194954615653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679244957978796636410435 8518867436968194954615653)
            ·
              refine ⟨1597287644431536553990435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8518867436968194954615653 1597287644431536553990435)
              ·
                refine ⟨2395931466647304830985653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597287644431536553990435 2395931466647304830985653)
                ·
                  refine ⟨224618574998184827904905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2395931466647304830985653 224618574998184827904905)
                  ·
                    rfl

theorem cell21_984247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_984247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984247 prefixEnd_984247 := by exact prefixLift 984247
  have htrace : WordTrace (prefixWord ++ tailWord_984247) baseStart_984247 baseEnd_984247 := by
    simpa [prefixWord, tailWord_984247, baseEnd_984247] using wordTrace_append hprefix tailTrace_984247
  have hstable : (prefixWord ++ tailWord_984247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984247).length < 2 ^ (prefixWord ++ tailWord_984247).sum := by decide
  have hdescent : baseEnd_984247 < baseStart_984247 := by decide
  rcases family_descends (prefixWord ++ tailWord_984247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984275 : List Nat := [1, 1, 1, 2, 1, 1, 1, 13]
def baseStart_984275 : Nat := 118140960795 + 984275 * 2 ^ 59
def prefixEnd_984275 : Nat := 4983230072969 + 3 ^ 40 * 984275 * 2
def baseEnd_984275 : Nat := 74874988326554333812727

theorem tailTrace_984275 : CollatzResearch.WordTrace tailWord_984275 prefixEnd_984275 74874988326554333812727 := by
  unfold tailWord_984275
  simp only [CollatzResearch.WordTrace]
  refine ⟨35899458509147250631922279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23932972339431500421281519 35899458509147250631922279)
  ·
    refine ⟨53849187763720875947883419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35899458509147250631922279 53849187763720875947883419)
    ·
      refine ⟨80773781645581313921825129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53849187763720875947883419 80773781645581313921825129)
      ·
        refine ⟨60580336234185985441368847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80773781645581313921825129 60580336234185985441368847)
        ·
          refine ⟨90870504351278978162053271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60580336234185985441368847 90870504351278978162053271)
          ·
            refine ⟨136305756526918467243079907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90870504351278978162053271 136305756526918467243079907)
            ·
              refine ⟨204458634790377700864619861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136305756526918467243079907 204458634790377700864619861)
              ·
                refine ⟨74874988326554333812727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 204458634790377700864619861 74874988326554333812727)
                ·
                  rfl

theorem cell21_984275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_984275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984275 prefixEnd_984275 := by exact prefixLift 984275
  have htrace : WordTrace (prefixWord ++ tailWord_984275) baseStart_984275 baseEnd_984275 := by
    simpa [prefixWord, tailWord_984275, baseEnd_984275] using wordTrace_append hprefix tailTrace_984275
  have hstable : (prefixWord ++ tailWord_984275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984275).length < 2 ^ (prefixWord ++ tailWord_984275).sum := by decide
  have hdescent : baseEnd_984275 < baseStart_984275 := by decide
  rcases family_descends (prefixWord ++ tailWord_984275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984351 : List Nat := [1, 1, 2, 4, 13]
def baseStart_984351 : Nat := 118140960795 + 984351 * 2 ^ 59
def prefixEnd_984351 : Nat := 4983230072969 + 3 ^ 40 * 984351 * 2
def baseEnd_984351 : Nat := 2773361842161774792239

theorem tailTrace_984351 : CollatzResearch.WordTrace tailWord_984351 prefixEnd_984351 2773361842161774792239 := by
  unfold tailWord_984351
  simp only [CollatzResearch.WordTrace]
  refine ⟨35902230456871915611688907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23934820304581277074459271 35902230456871915611688907)
  ·
    refine ⟨53853345685307873417533361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35902230456871915611688907 53853345685307873417533361)
    ·
      refine ⟨40390009263980905063150021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53853345685307873417533361 40390009263980905063150021)
      ·
        refine ⟨7573126736996419699340629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40390009263980905063150021 7573126736996419699340629)
        ·
          refine ⟨2773361842161774792239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7573126736996419699340629 2773361842161774792239)
          ·
            rfl

theorem cell21_984351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 13].length) (baseStart_984351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984351 prefixEnd_984351 := by exact prefixLift 984351
  have htrace : WordTrace (prefixWord ++ tailWord_984351) baseStart_984351 baseEnd_984351 := by
    simpa [prefixWord, tailWord_984351, baseEnd_984351] using wordTrace_append hprefix tailTrace_984351
  have hstable : (prefixWord ++ tailWord_984351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984351).length < 2 ^ (prefixWord ++ tailWord_984351).sum := by decide
  have hdescent : baseEnd_984351 < baseStart_984351 := by decide
  rcases family_descends (prefixWord ++ tailWord_984351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984357 : List Nat := [1, 3, 1, 2, 4, 1, 4, 2, 3]
def baseStart_984357 : Nat := 118140960795 + 984357 * 2 ^ 59
def prefixEnd_984357 : Nat := 4983230072969 + 3 ^ 40 * 984357 * 2
def baseEnd_984357 : Nat := 224643678496849081071347

theorem tailTrace_984357 : CollatzResearch.WordTrace tailWord_984357 prefixEnd_984357 224643678496849081071347 := by
  unfold tailWord_984357
  simp only [CollatzResearch.WordTrace]
  refine ⟨35902449294850178636407325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23934966196566785757604883 35902449294850178636407325)
  ·
    refine ⟨13463418485568816988652747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35902449294850178636407325 13463418485568816988652747)
    ·
      refine ⟨20195127728353225482979121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463418485568816988652747 20195127728353225482979121)
      ·
        refine ⟨15146345796264919112234341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20195127728353225482979121 15146345796264919112234341)
        ·
          refine ⟨2839939836799672333543939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15146345796264919112234341 2839939836799672333543939)
          ·
            refine ⟨4259909755199508500315909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839939836799672333543939 4259909755199508500315909)
            ·
              refine ⟨798733079099907843809233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4259909755199508500315909 798733079099907843809233)
              ·
                refine ⟨599049809324930882856925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798733079099907843809233 599049809324930882856925)
                ·
                  refine ⟨224643678496849081071347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599049809324930882856925 224643678496849081071347)
                  ·
                    rfl

theorem cell21_984357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_984357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984357 prefixEnd_984357 := by exact prefixLift 984357
  have htrace : WordTrace (prefixWord ++ tailWord_984357) baseStart_984357 baseEnd_984357 := by
    simpa [prefixWord, tailWord_984357, baseEnd_984357] using wordTrace_append hprefix tailTrace_984357
  have hstable : (prefixWord ++ tailWord_984357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984357).length < 2 ^ (prefixWord ++ tailWord_984357).sum := by decide
  have hdescent : baseEnd_984357 < baseStart_984357 := by decide
  rcases family_descends (prefixWord ++ tailWord_984357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984416 : List Nat := [2, 1, 1, 3, 4, 1, 2, 4, 3]
def baseStart_984416 : Nat := 118140960795 + 984416 * 2 ^ 59
def prefixEnd_984416 : Nat := 4983230072969 + 3 ^ 40 * 984416 * 2
def baseEnd_984416 : Nat := 224657143100678089587893

theorem tailTrace_984416 : CollatzResearch.WordTrace tailWord_984416 prefixEnd_984416 224657143100678089587893 := by
  unfold tailWord_984416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17952300600818215856402551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23936400801090954475203401 17952300600818215856402551)
  ·
    refine ⟨26928450901227323784603827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17952300600818215856402551 26928450901227323784603827)
    ·
      refine ⟨40392676351840985676905741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26928450901227323784603827 40392676351840985676905741)
      ·
        refine ⟨15147253631940369628839653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40392676351840985676905741 15147253631940369628839653)
        ·
          refine ⟨2840110055988819305407435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15147253631940369628839653 2840110055988819305407435)
          ·
            refine ⟨4260165083983228958111153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840110055988819305407435 4260165083983228958111153)
            ·
              refine ⟨3195123812987421718583365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4260165083983228958111153 3195123812987421718583365)
              ·
                refine ⟨599085714935141572234381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3195123812987421718583365 599085714935141572234381)
                ·
                  refine ⟨224657143100678089587893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599085714935141572234381 224657143100678089587893)
                  ·
                    rfl

theorem cell21_984416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_984416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984416 prefixEnd_984416 := by exact prefixLift 984416
  have htrace : WordTrace (prefixWord ++ tailWord_984416) baseStart_984416 baseEnd_984416 := by
    simpa [prefixWord, tailWord_984416, baseEnd_984416] using wordTrace_append hprefix tailTrace_984416
  have hstable : (prefixWord ++ tailWord_984416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984416).length < 2 ^ (prefixWord ++ tailWord_984416).sum := by decide
  have hdescent : baseEnd_984416 < baseStart_984416 := by decide
  rcases family_descends (prefixWord ++ tailWord_984416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984450 : List Nat := [3, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_984450 : Nat := 118140960795 + 984450 * 2 ^ 59
def prefixEnd_984450 : Nat := 4983230072969 + 3 ^ 40 * 984450 * 2
def baseEnd_984450 : Nat := 224664902363901586021157

theorem tailTrace_984450 : CollatzResearch.WordTrace tailWord_984450 prefixEnd_984450 224664902363901586021157 := by
  unfold tailWord_984450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976460320878313879885701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23937227522342170346361869 8976460320878313879885701)
  ·
    refine ⟨1683086310164683852478569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8976460320878313879885701 1683086310164683852478569)
    ·
      refine ⟨1262314732623512889358927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1683086310164683852478569 1262314732623512889358927)
      ·
        refine ⟨1893472098935269334038391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262314732623512889358927 1893472098935269334038391)
        ·
          refine ⟨2840208148402904001057587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893472098935269334038391 2840208148402904001057587)
          ·
            refine ⟨4260312222604356001586381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840208148402904001057587 4260312222604356001586381)
            ·
              refine ⟨1597617083476633500594893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4260312222604356001586381 1597617083476633500594893)
              ·
                refine ⟨599106406303737562723085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597617083476633500594893 599106406303737562723085)
                ·
                  refine ⟨224664902363901586021157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599106406303737562723085 224664902363901586021157)
                  ·
                    rfl

theorem cell21_984450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_984450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984450 prefixEnd_984450 := by exact prefixLift 984450
  have htrace : WordTrace (prefixWord ++ tailWord_984450) baseStart_984450 baseEnd_984450 := by
    simpa [prefixWord, tailWord_984450, baseEnd_984450] using wordTrace_append hprefix tailTrace_984450
  have hstable : (prefixWord ++ tailWord_984450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984450).length < 2 ^ (prefixWord ++ tailWord_984450).sum := by decide
  have hdescent : baseEnd_984450 < baseStart_984450 := by decide
  rcases family_descends (prefixWord ++ tailWord_984450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984478 : List Nat := [4, 3, 1, 2, 2, 1, 2, 6]
def baseStart_984478 : Nat := 118140960795 + 984478 * 2 ^ 59
def prefixEnd_984478 : Nat := 4983230072969 + 3 ^ 40 * 984478 * 2
def baseEnd_984478 : Nat := 74890430781793253184811

theorem tailTrace_984478 : CollatzResearch.WordTrace tailWord_984478 prefixEnd_984478 74890430781793253184811 := by
  unfold tailWord_984478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488357815926477037695261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23937908351607877534374725 4488357815926477037695261)
  ·
    refine ⟨1683134180972428889135723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4488357815926477037695261 1683134180972428889135723)
    ·
      refine ⟨2524701271458643333703585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683134180972428889135723 2524701271458643333703585)
      ·
        refine ⟨1893525953593982500277689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2524701271458643333703585 1893525953593982500277689)
        ·
          refine ⟨1420144465195486875208267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1893525953593982500277689 1420144465195486875208267)
          ·
            refine ⟨2130216697793230312812401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420144465195486875208267 2130216697793230312812401)
            ·
              refine ⟨1597662523344922734609301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130216697793230312812401 1597662523344922734609301)
              ·
                refine ⟨74890430781793253184811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1597662523344922734609301 74890430781793253184811)
                ·
                  rfl

theorem cell21_984478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_984478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984478 prefixEnd_984478 := by exact prefixLift 984478
  have htrace : WordTrace (prefixWord ++ tailWord_984478) baseStart_984478 baseEnd_984478 := by
    simpa [prefixWord, tailWord_984478, baseEnd_984478] using wordTrace_append hprefix tailTrace_984478
  have hstable : (prefixWord ++ tailWord_984478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984478).length < 2 ^ (prefixWord ++ tailWord_984478).sum := by decide
  have hdescent : baseEnd_984478 < baseStart_984478 := by decide
  rcases family_descends (prefixWord ++ tailWord_984478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984503 : List Nat := [1, 1, 3, 1, 3, 2, 1, 9]
def baseStart_984503 : Nat := 118140960795 + 984503 * 2 ^ 59
def prefixEnd_984503 : Nat := 4983230072969 + 3 ^ 40 * 984503 * 2
def baseEnd_984503 : Nat := 74892332561995090545905

theorem tailTrace_984503 : CollatzResearch.WordTrace tailWord_984503 prefixEnd_984503 74892332561995090545905 := by
  unfold tailWord_984503
  simp only [CollatzResearch.WordTrace]
  refine ⟨35907774352321245571222163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23938516234880830380814775 35907774352321245571222163)
  ·
    refine ⟨53861661528481868356833245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35907774352321245571222163 53861661528481868356833245)
    ·
      refine ⟨20198123073180700633812467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53861661528481868356833245 20198123073180700633812467)
      ·
        refine ⟨30297184609771050950718701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20198123073180700633812467 30297184609771050950718701)
        ·
          refine ⟨11361444228664144106519513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30297184609771050950718701 11361444228664144106519513)
          ·
            refine ⟨8521083171498108079889635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11361444228664144106519513 8521083171498108079889635)
            ·
              refine ⟨12781624757247162119834453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8521083171498108079889635 12781624757247162119834453)
              ·
                refine ⟨74892332561995090545905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12781624757247162119834453 74892332561995090545905)
                ·
                  rfl

theorem cell21_984503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_984503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984503 prefixEnd_984503 := by exact prefixLift 984503
  have htrace : WordTrace (prefixWord ++ tailWord_984503) baseStart_984503 baseEnd_984503 := by
    simpa [prefixWord, tailWord_984503, baseEnd_984503] using wordTrace_append hprefix tailTrace_984503
  have hstable : (prefixWord ++ tailWord_984503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984503).length < 2 ^ (prefixWord ++ tailWord_984503).sum := by decide
  have hdescent : baseEnd_984503 < baseStart_984503 := by decide
  rcases family_descends (prefixWord ++ tailWord_984503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984551 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 5]
def baseStart_984551 : Nat := 118140960795 + 984551 * 2 ^ 59
def prefixEnd_984551 : Nat := 4983230072969 + 3 ^ 40 * 984551 * 2
def baseEnd_984551 : Nat := 224687951939947854837617

theorem tailTrace_984551 : CollatzResearch.WordTrace tailWord_984551 prefixEnd_984551 224687951939947854837617 := by
  unfold tailWord_984551
  simp only [CollatzResearch.WordTrace]
  refine ⟨35909525056147349768969507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23939683370764899845979671 35909525056147349768969507)
  ·
    refine ⟨53864287584221024653454261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35909525056147349768969507 53864287584221024653454261)
    ·
      refine ⟨5049776961020721061261337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53864287584221024653454261 5049776961020721061261337)
      ·
        refine ⟨3787332720765540795946003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5049776961020721061261337 3787332720765540795946003)
        ·
          refine ⟨5680999081148311193919005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787332720765540795946003 5680999081148311193919005)
          ·
            refine ⟨2130374655430616697719627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5680999081148311193919005 2130374655430616697719627)
            ·
              refine ⟨3195561983145925046579441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130374655430616697719627 3195561983145925046579441)
              ·
                refine ⟨2396671487359443784934581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195561983145925046579441 2396671487359443784934581)
                ·
                  refine ⟨224687951939947854837617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2396671487359443784934581 224687951939947854837617)
                  ·
                    rfl

theorem cell21_984551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_984551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984551 prefixEnd_984551 := by exact prefixLift 984551
  have htrace : WordTrace (prefixWord ++ tailWord_984551) baseStart_984551 baseEnd_984551 := by
    simpa [prefixWord, tailWord_984551, baseEnd_984551] using wordTrace_append hprefix tailTrace_984551
  have hstable : (prefixWord ++ tailWord_984551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984551).length < 2 ^ (prefixWord ++ tailWord_984551).sum := by decide
  have hdescent : baseEnd_984551 < baseStart_984551 := by decide
  rcases family_descends (prefixWord ++ tailWord_984551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984568 : List Nat := [2, 1, 2, 1, 1, 6, 2, 3, 3]
def baseStart_984568 : Nat := 118140960795 + 984568 * 2 ^ 59
def prefixEnd_984568 : Nat := 4983230072969 + 3 ^ 40 * 984568 * 2
def baseEnd_984568 : Nat := 224691831571559603054249

theorem tailTrace_984568 : CollatzResearch.WordTrace tailWord_984568 prefixEnd_984568 224691831571559603054249 := by
  unfold tailWord_984568
  simp only [CollatzResearch.WordTrace]
  refine ⟨17955072548542880836169179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23940096731390507781558905 17955072548542880836169179)
  ·
    refine ⟨26932608822814321254253769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17955072548542880836169179 26932608822814321254253769)
    ·
      refine ⟨20199456617110740940690327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26932608822814321254253769 20199456617110740940690327)
      ·
        refine ⟨30299184925666111411035491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20199456617110740940690327 30299184925666111411035491)
        ·
          refine ⟨45448777388499167116553237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30299184925666111411035491 45448777388499167116553237)
          ·
            refine ⟨2130411440085898458588433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45448777388499167116553237 2130411440085898458588433)
            ·
              refine ⟨1597808580064423843941325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130411440085898458588433 1597808580064423843941325)
              ·
                refine ⟨599178217524158941477997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597808580064423843941325 599178217524158941477997)
                ·
                  refine ⟨224691831571559603054249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599178217524158941477997 224691831571559603054249)
                  ·
                    rfl

theorem cell21_984568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_984568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984568 prefixEnd_984568 := by exact prefixLift 984568
  have htrace : WordTrace (prefixWord ++ tailWord_984568) baseStart_984568 baseEnd_984568 := by
    simpa [prefixWord, tailWord_984568, baseEnd_984568] using wordTrace_append hprefix tailTrace_984568
  have hstable : (prefixWord ++ tailWord_984568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984568).length < 2 ^ (prefixWord ++ tailWord_984568).sum := by decide
  have hdescent : baseEnd_984568 < baseStart_984568 := by decide
  rcases family_descends (prefixWord ++ tailWord_984568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984630 : List Nat := [5, 1, 2, 1, 4, 1, 7]
def baseStart_984630 : Nat := 118140960795 + 984630 * 2 ^ 59
def prefixEnd_984630 : Nat := 4983230072969 + 3 ^ 40 * 984630 * 2
def baseEnd_984630 : Nat := 24967331201806808113421

theorem tailTrace_984630 : CollatzResearch.WordTrace tailWord_984630 prefixEnd_984630 24967331201806808113421 := by
  unfold tailWord_984630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244525401428821641318459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23941604281907430840730229 2244525401428821641318459)
  ·
    refine ⟨3366788102143232461977689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244525401428821641318459 3366788102143232461977689)
    ·
      refine ⟨2525091076607424346483267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3366788102143232461977689 2525091076607424346483267)
      ·
        refine ⟨3787636614911136519724901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525091076607424346483267 3787636614911136519724901)
        ·
          refine ⟨710181865295838097448419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3787636614911136519724901 710181865295838097448419)
          ·
            refine ⟨1065272797943757146172629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710181865295838097448419 1065272797943757146172629)
            ·
              refine ⟨24967331201806808113421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1065272797943757146172629 24967331201806808113421)
              ·
                rfl

theorem cell21_984630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 7].length) (baseStart_984630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984630 prefixEnd_984630 := by exact prefixLift 984630
  have htrace : WordTrace (prefixWord ++ tailWord_984630) baseStart_984630 baseEnd_984630 := by
    simpa [prefixWord, tailWord_984630, baseEnd_984630] using wordTrace_append hprefix tailTrace_984630
  have hstable : (prefixWord ++ tailWord_984630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984630).length < 2 ^ (prefixWord ++ tailWord_984630).sum := by decide
  have hdescent : baseEnd_984630 < baseStart_984630 := by decide
  rcases family_descends (prefixWord ++ tailWord_984630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984641 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 6]
def baseStart_984641 : Nat := 118140960795 + 984641 * 2 ^ 59
def prefixEnd_984641 : Nat := 4983230072969 + 3 ^ 40 * 984641 * 2
def baseEnd_984641 : Nat := 224708491166127698337433

theorem tailTrace_984641 : CollatzResearch.WordTrace tailWord_984641 prefixEnd_984641 224708491166127698337433 := by
  unfold tailWord_984641
  simp only [CollatzResearch.WordTrace]
  refine ⟨35912807625821295139745777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23941871750547530093163851 35912807625821295139745777)
  ·
    refine ⟨26934605719365971354809333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35912807625821295139745777 26934605719365971354809333)
    ·
      refine ⟨2525119286190559814513375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26934605719365971354809333 2525119286190559814513375)
      ·
        refine ⟨3787678929285839721770063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525119286190559814513375 3787678929285839721770063)
        ·
          refine ⟨5681518393928759582655095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787678929285839721770063 5681518393928759582655095)
          ·
            refine ⟨8522277590893139373982643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681518393928759582655095 8522277590893139373982643)
            ·
              refine ⟨12783416386339709060973965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522277590893139373982643 12783416386339709060973965)
              ·
                refine ⟨4793781144877390897865237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12783416386339709060973965 4793781144877390897865237)
                ·
                  refine ⟨224708491166127698337433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4793781144877390897865237 224708491166127698337433)
                  ·
                    rfl

theorem cell21_984641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_984641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984641 prefixEnd_984641 := by exact prefixLift 984641
  have htrace : WordTrace (prefixWord ++ tailWord_984641) baseStart_984641 baseEnd_984641 := by
    simpa [prefixWord, tailWord_984641, baseEnd_984641] using wordTrace_append hprefix tailTrace_984641
  have hstable : (prefixWord ++ tailWord_984641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984641).length < 2 ^ (prefixWord ++ tailWord_984641).sum := by decide
  have hdescent : baseEnd_984641 < baseStart_984641 := by decide
  rcases family_descends (prefixWord ++ tailWord_984641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984658 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_984658 : Nat := 118140960795 + 984658 * 2 ^ 59
def prefixEnd_984658 : Nat := 4983230072969 + 3 ^ 40 * 984658 * 2
def baseEnd_984658 : Nat := 224712370797739446554065

theorem tailTrace_984658 : CollatzResearch.WordTrace tailWord_984658 prefixEnd_984658 224712370797739446554065 := by
  unfold tailWord_984658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8978356916689926760778657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23942285111173138028743085 8978356916689926760778657)
  ·
    refine ⟨6733767687517445070583993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8978356916689926760778657 6733767687517445070583993)
    ·
      refine ⟨5050325765638083802937995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6733767687517445070583993 5050325765638083802937995)
      ·
        refine ⟨7575488648457125704406993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050325765638083802937995 7575488648457125704406993)
        ·
          refine ⟨5681616486342844278305245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7575488648457125704406993 5681616486342844278305245)
          ·
            refine ⟨2130606182378566604364467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5681616486342844278305245 2130606182378566604364467)
            ·
              refine ⟨3195909273567849906546701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130606182378566604364467 3195909273567849906546701)
              ·
                refine ⟨1198465977587943714955013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195909273567849906546701 1198465977587943714955013)
                ·
                  refine ⟨224712370797739446554065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1198465977587943714955013 224712370797739446554065)
                  ·
                    rfl

theorem cell21_984658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_984658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984658 prefixEnd_984658 := by exact prefixLift 984658
  have htrace : WordTrace (prefixWord ++ tailWord_984658) baseStart_984658 baseEnd_984658 := by
    simpa [prefixWord, tailWord_984658, baseEnd_984658] using wordTrace_append hprefix tailTrace_984658
  have hstable : (prefixWord ++ tailWord_984658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984658).length < 2 ^ (prefixWord ++ tailWord_984658).sum := by decide
  have hdescent : baseEnd_984658 < baseStart_984658 := by decide
  rcases family_descends (prefixWord ++ tailWord_984658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984762 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_984762 : Nat := 118140960795 + 984762 * 2 ^ 59
def prefixEnd_984762 : Nat := 4983230072969 + 3 ^ 40 * 984762 * 2
def baseEnd_984762 : Nat := 224736105014658376820519

theorem tailTrace_984762 : CollatzResearch.WordTrace tailWord_984762 prefixEnd_984762 224736105014658376820519 := by
  unfold tailWord_984762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979305214595733201225135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23944813905588621869933693 8979305214595733201225135)
  ·
    refine ⟨13468957821893599801837703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8979305214595733201225135 13468957821893599801837703)
    ·
      refine ⟨20203436732840399702756555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13468957821893599801837703 20203436732840399702756555)
      ·
        refine ⟨30305155099260599554134833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20203436732840399702756555 30305155099260599554134833)
        ·
          refine ⟨22728866324445449665601125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30305155099260599554134833 22728866324445449665601125)
          ·
            refine ⟨4261662435833521812300211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22728866324445449665601125 4261662435833521812300211)
            ·
              refine ⟨6392493653750282718450317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261662435833521812300211 6392493653750282718450317)
              ·
                refine ⟨2397185120156356019418869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6392493653750282718450317 2397185120156356019418869)
                ·
                  refine ⟨224736105014658376820519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397185120156356019418869 224736105014658376820519)
                  ·
                    rfl

theorem cell21_984762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_984762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984762 prefixEnd_984762 := by exact prefixLift 984762
  have htrace : WordTrace (prefixWord ++ tailWord_984762) baseStart_984762 baseEnd_984762 := by
    simpa [prefixWord, tailWord_984762, baseEnd_984762] using wordTrace_append hprefix tailTrace_984762
  have hstable : (prefixWord ++ tailWord_984762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984762).length < 2 ^ (prefixWord ++ tailWord_984762).sum := by decide
  have hdescent : baseEnd_984762 < baseStart_984762 := by decide
  rcases family_descends (prefixWord ++ tailWord_984762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984813 : List Nat := [1, 5, 1, 2, 1, 3, 3, 2, 3]
def baseStart_984813 : Nat := 118140960795 + 984813 * 2 ^ 59
def prefixEnd_984813 : Nat := 4983230072969 + 3 ^ 40 * 984813 * 2
def baseEnd_984813 : Nat := 224747743909493621470415

theorem tailTrace_984813 : CollatzResearch.WordTrace tailWord_984813 prefixEnd_984813 224747743909493621470415 := by
  unfold tailWord_984813
  simp only [CollatzResearch.WordTrace]
  refine ⟨35919080981198168515007093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23946053987465445676671395 35919080981198168515007093)
  ·
    refine ⟨3367413841987328298281915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35919080981198168515007093 3367413841987328298281915)
    ·
      refine ⟨5051120762980992447422873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367413841987328298281915 5051120762980992447422873)
      ·
        refine ⟨3788340572235744335567155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5051120762980992447422873 3788340572235744335567155)
        ·
          refine ⟨5682510858353616503350733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788340572235744335567155 5682510858353616503350733)
          ·
            refine ⟨2130941571882606188756525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5682510858353616503350733 2130941571882606188756525)
            ·
              refine ⟨799103089455977320783697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2130941571882606188756525 799103089455977320783697)
              ·
                refine ⟨599327317091982990587773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799103089455977320783697 599327317091982990587773)
                ·
                  refine ⟨224747743909493621470415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599327317091982990587773 224747743909493621470415)
                  ·
                    rfl

theorem cell21_984813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_984813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984813 prefixEnd_984813 := by exact prefixLift 984813
  have htrace : WordTrace (prefixWord ++ tailWord_984813) baseStart_984813 baseEnd_984813 := by
    simpa [prefixWord, tailWord_984813, baseEnd_984813] using wordTrace_append hprefix tailTrace_984813
  have hstable : (prefixWord ++ tailWord_984813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984813).length < 2 ^ (prefixWord ++ tailWord_984813).sum := by decide
  have hdescent : baseEnd_984813 < baseStart_984813 := by decide
  rcases family_descends (prefixWord ++ tailWord_984813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984869 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 4]
def baseStart_984869 : Nat := 118140960795 + 984869 * 2 ^ 59
def prefixEnd_984869 : Nat := 4983230072969 + 3 ^ 40 * 984869 * 2
def baseEnd_984869 : Nat := 224760523872449968536967

theorem tailTrace_984869 : CollatzResearch.WordTrace tailWord_984869 prefixEnd_984869 224760523872449968536967 := by
  unfold tailWord_984869
  simp only [CollatzResearch.WordTrace]
  refine ⟨35921123468995290079045661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23947415645996860052697107 35921123468995290079045661)
  ·
    refine ⟨13470421300873233779642123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35921123468995290079045661 13470421300873233779642123)
    ·
      refine ⟨20205631951309850669463185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13470421300873233779642123 20205631951309850669463185)
      ·
        refine ⟨15154223963482388002097389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20205631951309850669463185 15154223963482388002097389)
        ·
          refine ⟨5682833986305895500786521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15154223963482388002097389 5682833986305895500786521)
          ·
            refine ⟨4262125489729421625589891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5682833986305895500786521 4262125489729421625589891)
            ·
              refine ⟨6393188234594132438384837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262125489729421625589891 6393188234594132438384837)
              ·
                refine ⟨1198722793986399832197157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6393188234594132438384837 1198722793986399832197157)
                ·
                  refine ⟨224760523872449968536967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1198722793986399832197157 224760523872449968536967)
                  ·
                    rfl

theorem cell21_984869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_984869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984869 prefixEnd_984869 := by exact prefixLift 984869
  have htrace : WordTrace (prefixWord ++ tailWord_984869) baseStart_984869 baseEnd_984869 := by
    simpa [prefixWord, tailWord_984869, baseEnd_984869] using wordTrace_append hprefix tailTrace_984869
  have hstable : (prefixWord ++ tailWord_984869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984869).length < 2 ^ (prefixWord ++ tailWord_984869).sum := by decide
  have hdescent : baseEnd_984869 < baseStart_984869 := by decide
  rcases family_descends (prefixWord ++ tailWord_984869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984872 : List Nat := [2, 1, 5, 1, 1, 3, 1, 4, 3]
def baseStart_984872 : Nat := 118140960795 + 984872 * 2 ^ 59
def prefixEnd_984872 : Nat := 4983230072969 + 3 ^ 40 * 984872 * 2
def baseEnd_984872 : Nat := 224761208513322629986961

theorem tailTrace_984872 : CollatzResearch.WordTrace tailWord_984872 prefixEnd_984872 224761208513322629986961 := by
  unfold tailWord_984872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960616443992210795702435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23947488591989614394269913 17960616443992210795702435)
  ·
    refine ⟨26940924665988316193553653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960616443992210795702435 26940924665988316193553653)
    ·
      refine ⟨2525711687436404643145655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26940924665988316193553653 2525711687436404643145655)
      ·
        refine ⟨3788567531154606964718483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525711687436404643145655 3788567531154606964718483)
        ·
          refine ⟨5682851296731910447077725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3788567531154606964718483 5682851296731910447077725)
          ·
            refine ⟨2131069236274466417654147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5682851296731910447077725 2131069236274466417654147)
            ·
              refine ⟨3196603854411699626481221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131069236274466417654147 3196603854411699626481221)
              ·
                refine ⟨599363222702193679965229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3196603854411699626481221 599363222702193679965229)
                ·
                  refine ⟨224761208513322629986961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599363222702193679965229 224761208513322629986961)
                  ·
                    rfl

theorem cell21_984872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_984872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984872 prefixEnd_984872 := by exact prefixLift 984872
  have htrace : WordTrace (prefixWord ++ tailWord_984872) baseStart_984872 baseEnd_984872 := by
    simpa [prefixWord, tailWord_984872, baseEnd_984872] using wordTrace_append hprefix tailTrace_984872
  have hstable : (prefixWord ++ tailWord_984872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984872).length < 2 ^ (prefixWord ++ tailWord_984872).sum := by decide
  have hdescent : baseEnd_984872 < baseStart_984872 := by decide
  rcases family_descends (prefixWord ++ tailWord_984872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984931 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 5]
def baseStart_984931 : Nat := 118140960795 + 984931 * 2 ^ 59
def prefixEnd_984931 : Nat := 4983230072969 + 3 ^ 40 * 984931 * 2
def baseEnd_984931 : Nat := 224774673117151638503507

theorem tailTrace_984931 : CollatzResearch.WordTrace tailWord_984931 prefixEnd_984931 224774673117151638503507 := by
  unfold tailWord_984931
  simp only [CollatzResearch.WordTrace]
  refine ⟨35923384794770674667802647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23948923196513783111868431 35923384794770674667802647)
  ·
    refine ⟨53885077192156012001703971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35923384794770674667802647 53885077192156012001703971)
    ·
      refine ⟨80827615788234018002555957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53885077192156012001703971 80827615788234018002555957)
      ·
        refine ⟨7577588980146939187739621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80827615788234018002555957 7577588980146939187739621)
        ·
          refine ⟨1420797933777551097701179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7577588980146939187739621 1420797933777551097701179)
          ·
            refine ⟨2131196900666326646551769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420797933777551097701179 2131196900666326646551769)
            ·
              refine ⟨1598397675499744984913827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131196900666326646551769 1598397675499744984913827)
              ·
                refine ⟨2397596513249617477370741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598397675499744984913827 2397596513249617477370741)
                ·
                  refine ⟨224774673117151638503507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397596513249617477370741 224774673117151638503507)
                  ·
                    rfl

theorem cell21_984931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_984931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984931 prefixEnd_984931 := by exact prefixLift 984931
  have htrace : WordTrace (prefixWord ++ tailWord_984931) baseStart_984931 baseEnd_984931 := by
    simpa [prefixWord, tailWord_984931, baseEnd_984931] using wordTrace_append hprefix tailTrace_984931
  have hstable : (prefixWord ++ tailWord_984931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984931).length < 2 ^ (prefixWord ++ tailWord_984931).sum := by decide
  have hdescent : baseEnd_984931 < baseStart_984931 := by decide
  rcases family_descends (prefixWord ++ tailWord_984931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984982 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_984982 : Nat := 118140960795 + 984982 * 2 ^ 59
def prefixEnd_984982 : Nat := 4983230072969 + 3 ^ 40 * 984982 * 2
def baseEnd_984982 : Nat := 224786312011986883153403

theorem tailTrace_984982 : CollatzResearch.WordTrace tailWord_984982 prefixEnd_984982 224786312011986883153403 := by
  unfold tailWord_984982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245327807349119398619325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23950163278390606918606133 2245327807349119398619325)
  ·
    refine ⟨841997927755919774482247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2245327807349119398619325 841997927755919774482247)
    ·
      refine ⟨1262996891633879661723371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 841997927755919774482247 1262996891633879661723371)
      ·
        refine ⟨1894495337450819492585057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262996891633879661723371 1894495337450819492585057)
        ·
          refine ⟨1420871503088114619438793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894495337450819492585057 1420871503088114619438793)
          ·
            refine ⟨1065653627316085964579095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1420871503088114619438793 1065653627316085964579095)
            ·
              refine ⟨1598480440974128946868643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065653627316085964579095 1598480440974128946868643)
              ·
                refine ⟨2397720661461193420302965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598480440974128946868643 2397720661461193420302965)
                ·
                  refine ⟨224786312011986883153403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397720661461193420302965 224786312011986883153403)
                  ·
                    rfl

theorem cell21_984982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_984982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_984982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_984982 prefixEnd_984982 := by exact prefixLift 984982
  have htrace : WordTrace (prefixWord ++ tailWord_984982) baseStart_984982 baseEnd_984982 := by
    simpa [prefixWord, tailWord_984982, baseEnd_984982] using wordTrace_append hprefix tailTrace_984982
  have hstable : (prefixWord ++ tailWord_984982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984982).length < 2 ^ (prefixWord ++ tailWord_984982).sum := by decide
  have hdescent : baseEnd_984982 < baseStart_984982 := by decide
  rcases family_descends (prefixWord ++ tailWord_984982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985066 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_985066 : Nat := 118140960795 + 985066 * 2 ^ 59
def prefixEnd_985066 : Nat := 4983230072969 + 3 ^ 40 * 985066 * 2
def baseEnd_985066 : Nat := 224805481956421403753231

theorem tailTrace_985066 : CollatzResearch.WordTrace tailWord_985066 prefixEnd_985066 224805481956421403753231 := by
  unfold tailWord_985066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8982077162320398180991763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23952205766187728482644701 8982077162320398180991763)
  ·
    refine ⟨13473115743480597271487645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8982077162320398180991763 13473115743480597271487645)
    ·
      refine ⟨5052418403805223976807867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13473115743480597271487645 5052418403805223976807867)
      ·
        refine ⟨7578627605707835965211801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5052418403805223976807867 7578627605707835965211801)
        ·
          refine ⟨5683970704280876973908851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7578627605707835965211801 5683970704280876973908851)
          ·
            refine ⟨8525956056421315460863277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683970704280876973908851 8525956056421315460863277)
            ·
              refine ⟨3197233521157993297823729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8525956056421315460863277 3197233521157993297823729)
              ·
                refine ⟨2397925140868494973367797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197233521157993297823729 2397925140868494973367797)
                ·
                  refine ⟨224805481956421403753231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397925140868494973367797 224805481956421403753231)
                  ·
                    rfl

theorem cell21_985066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_985066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985066 prefixEnd_985066 := by exact prefixLift 985066
  have htrace : WordTrace (prefixWord ++ tailWord_985066) baseStart_985066 baseEnd_985066 := by
    simpa [prefixWord, tailWord_985066, baseEnd_985066] using wordTrace_append hprefix tailTrace_985066
  have hstable : (prefixWord ++ tailWord_985066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985066).length < 2 ^ (prefixWord ++ tailWord_985066).sum := by decide
  have hdescent : baseEnd_985066 < baseStart_985066 := by decide
  rcases family_descends (prefixWord ++ tailWord_985066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985114 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_985114 : Nat := 118140960795 + 985114 * 2 ^ 59
def prefixEnd_985114 : Nat := 4983230072969 + 3 ^ 40 * 985114 * 2
def baseEnd_985114 : Nat := 224816436210383986953133

theorem tailTrace_985114 : CollatzResearch.WordTrace tailWord_985114 prefixEnd_985114 224816436210383986953133 := by
  unfold tailWord_985114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8982514838276924230428599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23953372902071797947809597 8982514838276924230428599)
  ·
    refine ⟨13473772257415386345642899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8982514838276924230428599 13473772257415386345642899)
    ·
      refine ⟨20210658386123079518464349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13473772257415386345642899 20210658386123079518464349)
      ·
        refine ⟨7578996894796154819424131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20210658386123079518464349 7578996894796154819424131)
        ·
          refine ⟨11368495342194232229136197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578996894796154819424131 11368495342194232229136197)
          ·
            refine ⟨2131592876661418542963037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11368495342194232229136197 2131592876661418542963037)
            ·
              refine ⟨799347328748031953611139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2131592876661418542963037 799347328748031953611139)
              ·
                refine ⟨1199020993122047930416709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799347328748031953611139 1199020993122047930416709)
                ·
                  refine ⟨224816436210383986953133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199020993122047930416709 224816436210383986953133)
                  ·
                    rfl

theorem cell21_985114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_985114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985114 prefixEnd_985114 := by exact prefixLift 985114
  have htrace : WordTrace (prefixWord ++ tailWord_985114) baseStart_985114 baseEnd_985114 := by
    simpa [prefixWord, tailWord_985114, baseEnd_985114] using wordTrace_append hprefix tailTrace_985114
  have hstable : (prefixWord ++ tailWord_985114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985114).length < 2 ^ (prefixWord ++ tailWord_985114).sum := by decide
  have hdescent : baseEnd_985114 < baseStart_985114 := by decide
  rcases family_descends (prefixWord ++ tailWord_985114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985173 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 4]
def baseStart_985173 : Nat := 118140960795 + 985173 * 2 ^ 59
def prefixEnd_985173 : Nat := 4983230072969 + 3 ^ 40 * 985173 * 2
def baseEnd_985173 : Nat := 224829900814212995469679

theorem tailTrace_985173 : CollatzResearch.WordTrace tailWord_985173 prefixEnd_985173 224829900814212995469679 := by
  unfold tailWord_985173
  simp only [CollatzResearch.WordTrace]
  refine ⟨35932211259893949998112173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23954807506595966665408115 35932211259893949998112173)
  ·
    refine ⟨13474579222460231249292065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35932211259893949998112173 13474579222460231249292065)
    ·
      refine ⟨10105934416845173436969049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13474579222460231249292065 10105934416845173436969049)
      ·
        refine ⟨7579450812633880077726787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10105934416845173436969049 7579450812633880077726787)
        ·
          refine ⟨11369176218950820116590181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7579450812633880077726787 11369176218950820116590181)
          ·
            refine ⟨2131720541053278771860659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11369176218950820116590181 2131720541053278771860659)
            ·
              refine ⟨3197580811579918157790989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131720541053278771860659 3197580811579918157790989)
              ·
                refine ⟨1199092804342469309171621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3197580811579918157790989 1199092804342469309171621)
                ·
                  refine ⟨224829900814212995469679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199092804342469309171621 224829900814212995469679)
                  ·
                    rfl

theorem cell21_985173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_985173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985173 prefixEnd_985173 := by exact prefixLift 985173
  have htrace : WordTrace (prefixWord ++ tailWord_985173) baseStart_985173 baseEnd_985173 := by
    simpa [prefixWord, tailWord_985173, baseEnd_985173] using wordTrace_append hprefix tailTrace_985173
  have hstable : (prefixWord ++ tailWord_985173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985173).length < 2 ^ (prefixWord ++ tailWord_985173).sum := by decide
  have hdescent : baseEnd_985173 < baseStart_985173 := by decide
  rcases family_descends (prefixWord ++ tailWord_985173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985232 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_985232 : Nat := 118140960795 + 985232 * 2 ^ 59
def prefixEnd_985232 : Nat := 4983230072969 + 3 ^ 40 * 985232 * 2
def baseEnd_985232 : Nat := 224843365418042003986225

theorem tailTrace_985232 : CollatzResearch.WordTrace tailWord_985232 prefixEnd_985232 224843365418042003986225 := by
  unfold tailWord_985232
  simp only [CollatzResearch.WordTrace]
  refine ⟨17967181583340101537254975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23956242111120135383006633 17967181583340101537254975)
  ·
    refine ⟨26950772375010152305882463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17967181583340101537254975 26950772375010152305882463)
    ·
      refine ⟨40426158562515228458823695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26950772375010152305882463 40426158562515228458823695)
      ·
        refine ⟨60639237843772842688235543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40426158562515228458823695 60639237843772842688235543)
        ·
          refine ⟨90958856765659264032353315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60639237843772842688235543 90958856765659264032353315)
          ·
            refine ⟨136438285148488896048529973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90958856765659264032353315 136438285148488896048529973)
            ·
              refine ⟨12791089232670834004549685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136438285148488896048529973 12791089232670834004549685)
              ·
                refine ⟨1199164615562890687926533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12791089232670834004549685 1199164615562890687926533)
                ·
                  refine ⟨224843365418042003986225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199164615562890687926533 224843365418042003986225)
                  ·
                    rfl

theorem cell21_985232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_985232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985232 prefixEnd_985232 := by exact prefixLift 985232
  have htrace : WordTrace (prefixWord ++ tailWord_985232) baseStart_985232 baseEnd_985232 := by
    simpa [prefixWord, tailWord_985232, baseEnd_985232] using wordTrace_append hprefix tailTrace_985232
  have hstable : (prefixWord ++ tailWord_985232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985232).length < 2 ^ (prefixWord ++ tailWord_985232).sum := by decide
  have hdescent : baseEnd_985232 < baseStart_985232 := by decide
  rcases family_descends (prefixWord ++ tailWord_985232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985252 : List Nat := [2, 3, 1, 2, 4, 1, 2, 3, 3]
def baseStart_985252 : Nat := 118140960795 + 985252 * 2 ^ 59
def prefixEnd_985252 : Nat := 4983230072969 + 3 ^ 40 * 985252 * 2
def baseEnd_985252 : Nat := 224847929690526413652851

theorem tailTrace_985252 : CollatzResearch.WordTrace tailWord_985252 prefixEnd_985252 224847929690526413652851 := by
  unfold tailWord_985252
  simp only [CollatzResearch.WordTrace]
  refine ⟨17967546313303873245119005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23956728417738497660158673 17967546313303873245119005)
  ·
    refine ⟨6737829867488952466919627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17967546313303873245119005 6737829867488952466919627)
    ·
      refine ⟨10106744801233428700379441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6737829867488952466919627 10106744801233428700379441)
      ·
        refine ⟨7580058600925071525284581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10106744801233428700379441 7580058600925071525284581)
        ·
          refine ⟨1421260987673450910990859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7580058600925071525284581 1421260987673450910990859)
          ·
            refine ⟨2131891481510176366486289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421260987673450910990859 2131891481510176366486289)
            ·
              refine ⟨1598918611132632274864717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131891481510176366486289 1598918611132632274864717)
              ·
                refine ⟨599594479174737103074269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1598918611132632274864717 599594479174737103074269)
                ·
                  refine ⟨224847929690526413652851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599594479174737103074269 224847929690526413652851)
                  ·
                    rfl

theorem cell21_985252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_985252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985252 prefixEnd_985252 := by exact prefixLift 985252
  have htrace : WordTrace (prefixWord ++ tailWord_985252) baseStart_985252 baseEnd_985252 := by
    simpa [prefixWord, tailWord_985252, baseEnd_985252] using wordTrace_append hprefix tailTrace_985252
  have hstable : (prefixWord ++ tailWord_985252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985252).length < 2 ^ (prefixWord ++ tailWord_985252).sum := by decide
  have hdescent : baseEnd_985252 < baseStart_985252 := by decide
  rcases family_descends (prefixWord ++ tailWord_985252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985294 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_985294 : Nat := 118140960795 + 985294 * 2 ^ 59
def prefixEnd_985294 : Nat := 4983230072969 + 3 ^ 40 * 985294 * 2
def baseEnd_985294 : Nat := 224857514662743673952765

theorem tailTrace_985294 : CollatzResearch.WordTrace tailWord_985294 prefixEnd_985294 224857514662743673952765 := by
  unfold tailWord_985294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492078061556948457908367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23957749661637058442177957 4492078061556948457908367)
  ·
    refine ⟨6738117092335422686862551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492078061556948457908367 6738117092335422686862551)
    ·
      refine ⟨10107175638503134030293827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738117092335422686862551 10107175638503134030293827)
      ·
        refine ⟨15160763457754701045440741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10107175638503134030293827 15160763457754701045440741)
        ·
          refine ⟨2842643148329006446020139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15160763457754701045440741 2842643148329006446020139)
          ·
            refine ⟨4263964722493509669030209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842643148329006446020139 4263964722493509669030209)
            ·
              refine ⟨3197973541870132251772657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4263964722493509669030209 3197973541870132251772657)
              ·
                refine ⟨2398480156402599188829493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197973541870132251772657 2398480156402599188829493)
                ·
                  refine ⟨224857514662743673952765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2398480156402599188829493 224857514662743673952765)
                  ·
                    rfl

theorem cell21_985294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_985294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985294 prefixEnd_985294 := by exact prefixLift 985294
  have htrace : WordTrace (prefixWord ++ tailWord_985294) baseStart_985294 baseEnd_985294 := by
    simpa [prefixWord, tailWord_985294, baseEnd_985294] using wordTrace_append hprefix tailTrace_985294
  have hstable : (prefixWord ++ tailWord_985294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985294).length < 2 ^ (prefixWord ++ tailWord_985294).sum := by decide
  have hdescent : baseEnd_985294 < baseStart_985294 := by decide
  rcases family_descends (prefixWord ++ tailWord_985294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985314 : List Nat := [3, 3, 4, 1, 1, 2, 7]
def baseStart_985314 : Nat := 118140960795 + 985314 * 2 ^ 59
def prefixEnd_985314 : Nat := 4983230072969 + 3 ^ 40 * 985314 * 2
def baseEnd_985314 : Nat := 24984675437247564846599

theorem tailTrace_985314 : CollatzResearch.WordTrace tailWord_985314 prefixEnd_985314 24984675437247564846599 := by
  unfold tailWord_985314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984338488095782769748749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23958235968255420719329997 8984338488095782769748749)
  ·
    refine ⟨3369126933035918538655781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8984338488095782769748749 3369126933035918538655781)
    ·
      refine ⟨631711299944234725997959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3369126933035918538655781 631711299944234725997959)
      ·
        refine ⟨947566949916352088996939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631711299944234725997959 947566949916352088996939)
        ·
          refine ⟨1421350424874528133495409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947566949916352088996939 1421350424874528133495409)
          ·
            refine ⟨1066012818655896100121557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421350424874528133495409 1066012818655896100121557)
            ·
              refine ⟨24984675437247564846599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1066012818655896100121557 24984675437247564846599)
              ·
                rfl

theorem cell21_985314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 7].length) (baseStart_985314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985314 prefixEnd_985314 := by exact prefixLift 985314
  have htrace : WordTrace (prefixWord ++ tailWord_985314) baseStart_985314 baseEnd_985314 := by
    simpa [prefixWord, tailWord_985314, baseEnd_985314] using wordTrace_append hprefix tailTrace_985314
  have hstable : (prefixWord ++ tailWord_985314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985314).length < 2 ^ (prefixWord ++ tailWord_985314).sum := by decide
  have hdescent : baseEnd_985314 < baseStart_985314 := by decide
  rcases family_descends (prefixWord ++ tailWord_985314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985390 : List Nat := [4, 1, 3, 3, 2, 1, 1, 6]
def baseStart_985390 : Nat := 118140960795 + 985390 * 2 ^ 59
def prefixEnd_985390 : Nat := 4983230072969 + 3 ^ 40 * 985390 * 2
def baseEnd_985390 : Nat := 74959807723556280117523

theorem tailTrace_985390 : CollatzResearch.WordTrace tailWord_985390 prefixEnd_985390 74959807723556280117523 := by
  unfold tailWord_985390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492515737513474507345203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23960083933405197372507749 4492515737513474507345203)
  ·
    refine ⟨6738773606270211761017805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492515737513474507345203 6738773606270211761017805)
    ·
      refine ⟨2527040102351329410381677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6738773606270211761017805 2527040102351329410381677)
      ·
        refine ⟨947640038381748528893129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2527040102351329410381677 947640038381748528893129)
        ·
          refine ⟨710730028786311396669847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947640038381748528893129 710730028786311396669847)
          ·
            refine ⟨1066095043179467095004771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710730028786311396669847 1066095043179467095004771)
            ·
              refine ⟨1599142564769200642507157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066095043179467095004771 1599142564769200642507157)
              ·
                refine ⟨74959807723556280117523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1599142564769200642507157 74959807723556280117523)
                ·
                  rfl

theorem cell21_985390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_985390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985390 prefixEnd_985390 := by exact prefixLift 985390
  have htrace : WordTrace (prefixWord ++ tailWord_985390) baseStart_985390 baseEnd_985390 := by
    simpa [prefixWord, tailWord_985390, baseEnd_985390] using wordTrace_append hprefix tailTrace_985390
  have hstable : (prefixWord ++ tailWord_985390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985390).length < 2 ^ (prefixWord ++ tailWord_985390).sum := by decide
  have hdescent : baseEnd_985390 < baseStart_985390 := by decide
  rcases family_descends (prefixWord ++ tailWord_985390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985401 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 4]
def baseStart_985401 : Nat := 118140960795 + 985401 * 2 ^ 59
def prefixEnd_985401 : Nat := 4983230072969 + 3 ^ 40 * 985401 * 2
def baseEnd_985401 : Nat := 224881933520535265669213

theorem tailTrace_985401 : CollatzResearch.WordTrace tailWord_985401 prefixEnd_985401 224881933520535265669213 := by
  unfold tailWord_985401
  simp only [CollatzResearch.WordTrace]
  refine ⟨35940527103067944937412057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23960351402045296624941371 35940527103067944937412057)
  ·
    refine ⟨26955395327300958703059043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35940527103067944937412057 26955395327300958703059043)
    ·
      refine ⟨40433092990951438054588565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26955395327300958703059043 40433092990951438054588565)
      ·
        refine ⟨1895301233950848658808839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40433092990951438054588565 1895301233950848658808839)
        ·
          refine ⟨2842951850926272988213259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895301233950848658808839 2842951850926272988213259)
          ·
            refine ⟨4264427776389409482319889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842951850926272988213259 4264427776389409482319889)
            ·
              refine ⟨3198320832292057111739917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264427776389409482319889 3198320832292057111739917)
              ·
                refine ⟨1199370312109521416902469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198320832292057111739917 1199370312109521416902469)
                ·
                  refine ⟨224881933520535265669213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199370312109521416902469 224881933520535265669213)
                  ·
                    rfl

theorem cell21_985401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_985401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985401 prefixEnd_985401 := by exact prefixLift 985401
  have htrace : WordTrace (prefixWord ++ tailWord_985401) baseStart_985401 baseEnd_985401 := by
    simpa [prefixWord, tailWord_985401, baseEnd_985401] using wordTrace_append hprefix tailTrace_985401
  have hstable : (prefixWord ++ tailWord_985401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985401).length < 2 ^ (prefixWord ++ tailWord_985401).sum := by decide
  have hdescent : baseEnd_985401 < baseStart_985401 := by decide
  rcases family_descends (prefixWord ++ tailWord_985401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985415 : List Nat := [1, 1, 4, 1, 2, 2, 5, 5]
def baseStart_985415 : Nat := 118140960795 + 985415 * 2 ^ 59
def prefixEnd_985415 : Nat := 4983230072969 + 3 ^ 40 * 985415 * 2
def baseEnd_985415 : Nat := 74961709503758117478617

theorem tailTrace_985415 : CollatzResearch.WordTrace tailWord_985415 prefixEnd_985415 74961709503758117478617 := by
  unfold tailWord_985415
  simp only [CollatzResearch.WordTrace]
  refine ⟨35941037725017225328421699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23960691816678150218947799 35941037725017225328421699)
  ·
    refine ⟨53911556587525837992632549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35941037725017225328421699 53911556587525837992632549)
    ·
      refine ⟨10108416860161094623618603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53911556587525837992632549 10108416860161094623618603)
      ·
        refine ⟨15162625290241641935427905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108416860161094623618603 15162625290241641935427905)
        ·
          refine ⟨11371968967681231451570929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15162625290241641935427905 11371968967681231451570929)
          ·
            refine ⟨8528976725760923588678197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11371968967681231451570929 8528976725760923588678197)
            ·
              refine ⟨799591568040086586438581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8528976725760923588678197 799591568040086586438581)
              ·
                refine ⟨74961709503758117478617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 799591568040086586438581 74961709503758117478617)
                ·
                  rfl

theorem cell21_985415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 5].length) (baseStart_985415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985415 prefixEnd_985415 := by exact prefixLift 985415
  have htrace : WordTrace (prefixWord ++ tailWord_985415) baseStart_985415 baseEnd_985415 := by
    simpa [prefixWord, tailWord_985415, baseEnd_985415] using wordTrace_append hprefix tailTrace_985415
  have hstable : (prefixWord ++ tailWord_985415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985415).length < 2 ^ (prefixWord ++ tailWord_985415).sum := by decide
  have hdescent : baseEnd_985415 < baseStart_985415 := by decide
  rcases family_descends (prefixWord ++ tailWord_985415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985438 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_985438 : Nat := 118140960795 + 985438 * 2 ^ 59
def prefixEnd_985438 : Nat := 4983230072969 + 3 ^ 40 * 985438 * 2
def baseEnd_985438 : Nat := 224890377424631423552471

theorem tailTrace_985438 : CollatzResearch.WordTrace tailWord_985438 prefixEnd_985438 224890377424631423552471 := by
  unfold tailWord_985438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492734575491737532063621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23961251069289266837672645 4492734575491737532063621)
  ·
    refine ⟨842387732904700787261929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4492734575491737532063621 842387732904700787261929)
    ·
      refine ⟨631790799678525590446447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 842387732904700787261929 631790799678525590446447)
      ·
        refine ⟨947686199517788385669671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631790799678525590446447 947686199517788385669671)
        ·
          refine ⟨1421529299276682578504507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947686199517788385669671 1421529299276682578504507)
          ·
            refine ⟨2132293948915023867756761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421529299276682578504507 2132293948915023867756761)
            ·
              refine ⟨1599220461686267900817571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132293948915023867756761 1599220461686267900817571)
              ·
                refine ⟨2398830692529401851226357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599220461686267900817571 2398830692529401851226357)
                ·
                  refine ⟨224890377424631423552471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2398830692529401851226357 224890377424631423552471)
                  ·
                    rfl

theorem cell21_985438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_985438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985438 prefixEnd_985438 := by exact prefixLift 985438
  have htrace : WordTrace (prefixWord ++ tailWord_985438) baseStart_985438 baseEnd_985438 := by
    simpa [prefixWord, tailWord_985438, baseEnd_985438] using wordTrace_append hprefix tailTrace_985438
  have hstable : (prefixWord ++ tailWord_985438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985438).length < 2 ^ (prefixWord ++ tailWord_985438).sum := by decide
  have hdescent : baseEnd_985438 < baseStart_985438 := by decide
  rcases family_descends (prefixWord ++ tailWord_985438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985556 : List Nat := [2, 4, 1, 2, 2, 1, 4, 2, 3]
def baseStart_985556 : Nat := 118140960795 + 985556 * 2 ^ 59
def prefixEnd_985556 : Nat := 4983230072969 + 3 ^ 40 * 985556 * 2
def baseEnd_985556 : Nat := 224917306632289440585563

theorem tailTrace_985556 : CollatzResearch.WordTrace tailWord_985556 prefixEnd_985556 224917306632289440585563 := by
  unfold tailWord_985556
  simp only [CollatzResearch.WordTrace]
  refine ⟨17973090208753203204652261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23964120278337604272869681 17973090208753203204652261)
  ·
    refine ⟨3369954414141225600872299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17973090208753203204652261 3369954414141225600872299)
    ·
      refine ⟨5054931621211838401308449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3369954414141225600872299 5054931621211838401308449)
      ·
        refine ⟨3791198715908878800981337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5054931621211838401308449 3791198715908878800981337)
        ·
          refine ⟨2843399036931659100736003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3791198715908878800981337 2843399036931659100736003)
          ·
            refine ⟨4265098555397488651104005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843399036931659100736003 4265098555397488651104005)
            ·
              refine ⟨799705979137029122082001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4265098555397488651104005 799705979137029122082001)
              ·
                refine ⟨599779484352771841561501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799705979137029122082001 599779484352771841561501)
                ·
                  refine ⟨224917306632289440585563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599779484352771841561501 224917306632289440585563)
                  ·
                    rfl

theorem cell21_985556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_985556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985556 prefixEnd_985556 := by exact prefixLift 985556
  have htrace : WordTrace (prefixWord ++ tailWord_985556) baseStart_985556 baseEnd_985556 := by
    simpa [prefixWord, tailWord_985556, baseEnd_985556] using wordTrace_append hprefix tailTrace_985556
  have hstable : (prefixWord ++ tailWord_985556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985556).length < 2 ^ (prefixWord ++ tailWord_985556).sum := by decide
  have hdescent : baseEnd_985556 < baseStart_985556 := by decide
  rcases family_descends (prefixWord ++ tailWord_985556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985567 : List Nat := [1, 1, 2, 3, 3, 4, 1, 6]
def baseStart_985567 : Nat := 118140960795 + 985567 * 2 ^ 59
def prefixEnd_985567 : Nat := 4983230072969 + 3 ^ 40 * 985567 * 2
def baseEnd_985567 : Nat := 74973272327385288634069

theorem tailTrace_985567 : CollatzResearch.WordTrace tailWord_985567 prefixEnd_985567 74973272327385288634069 := by
  unfold tailWord_985567
  simp only [CollatzResearch.WordTrace]
  refine ⟨35946581620466555287954955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23964387746977703525303303 35946581620466555287954955)
  ·
    refine ⟨53919872430699832931932433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35946581620466555287954955 53919872430699832931932433)
    ·
      refine ⟨40439904323024874698949325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53919872430699832931932433 40439904323024874698949325)
      ·
        refine ⟨15164964121134328012105997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40439904323024874698949325 15164964121134328012105997)
        ·
          refine ⟨5686861545425373004539749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15164964121134328012105997 5686861545425373004539749)
          ·
            refine ⟨1066286539767257438351203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5686861545425373004539749 1066286539767257438351203)
            ·
              refine ⟨1599429809650886157526805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066286539767257438351203 1599429809650886157526805)
              ·
                refine ⟨74973272327385288634069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1599429809650886157526805 74973272327385288634069)
                ·
                  rfl

theorem cell21_985567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 6].length) (baseStart_985567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985567 prefixEnd_985567 := by exact prefixLift 985567
  have htrace : WordTrace (prefixWord ++ tailWord_985567) baseStart_985567 baseEnd_985567 := by
    simpa [prefixWord, tailWord_985567, baseEnd_985567] using wordTrace_append hprefix tailTrace_985567
  have hstable : (prefixWord ++ tailWord_985567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985567).length < 2 ^ (prefixWord ++ tailWord_985567).sum := by decide
  have hdescent : baseEnd_985567 < baseStart_985567 := by decide
  rcases family_descends (prefixWord ++ tailWord_985567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985612 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_985612 : Nat := 118140960795 + 985612 * 2 ^ 59
def prefixEnd_985612 : Nat := 4983230072969 + 3 ^ 40 * 985612 * 2
def baseEnd_985612 : Nat := 224930086595245787652115

theorem tailTrace_985612 : CollatzResearch.WordTrace tailWord_985612 prefixEnd_985612 224930086595245787652115 := by
  unfold tailWord_985612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17974111452651763986671545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23965481936869018648895393 17974111452651763986671545)
  ·
    refine ⟨13480583589488822990003659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17974111452651763986671545 13480583589488822990003659)
    ·
      refine ⟨20220875384233234485005489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13480583589488822990003659 20220875384233234485005489)
      ·
        refine ⟨15165656538174925863754117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20220875384233234485005489 15165656538174925863754117)
        ·
          refine ⟨2843560600907798599453897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15165656538174925863754117 2843560600907798599453897)
          ·
            refine ⟨2132670450680848949590423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2843560600907798599453897 2132670450680848949590423)
            ·
              refine ⟨3199005676021273424385635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132670450680848949590423 3199005676021273424385635)
              ·
                refine ⟨4798508514031910136578453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199005676021273424385635 4798508514031910136578453)
                ·
                  refine ⟨224930086595245787652115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4798508514031910136578453 224930086595245787652115)
                  ·
                    rfl

theorem cell21_985612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_985612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985612 prefixEnd_985612 := by exact prefixLift 985612
  have htrace : WordTrace (prefixWord ++ tailWord_985612) baseStart_985612 baseEnd_985612 := by
    simpa [prefixWord, tailWord_985612, baseEnd_985612] using wordTrace_append hprefix tailTrace_985612
  have hstable : (prefixWord ++ tailWord_985612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985612).length < 2 ^ (prefixWord ++ tailWord_985612).sum := by decide
  have hdescent : baseEnd_985612 < baseStart_985612 := by decide
  rcases family_descends (prefixWord ++ tailWord_985612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985674 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_985674 : Nat := 118140960795 + 985674 * 2 ^ 59
def prefixEnd_985674 : Nat := 4983230072969 + 3 ^ 40 * 985674 * 2
def baseEnd_985674 : Nat := 224944235839947457618655

theorem tailTrace_985674 : CollatzResearch.WordTrace tailWord_985674 prefixEnd_985674 224944235839947457618655 := by
  unfold tailWord_985674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987621057769728140525019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23966989487385941708066717 8987621057769728140525019)
  ·
    refine ⟨13481431586654592210787529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8987621057769728140525019 13481431586654592210787529)
    ·
      refine ⟨10111073689990944158090647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13481431586654592210787529 10111073689990944158090647)
      ·
        refine ⟨15166610534986416237135971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10111073689990944158090647 15166610534986416237135971)
        ·
          refine ⟨22749915802479624355703957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15166610534986416237135971 22749915802479624355703957)
          ·
            refine ⟨1066402303241232391673623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22749915802479624355703957 1066402303241232391673623)
            ·
              refine ⟨1599603454861848587510435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066402303241232391673623 1599603454861848587510435)
              ·
                refine ⟨2399405182292772881265653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599603454861848587510435 2399405182292772881265653)
                ·
                  refine ⟨224944235839947457618655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2399405182292772881265653 224944235839947457618655)
                  ·
                    rfl

theorem cell21_985674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_985674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985674 prefixEnd_985674 := by exact prefixLift 985674
  have htrace : WordTrace (prefixWord ++ tailWord_985674) baseStart_985674 baseEnd_985674 := by
    simpa [prefixWord, tailWord_985674, baseEnd_985674] using wordTrace_append hprefix tailTrace_985674
  have hstable : (prefixWord ++ tailWord_985674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985674).length < 2 ^ (prefixWord ++ tailWord_985674).sum := by decide
  have hdescent : baseEnd_985674 < baseStart_985674 := by decide
  rcases family_descends (prefixWord ++ tailWord_985674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985725 : List Nat := [1, 4, 1, 1, 6, 1, 2, 2, 3]
def baseStart_985725 : Nat := 118140960795 + 985725 * 2 ^ 59
def prefixEnd_985725 : Nat := 4983230072969 + 3 ^ 40 * 985725 * 2
def baseEnd_985725 : Nat := 224955874734782702268551

theorem tailTrace_985725 : CollatzResearch.WordTrace tailWord_985725 prefixEnd_985725 224955874734782702268551 := by
  unfold tailWord_985725
  simp only [CollatzResearch.WordTrace]
  refine ⟨35952344353894148272206629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23968229569262765514804419 35952344353894148272206629)
  ·
    refine ⟨6741064566355152801038743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35952344353894148272206629 6741064566355152801038743)
    ·
      refine ⟨10111596849532729201558115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6741064566355152801038743 10111596849532729201558115)
      ·
        refine ⟨15167395274299093802337173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10111596849532729201558115 15167395274299093802337173)
        ·
          refine ⟨710971653482770021984555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15167395274299093802337173 710971653482770021984555)
          ·
            refine ⟨1066457480224155032976833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710971653482770021984555 1066457480224155032976833)
            ·
              refine ⟨799843110168116274732625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066457480224155032976833 799843110168116274732625)
              ·
                refine ⟨599882332626087206049469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799843110168116274732625 599882332626087206049469)
                ·
                  refine ⟨224955874734782702268551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599882332626087206049469 224955874734782702268551)
                  ·
                    rfl

theorem cell21_985725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_985725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985725 prefixEnd_985725 := by exact prefixLift 985725
  have htrace : WordTrace (prefixWord ++ tailWord_985725) baseStart_985725 baseEnd_985725 := by
    simpa [prefixWord, tailWord_985725, baseEnd_985725] using wordTrace_append hprefix tailTrace_985725
  have hstable : (prefixWord ++ tailWord_985725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985725).length < 2 ^ (prefixWord ++ tailWord_985725).sum := by decide
  have hdescent : baseEnd_985725 < baseStart_985725 := by decide
  rcases family_descends (prefixWord ++ tailWord_985725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985781 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 4]
def baseStart_985781 : Nat := 118140960795 + 985781 * 2 ^ 59
def prefixEnd_985781 : Nat := 4983230072969 + 3 ^ 40 * 985781 * 2
def baseEnd_985781 : Nat := 224968654697739049335103

theorem tailTrace_985781 : CollatzResearch.WordTrace tailWord_985781 prefixEnd_985781 224968654697739049335103 := by
  unfold tailWord_985781
  simp only [CollatzResearch.WordTrace]
  refine ⟨35954386841691269836245197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23969591227794179890830131 35954386841691269836245197)
  ·
    refine ⟨13482895065634226188591949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35954386841691269836245197 13482895065634226188591949)
    ·
      refine ⟨5056085649612834820721981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13482895065634226188591949 5056085649612834820721981)
      ·
        refine ⟨1896032118604813057770743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5056085649612834820721981 1896032118604813057770743)
        ·
          refine ⟨2844048177907219586656115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896032118604813057770743 2844048177907219586656115)
          ·
            refine ⟨4266072266860829379984173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844048177907219586656115 4266072266860829379984173)
            ·
              refine ⟨1599777100072811017494065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4266072266860829379984173 1599777100072811017494065)
              ·
                refine ⟨1199832825054608263120549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599777100072811017494065 1199832825054608263120549)
                ·
                  refine ⟨224968654697739049335103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199832825054608263120549 224968654697739049335103)
                  ·
                    rfl

theorem cell21_985781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_985781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985781 prefixEnd_985781 := by exact prefixLift 985781
  have htrace : WordTrace (prefixWord ++ tailWord_985781) baseStart_985781 baseEnd_985781 := by
    simpa [prefixWord, tailWord_985781, baseEnd_985781] using wordTrace_append hprefix tailTrace_985781
  have hstable : (prefixWord ++ tailWord_985781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985781).length < 2 ^ (prefixWord ++ tailWord_985781).sum := by decide
  have hdescent : baseEnd_985781 < baseStart_985781 := by decide
  rcases family_descends (prefixWord ++ tailWord_985781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985823 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 6]
def baseStart_985823 : Nat := 118140960795 + 985823 * 2 ^ 59
def prefixEnd_985823 : Nat := 4983230072969 + 3 ^ 40 * 985823 * 2
def baseEnd_985823 : Nat := 224978239669956309635017

theorem tailTrace_985823 : CollatzResearch.WordTrace tailWord_985823 prefixEnd_985823 224978239669956309635017 := by
  unfold tailWord_985823
  simp only [CollatzResearch.WordTrace]
  refine ⟨35955918707539111009274123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23970612471692740672849415 35955918707539111009274123)
  ·
    refine ⟨53933878061308666513911185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35955918707539111009274123 53933878061308666513911185)
    ·
      refine ⟨40450408545981499885433389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53933878061308666513911185 40450408545981499885433389)
      ·
        refine ⟨15168903204743062457037521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40450408545981499885433389 15168903204743062457037521)
        ·
          refine ⟨11376677403557296842778141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15168903204743062457037521 11376677403557296842778141)
          ·
            refine ⟨4266254026333986316041803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11376677403557296842778141 4266254026333986316041803)
            ·
              refine ⟨6399381039500979474062705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266254026333986316041803 6399381039500979474062705)
              ·
                refine ⟨4799535779625734605547029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399381039500979474062705 4799535779625734605547029)
                ·
                  refine ⟨224978239669956309635017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4799535779625734605547029 224978239669956309635017)
                  ·
                    rfl

theorem cell21_985823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_985823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985823 prefixEnd_985823 := by exact prefixLift 985823
  have htrace : WordTrace (prefixWord ++ tailWord_985823) baseStart_985823 baseEnd_985823 := by
    simpa [prefixWord, tailWord_985823, baseEnd_985823] using wordTrace_append hprefix tailTrace_985823
  have hstable : (prefixWord ++ tailWord_985823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985823).length < 2 ^ (prefixWord ++ tailWord_985823).sum := by decide
  have hdescent : baseEnd_985823 < baseStart_985823 := by decide
  rcases family_descends (prefixWord ++ tailWord_985823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985868 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_985868 : Nat := 118140960795 + 985868 * 2 ^ 59
def prefixEnd_985868 : Nat := 4983230072969 + 3 ^ 40 * 985868 * 2
def baseEnd_985868 : Nat := 224988509283046231384925

theorem tailTrace_985868 : CollatzResearch.WordTrace tailWord_985868 prefixEnd_985868 224988509283046231384925 := by
  unfold tailWord_985868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17978779996188041847331129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23971706661584055796441505 17978779996188041847331129)
  ·
    refine ⟨13484084997141031385498347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17978779996188041847331129 13484084997141031385498347)
    ·
      refine ⟨20226127495711547078247521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13484084997141031385498347 20226127495711547078247521)
      ·
        refine ⟨15169595621783660308685641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20226127495711547078247521 15169595621783660308685641)
        ·
          refine ⟨11377196716337745231514231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15169595621783660308685641 11377196716337745231514231)
          ·
            refine ⟨17065795074506617847271347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11377196716337745231514231 17065795074506617847271347)
            ·
              refine ⟨25598692611759926770907021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17065795074506617847271347 25598692611759926770907021)
              ·
                refine ⟨9599509729409972539090133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25598692611759926770907021 9599509729409972539090133)
                ·
                  refine ⟨224988509283046231384925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9599509729409972539090133 224988509283046231384925)
                  ·
                    rfl

theorem cell21_985868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_985868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985868 prefixEnd_985868 := by exact prefixLift 985868
  have htrace : WordTrace (prefixWord ++ tailWord_985868) baseStart_985868 baseEnd_985868 := by
    simpa [prefixWord, tailWord_985868, baseEnd_985868] using wordTrace_append hprefix tailTrace_985868
  have hstable : (prefixWord ++ tailWord_985868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985868).length < 2 ^ (prefixWord ++ tailWord_985868).sum := by decide
  have hdescent : baseEnd_985868 < baseStart_985868 := by decide
  rcases family_descends (prefixWord ++ tailWord_985868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985899 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 4]
def baseStart_985899 : Nat := 118140960795 + 985899 * 2 ^ 59
def prefixEnd_985899 : Nat := 4983230072969 + 3 ^ 40 * 985899 * 2
def baseEnd_985899 : Nat := 224995583905397066368195

theorem tailTrace_985899 : CollatzResearch.WordTrace tailWord_985899 prefixEnd_985899 224995583905397066368195 := by
  unfold tailWord_985899
  simp only [CollatzResearch.WordTrace]
  refine ⟨35958690655263775989040751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23972460436842517326027167 35958690655263775989040751)
  ·
    refine ⟨53938035982895663983561127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35958690655263775989040751 53938035982895663983561127)
    ·
      refine ⟨80907053974343495975341691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53938035982895663983561127 80907053974343495975341691)
      ·
        refine ⟨121360580961515243963012537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80907053974343495975341691 121360580961515243963012537)
        ·
          refine ⟨91020435721136432972259403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121360580961515243963012537 91020435721136432972259403)
          ·
            refine ⟨136530653581704649458389105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91020435721136432972259403 136530653581704649458389105)
            ·
              refine ⟨102397990186278487093791829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136530653581704649458389105 102397990186278487093791829)
              ·
                refine ⟨1199976447495451020630373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 102397990186278487093791829 1199976447495451020630373)
                ·
                  refine ⟨224995583905397066368195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199976447495451020630373 224995583905397066368195)
                  ·
                    rfl

theorem cell21_985899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_985899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985899 prefixEnd_985899 := by exact prefixLift 985899
  have htrace : WordTrace (prefixWord ++ tailWord_985899) baseStart_985899 baseEnd_985899 := by
    simpa [prefixWord, tailWord_985899, baseEnd_985899] using wordTrace_append hprefix tailTrace_985899
  have hstable : (prefixWord ++ tailWord_985899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985899).length < 2 ^ (prefixWord ++ tailWord_985899).sum := by decide
  have hdescent : baseEnd_985899 < baseStart_985899 := by decide
  rcases family_descends (prefixWord ++ tailWord_985899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985975 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 4]
def baseStart_985975 : Nat := 118140960795 + 985975 * 2 ^ 59
def prefixEnd_985975 : Nat := 4983230072969 + 3 ^ 40 * 985975 * 2
def baseEnd_985975 : Nat := 225012928140837823101373

theorem tailTrace_985975 : CollatzResearch.WordTrace tailWord_985975 prefixEnd_985975 225012928140837823101373 := by
  unfold tailWord_985975
  simp only [CollatzResearch.WordTrace]
  refine ⟨35961462602988440968807379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23974308401992293979204919 35961462602988440968807379)
  ·
    refine ⟨53942193904482661453211069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35961462602988440968807379 53942193904482661453211069)
    ·
      refine ⟨20228322714180998044954151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53942193904482661453211069 20228322714180998044954151)
      ·
        refine ⟨30342484071271497067431227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20228322714180998044954151 30342484071271497067431227)
        ·
          refine ⟨45513726106907245601146841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30342484071271497067431227 45513726106907245601146841)
          ·
            refine ⟨34135294580180434200860131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45513726106907245601146841 34135294580180434200860131)
            ·
              refine ⟨51202941870270651301290197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34135294580180434200860131 51202941870270651301290197)
              ·
                refine ⟨1200068950084468389873989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51202941870270651301290197 1200068950084468389873989)
                ·
                  refine ⟨225012928140837823101373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200068950084468389873989 225012928140837823101373)
                  ·
                    rfl

theorem cell21_985975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_985975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_985975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_985975 prefixEnd_985975 := by exact prefixLift 985975
  have htrace : WordTrace (prefixWord ++ tailWord_985975) baseStart_985975 baseEnd_985975 := by
    simpa [prefixWord, tailWord_985975, baseEnd_985975] using wordTrace_append hprefix tailTrace_985975
  have hstable : (prefixWord ++ tailWord_985975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985975).length < 2 ^ (prefixWord ++ tailWord_985975).sum := by decide
  have hdescent : baseEnd_985975 < baseStart_985975 := by decide
  rcases family_descends (prefixWord ++ tailWord_985975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986012 : List Nat := [2, 2, 3, 3, 2, 1, 3, 2, 3]
def baseStart_986012 : Nat := 118140960795 + 986012 * 2 ^ 59
def prefixEnd_986012 : Nat := 4983230072969 + 3 ^ 40 * 986012 * 2
def baseEnd_986012 : Nat := 225021372044933980984631

theorem tailTrace_986012 : CollatzResearch.WordTrace tailWord_986012 prefixEnd_986012 225021372044933980984631 := by
  unfold tailWord_986012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17981406051927198143952145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23975208069236264191936193 17981406051927198143952145)
  ·
    refine ⟨13486054538945398607964109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17981406051927198143952145 13486054538945398607964109)
    ·
      refine ⟨5057270452104524477986541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13486054538945398607964109 5057270452104524477986541)
      ·
        refine ⟨1896476419539196679244953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5057270452104524477986541 1896476419539196679244953)
        ·
          refine ⟨1422357314654397509433715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1896476419539196679244953 1422357314654397509433715)
          ·
            refine ⟨2133535971981596264150573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422357314654397509433715 2133535971981596264150573)
            ·
              refine ⟨800075989493098599056465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2133535971981596264150573 800075989493098599056465)
              ·
                refine ⟨600056992119823949292349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800075989493098599056465 600056992119823949292349)
                ·
                  refine ⟨225021372044933980984631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600056992119823949292349 225021372044933980984631)
                  ·
                    rfl

theorem cell21_986012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_986012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986012 prefixEnd_986012 := by exact prefixLift 986012
  have htrace : WordTrace (prefixWord ++ tailWord_986012) baseStart_986012 baseEnd_986012 := by
    simpa [prefixWord, tailWord_986012, baseEnd_986012] using wordTrace_append hprefix tailTrace_986012
  have hstable : (prefixWord ++ tailWord_986012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986012).length < 2 ^ (prefixWord ++ tailWord_986012).sum := by decide
  have hdescent : baseEnd_986012 < baseStart_986012 := by decide
  rcases family_descends (prefixWord ++ tailWord_986012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986023 : List Nat := [1, 1, 6, 1, 3, 1, 2, 6]
def baseStart_986023 : Nat := 118140960795 + 986023 * 2 ^ 59
def prefixEnd_986023 : Nat := 4983230072969 + 3 ^ 40 * 986023 * 2
def baseEnd_986023 : Nat := 75007960798266802100425

theorem tailTrace_986023 : CollatzResearch.WordTrace tailWord_986023 prefixEnd_986023 75007960798266802100425 := by
  unfold tailWord_986023
  simp only [CollatzResearch.WordTrace]
  refine ⟨35963213306814545166554723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23975475537876363444369815 35963213306814545166554723)
  ·
    refine ⟨53944819960221817749832085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35963213306814545166554723 53944819960221817749832085)
    ·
      refine ⟨2528663435635397707023379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53944819960221817749832085 2528663435635397707023379)
      ·
        refine ⟨3792995153453096560535069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528663435635397707023379 3792995153453096560535069)
        ·
          refine ⟨1422373182544911210200651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3792995153453096560535069 1422373182544911210200651)
          ·
            refine ⟨2133559773817366815300977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422373182544911210200651 2133559773817366815300977)
            ·
              refine ⟨1600169830363025111475733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133559773817366815300977 1600169830363025111475733)
              ·
                refine ⟨75007960798266802100425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1600169830363025111475733 75007960798266802100425)
                ·
                  rfl

theorem cell21_986023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 6].length) (baseStart_986023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986023 prefixEnd_986023 := by exact prefixLift 986023
  have htrace : WordTrace (prefixWord ++ tailWord_986023) baseStart_986023 baseEnd_986023 := by
    simpa [prefixWord, tailWord_986023, baseEnd_986023] using wordTrace_append hprefix tailTrace_986023
  have hstable : (prefixWord ++ tailWord_986023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986023).length < 2 ^ (prefixWord ++ tailWord_986023).sum := by decide
  have hdescent : baseEnd_986023 < baseStart_986023 := by decide
  rcases family_descends (prefixWord ++ tailWord_986023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986068 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_986068 : Nat := 118140960795 + 986068 * 2 ^ 59
def prefixEnd_986068 : Nat := 4983230072969 + 3 ^ 40 * 986068 * 2
def baseEnd_986068 : Nat := 225034152007890328051183

theorem tailTrace_986068 : CollatzResearch.WordTrace tailWord_986068 prefixEnd_986068 225034152007890328051183 := by
  unfold tailWord_986068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17982427295825758925971429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23976569727767678567961905 17982427295825758925971429)
  ·
    refine ⟨3371705117967329798619643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17982427295825758925971429 3371705117967329798619643)
    ·
      refine ⟨5057557676950994697929465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371705117967329798619643 5057557676950994697929465)
      ·
        refine ⟨3793168257713246023447099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057557676950994697929465 3793168257713246023447099)
        ·
          refine ⟨5689752386569869035170649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793168257713246023447099 5689752386569869035170649)
          ·
            refine ⟨4267314289927401776377987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5689752386569869035170649 4267314289927401776377987)
            ·
              refine ⟨6400971434891102664566981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267314289927401776377987 6400971434891102664566981)
              ·
                refine ⟨1200182144042081749606309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6400971434891102664566981 1200182144042081749606309)
                ·
                  refine ⟨225034152007890328051183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200182144042081749606309 225034152007890328051183)
                  ·
                    rfl

theorem cell21_986068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_986068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986068 prefixEnd_986068 := by exact prefixLift 986068
  have htrace : WordTrace (prefixWord ++ tailWord_986068) baseStart_986068 baseEnd_986068 := by
    simpa [prefixWord, tailWord_986068, baseEnd_986068] using wordTrace_append hprefix tailTrace_986068
  have hstable : (prefixWord ++ tailWord_986068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986068).length < 2 ^ (prefixWord ++ tailWord_986068).sum := by decide
  have hdescent : baseEnd_986068 < baseStart_986068 := by decide
  rcases family_descends (prefixWord ++ tailWord_986068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986158 : List Nat := [4, 1, 3, 1, 1, 1, 3, 7]
def baseStart_986158 : Nat := 118140960795 + 986158 * 2 ^ 59
def prefixEnd_986158 : Nat := 4983230072969 + 3 ^ 40 * 986158 * 2
def baseEnd_986158 : Nat := 75018230411356723850333

theorem tailTrace_986158 : CollatzResearch.WordTrace tailWord_986158 prefixEnd_986158 75018230411356723850333 := by
  unfold tailWord_986158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4496017145165682902839891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23978758107550308815146085 4496017145165682902839891)
  ·
    refine ⟨6744025717748524354259837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4496017145165682902839891 6744025717748524354259837)
    ·
      refine ⟨2529009644155696632847439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6744025717748524354259837 2529009644155696632847439)
      ·
        refine ⟨3793514466233544949271159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2529009644155696632847439 3793514466233544949271159)
        ·
          refine ⟨5690271699350317423906739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793514466233544949271159 5690271699350317423906739)
          ·
            refine ⟨8535407549025476135860109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690271699350317423906739 8535407549025476135860109)
            ·
              refine ⟨3200777830884553550947541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8535407549025476135860109 3200777830884553550947541)
              ·
                refine ⟨75018230411356723850333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3200777830884553550947541 75018230411356723850333)
                ·
                  rfl

theorem cell21_986158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_986158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986158 prefixEnd_986158 := by exact prefixLift 986158
  have htrace : WordTrace (prefixWord ++ tailWord_986158) baseStart_986158 baseEnd_986158 := by
    simpa [prefixWord, tailWord_986158, baseEnd_986158] using wordTrace_append hprefix tailTrace_986158
  have hstable : (prefixWord ++ tailWord_986158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986158).length < 2 ^ (prefixWord ++ tailWord_986158).sum := by decide
  have hdescent : baseEnd_986158 < baseStart_986158 := by decide
  rcases family_descends (prefixWord ++ tailWord_986158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986164 : List Nat := [2, 5, 1, 2, 1, 3, 1, 3, 3]
def baseStart_986164 : Nat := 118140960795 + 986164 * 2 ^ 59
def prefixEnd_986164 : Nat := 4983230072969 + 3 ^ 40 * 986164 * 2
def baseEnd_986164 : Nat := 225056060515815494450987

theorem tailTrace_986164 : CollatzResearch.WordTrace tailWord_986164 prefixEnd_986164 225056060515815494450987 := by
  unfold tailWord_986164
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984177999651863123718773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23978903999535817498291697 17984177999651863123718773)
  ·
    refine ⟨1686016687467362167848635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17984177999651863123718773 1686016687467362167848635)
    ·
      refine ⟨2529025031201043251772953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686016687467362167848635 2529025031201043251772953)
      ·
        refine ⟨1896768773400782438829715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529025031201043251772953 1896768773400782438829715)
        ·
          refine ⟨2845153160101173658244573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896768773400782438829715 2845153160101173658244573)
          ·
            refine ⟨1066932435037940121841715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2845153160101173658244573 1066932435037940121841715)
            ·
              refine ⟨1600398652556910182762573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066932435037940121841715 1600398652556910182762573)
              ·
                refine ⟨600149494708841318535965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1600398652556910182762573 600149494708841318535965)
                ·
                  refine ⟨225056060515815494450987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600149494708841318535965 225056060515815494450987)
                  ·
                    rfl

theorem cell21_986164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_986164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986164 prefixEnd_986164 := by exact prefixLift 986164
  have htrace : WordTrace (prefixWord ++ tailWord_986164) baseStart_986164 baseEnd_986164 := by
    simpa [prefixWord, tailWord_986164, baseEnd_986164] using wordTrace_append hprefix tailTrace_986164
  have hstable : (prefixWord ++ tailWord_986164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986164).length < 2 ^ (prefixWord ++ tailWord_986164).sum := by decide
  have hdescent : baseEnd_986164 < baseStart_986164 := by decide
  rcases family_descends (prefixWord ++ tailWord_986164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986217 : List Nat := [1, 2, 1, 1, 1, 6, 2, 7]
def baseStart_986217 : Nat := 118140960795 + 986217 * 2 ^ 59
def prefixEnd_986217 : Nat := 4983230072969 + 3 ^ 40 * 986217 * 2
def baseEnd_986217 : Nat := 75022718612633060022515

theorem tailTrace_986217 : CollatzResearch.WordTrace tailWord_986217 prefixEnd_986217 75022718612633060022515 := by
  unfold tailWord_986217
  simp only [CollatzResearch.WordTrace]
  refine ⟨35970289068111716299116905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23980192712074477532744603 35970289068111716299116905)
  ·
    refine ⟨26977716801083787224337679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35970289068111716299116905 26977716801083787224337679)
    ·
      refine ⟨40466575201625680836506519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26977716801083787224337679 40466575201625680836506519)
      ·
        refine ⟨60699862802438521254759779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40466575201625680836506519 60699862802438521254759779)
        ·
          refine ⟨91049794203657781882139669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60699862802438521254759779 91049794203657781882139669)
          ·
            refine ⟨4267959103296458525725297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91049794203657781882139669 4267959103296458525725297)
            ·
              refine ⟨3200969327472343894293973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4267959103296458525725297 3200969327472343894293973)
              ·
                refine ⟨75022718612633060022515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3200969327472343894293973 75022718612633060022515)
                ·
                  rfl

theorem cell21_986217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 7].length) (baseStart_986217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986217 prefixEnd_986217 := by exact prefixLift 986217
  have htrace : WordTrace (prefixWord ++ tailWord_986217) baseStart_986217 baseEnd_986217 := by
    simpa [prefixWord, tailWord_986217, baseEnd_986217] using wordTrace_append hprefix tailTrace_986217
  have hstable : (prefixWord ++ tailWord_986217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986217).length < 2 ^ (prefixWord ++ tailWord_986217).sum := by decide
  have hdescent : baseEnd_986217 < baseStart_986217 := by decide
  rcases family_descends (prefixWord ++ tailWord_986217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986369 : List Nat := [1, 2, 4, 1, 1, 3, 1, 8]
def baseStart_986369 : Nat := 118140960795 + 986369 * 2 ^ 59
def prefixEnd_986369 : Nat := 4983230072969 + 3 ^ 40 * 986369 * 2
def baseEnd_986369 : Nat := 75034281436260231177967

theorem tailTrace_986369 : CollatzResearch.WordTrace tailWord_986369 prefixEnd_986369 75034281436260231177967 := by
  unfold tailWord_986369
  simp only [CollatzResearch.WordTrace]
  refine ⟨35975832963561046258650161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23983888642374030839100107 35975832963561046258650161)
  ·
    refine ⟨26981874722670784693987621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35975832963561046258650161 26981874722670784693987621)
    ·
      refine ⟨5059101510500772130122679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26981874722670784693987621 5059101510500772130122679)
      ·
        refine ⟨7588652265751158195184019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059101510500772130122679 7588652265751158195184019)
        ·
          refine ⟨11382978398626737292776029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588652265751158195184019 11382978398626737292776029)
          ·
            refine ⟨4268616899485026484791011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11382978398626737292776029 4268616899485026484791011)
            ·
              refine ⟨6402925349227539727186517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268616899485026484791011 6402925349227539727186517)
              ·
                refine ⟨75034281436260231177967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6402925349227539727186517 75034281436260231177967)
                ·
                  rfl

theorem cell21_986369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 8].length) (baseStart_986369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986369 prefixEnd_986369 := by exact prefixLift 986369
  have htrace : WordTrace (prefixWord ++ tailWord_986369) baseStart_986369 baseEnd_986369 := by
    simpa [prefixWord, tailWord_986369, baseEnd_986369] using wordTrace_append hprefix tailTrace_986369
  have hstable : (prefixWord ++ tailWord_986369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986369).length < 2 ^ (prefixWord ++ tailWord_986369).sum := by decide
  have hdescent : baseEnd_986369 < baseStart_986369 := by decide
  rcases family_descends (prefixWord ++ tailWord_986369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986372 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_986372 : Nat := 118140960795 + 986372 * 2 ^ 59
def prefixEnd_986372 : Nat := 4983230072969 + 3 ^ 40 * 986372 * 2
def baseEnd_986372 : Nat := 225103528949653354983895

theorem tailTrace_986372 : CollatzResearch.WordTrace tailWord_986372 prefixEnd_986372 225103528949653354983895 := by
  unfold tailWord_986372
  simp only [CollatzResearch.WordTrace]
  refine ⟨17987971191275088885504685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23983961588366785180672913 17987971191275088885504685)
  ·
    refine ⟨6745489196728158332064257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17987971191275088885504685 6745489196728158332064257)
    ·
      refine ⟨5059116897546118749048193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6745489196728158332064257 5059116897546118749048193)
      ·
        refine ⟨3794337673159589061786145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5059116897546118749048193 3794337673159589061786145)
        ·
          refine ⟨2845753254869691796339609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3794337673159589061786145 2845753254869691796339609)
          ·
            refine ⟨2134314941152268847254707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845753254869691796339609 2134314941152268847254707)
            ·
              refine ⟨3201472411728403270882061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134314941152268847254707 3201472411728403270882061)
              ·
                refine ⟨1200552154398151226580773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201472411728403270882061 1200552154398151226580773)
                ·
                  refine ⟨225103528949653354983895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200552154398151226580773 225103528949653354983895)
                  ·
                    rfl

theorem cell21_986372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_986372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986372 prefixEnd_986372 := by exact prefixLift 986372
  have htrace : WordTrace (prefixWord ++ tailWord_986372) baseStart_986372 baseEnd_986372 := by
    simpa [prefixWord, tailWord_986372, baseEnd_986372] using wordTrace_append hprefix tailTrace_986372
  have hstable : (prefixWord ++ tailWord_986372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986372).length < 2 ^ (prefixWord ++ tailWord_986372).sum := by decide
  have hdescent : baseEnd_986372 < baseStart_986372 := by decide
  rcases family_descends (prefixWord ++ tailWord_986372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986431 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 4]
def baseStart_986431 : Nat := 118140960795 + 986431 * 2 ^ 59
def prefixEnd_986431 : Nat := 4983230072969 + 3 ^ 40 * 986431 * 2
def baseEnd_986431 : Nat := 225116993553482363500441

theorem tailTrace_986431 : CollatzResearch.WordTrace tailWord_986431 prefixEnd_986431 225116993553482363500441 := by
  unfold tailWord_986431
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978094289336430847407147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23985396192890953898271431 35978094289336430847407147)
  ·
    refine ⟨53967141434004646271110721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35978094289336430847407147 53967141434004646271110721)
    ·
      refine ⟨40475356075503484703333041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53967141434004646271110721 40475356075503484703333041)
      ·
        refine ⟨30356517056627613527499781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40475356075503484703333041 30356517056627613527499781)
        ·
          refine ⟨5691846948117677536406209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30356517056627613527499781 5691846948117677536406209)
          ·
            refine ⟨4268885211088258152304657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5691846948117677536406209 4268885211088258152304657)
            ·
              refine ⟨3201663908316193614228493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4268885211088258152304657 3201663908316193614228493)
              ·
                refine ⟨1200623965618572605335685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201663908316193614228493 1200623965618572605335685)
                ·
                  refine ⟨225116993553482363500441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200623965618572605335685 225116993553482363500441)
                  ·
                    rfl

theorem cell21_986431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_986431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986431 prefixEnd_986431 := by exact prefixLift 986431
  have htrace : WordTrace (prefixWord ++ tailWord_986431) baseStart_986431 baseEnd_986431 := by
    simpa [prefixWord, tailWord_986431, baseEnd_986431] using wordTrace_append hprefix tailTrace_986431
  have hstable : (prefixWord ++ tailWord_986431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986431).length < 2 ^ (prefixWord ++ tailWord_986431).sum := by decide
  have hdescent : baseEnd_986431 < baseStart_986431 := by decide
  rcases family_descends (prefixWord ++ tailWord_986431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986476 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_986476 : Nat := 118140960795 + 986476 * 2 ^ 59
def prefixEnd_986476 : Nat := 4983230072969 + 3 ^ 40 * 986476 * 2
def baseEnd_986476 : Nat := 225127263166572285250349

theorem tailTrace_986476 : CollatzResearch.WordTrace tailWord_986476 prefixEnd_986476 225127263166572285250349 := by
  unfold tailWord_986476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989867787086701766397641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23986490382782269021863521 17989867787086701766397641)
  ·
    refine ⟨13492400840315026324798231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17989867787086701766397641 13492400840315026324798231)
    ·
      refine ⟨20238601260472539487197347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13492400840315026324798231 20238601260472539487197347)
      ·
        refine ⟨30357901890708809230796021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20238601260472539487197347 30357901890708809230796021)
        ·
          refine ⟨2846053302253950865387127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30357901890708809230796021 2846053302253950865387127)
          ·
            refine ⟨4269079953380926298080691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846053302253950865387127 4269079953380926298080691)
            ·
              refine ⟨6403619930071389447121037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269079953380926298080691 6403619930071389447121037)
              ·
                refine ⟨2401357473776771042670389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6403619930071389447121037 2401357473776771042670389)
                ·
                  refine ⟨225127263166572285250349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2401357473776771042670389 225127263166572285250349)
                  ·
                    rfl

theorem cell21_986476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_986476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986476 prefixEnd_986476 := by exact prefixLift 986476
  have htrace : WordTrace (prefixWord ++ tailWord_986476) baseStart_986476 baseEnd_986476 := by
    simpa [prefixWord, tailWord_986476, baseEnd_986476] using wordTrace_append hprefix tailTrace_986476
  have hstable : (prefixWord ++ tailWord_986476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986476).length < 2 ^ (prefixWord ++ tailWord_986476).sum := by decide
  have hdescent : baseEnd_986476 < baseStart_986476 := by decide
  rcases family_descends (prefixWord ++ tailWord_986476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986521 : List Nat := [1, 2, 1, 2, 1, 7, 7]
def baseStart_986521 : Nat := 118140960795 + 986521 * 2 ^ 59
def prefixEnd_986521 : Nat := 4983230072969 + 3 ^ 40 * 986521 * 2
def baseEnd_986521 : Nat := 25015281419962467444473

theorem tailTrace_986521 : CollatzResearch.WordTrace tailWord_986521 prefixEnd_986521 25015281419962467444473 := by
  unfold tailWord_986521
  simp only [CollatzResearch.WordTrace]
  refine ⟨35981376859010376218183417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23987584572673584145455611 35981376859010376218183417)
  ·
    refine ⟨26986032644257782163637563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35981376859010376218183417 26986032644257782163637563)
    ·
      refine ⟨40479048966386673245456345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26986032644257782163637563 40479048966386673245456345)
      ·
        refine ⟨30359286724790004934092259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40479048966386673245456345 30359286724790004934092259)
        ·
          refine ⟨45538930087185007401138389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30359286724790004934092259 45538930087185007401138389)
          ·
            refine ⟨1067318673918398610964181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45538930087185007401138389 1067318673918398610964181)
            ·
              refine ⟨25015281419962467444473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1067318673918398610964181 25015281419962467444473)
              ·
                rfl

theorem cell21_986521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 7].length) (baseStart_986521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986521 prefixEnd_986521 := by exact prefixLift 986521
  have htrace : WordTrace (prefixWord ++ tailWord_986521) baseStart_986521 baseEnd_986521 := by
    simpa [prefixWord, tailWord_986521, baseEnd_986521] using wordTrace_append hprefix tailTrace_986521
  have hstable : (prefixWord ++ tailWord_986521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986521).length < 2 ^ (prefixWord ++ tailWord_986521).sum := by decide
  have hdescent : baseEnd_986521 < baseStart_986521 := by decide
  rcases family_descends (prefixWord ++ tailWord_986521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986541 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 4]
def baseStart_986541 : Nat := 118140960795 + 986541 * 2 ^ 59
def prefixEnd_986541 : Nat := 4983230072969 + 3 ^ 40 * 986541 * 2
def baseEnd_986541 : Nat := 225142097052146616666883

theorem tailTrace_986541 : CollatzResearch.WordTrace tailWord_986541 prefixEnd_986541 225142097052146616666883 := by
  unfold tailWord_986541
  simp only [CollatzResearch.WordTrace]
  refine ⟨35982106318937919633911477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23988070879291946422607651 35982106318937919633911477)
  ·
    refine ⟨3373322467400429965679201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35982106318937919633911477 3373322467400429965679201)
    ·
      refine ⟨2529991850550322474259401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3373322467400429965679201 2529991850550322474259401)
      ·
        refine ⟨1897493887912741855694551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529991850550322474259401 1897493887912741855694551)
        ·
          refine ⟨2846240831869112783541827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897493887912741855694551 2846240831869112783541827)
          ·
            refine ⟨4269361247803669175312741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846240831869112783541827 4269361247803669175312741)
            ·
              refine ⟨800505233963187970371139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4269361247803669175312741 800505233963187970371139)
              ·
                refine ⟨1200757850944781955556709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800505233963187970371139 1200757850944781955556709)
                ·
                  refine ⟨225142097052146616666883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200757850944781955556709 225142097052146616666883)
                  ·
                    rfl

theorem cell21_986541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_986541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986541 prefixEnd_986541 := by exact prefixLift 986541
  have htrace : WordTrace (prefixWord ++ tailWord_986541) baseStart_986541 baseEnd_986541 := by
    simpa [prefixWord, tailWord_986541, baseEnd_986541] using wordTrace_append hprefix tailTrace_986541
  have hstable : (prefixWord ++ tailWord_986541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986541).length < 2 ^ (prefixWord ++ tailWord_986541).sum := by decide
  have hdescent : baseEnd_986541 < baseStart_986541 := by decide
  rcases family_descends (prefixWord ++ tailWord_986541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986586 : List Nat := [3, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_986586 : Nat := 118140960795 + 986586 * 2 ^ 59
def prefixEnd_986586 : Nat := 4983230072969 + 3 ^ 40 * 986586 * 2
def baseEnd_986586 : Nat := 225152366665236538416791

theorem tailTrace_986586 : CollatzResearch.WordTrace tailWord_986586 prefixEnd_986586 225152366665236538416791 := by
  unfold tailWord_986586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995936900943723079824903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23989165069183261546199741 8995936900943723079824903)
  ·
    refine ⟨13493905351415584619737355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8995936900943723079824903 13493905351415584619737355)
    ·
      refine ⟨20240858027123376929606033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13493905351415584619737355 20240858027123376929606033)
      ·
        refine ⟨15180643520342532697204525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20240858027123376929606033 15180643520342532697204525)
        ·
          refine ⟨5692741320128449761451697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15180643520342532697204525 5692741320128449761451697)
          ·
            refine ⟨4269555990096337321088773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5692741320128449761451697 4269555990096337321088773)
            ·
              refine ⟨800541748143063247704145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4269555990096337321088773 800541748143063247704145)
              ·
                refine ⟨600406311107297435778109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800541748143063247704145 600406311107297435778109)
                ·
                  refine ⟨225152366665236538416791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600406311107297435778109 225152366665236538416791)
                  ·
                    rfl

theorem cell21_986586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_986586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986586 prefixEnd_986586 := by exact prefixLift 986586
  have htrace : WordTrace (prefixWord ++ tailWord_986586) baseStart_986586 baseEnd_986586 := by
    simpa [prefixWord, tailWord_986586, baseEnd_986586] using wordTrace_append hprefix tailTrace_986586
  have hstable : (prefixWord ++ tailWord_986586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986586).length < 2 ^ (prefixWord ++ tailWord_986586).sum := by decide
  have hdescent : baseEnd_986586 < baseStart_986586 := by decide
  rcases family_descends (prefixWord ++ tailWord_986586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986645 : List Nat := [1, 3, 2, 1, 3, 2, 2, 4, 3]
def baseStart_986645 : Nat := 118140960795 + 986645 * 2 ^ 59
def prefixEnd_986645 : Nat := 4983230072969 + 3 ^ 40 * 986645 * 2
def baseEnd_986645 : Nat := 225165831269065546933337

theorem tailTrace_986645 : CollatzResearch.WordTrace tailWord_986645 prefixEnd_986645 225165831269065546933337 := by
  unfold tailWord_986645
  simp only [CollatzResearch.WordTrace]
  refine ⟨35985899510561145395697389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23990599673707430263798259 35985899510561145395697389)
  ·
    refine ⟨13494712316460429523386521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35985899510561145395697389 13494712316460429523386521)
    ·
      refine ⟨10121034237345322142539891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13494712316460429523386521 10121034237345322142539891)
      ·
        refine ⟨15181551356017983213809837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10121034237345322142539891 15181551356017983213809837)
        ·
          refine ⟨5693081758506743705178689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15181551356017983213809837 5693081758506743705178689)
          ·
            refine ⟨4269811318880057778884017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5693081758506743705178689 4269811318880057778884017)
            ·
              refine ⟨3202358489160043334163013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269811318880057778884017 3202358489160043334163013)
              ·
                refine ⟨600442216717508125155565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3202358489160043334163013 600442216717508125155565)
                ·
                  refine ⟨225165831269065546933337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600442216717508125155565 225165831269065546933337)
                  ·
                    rfl

theorem cell21_986645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_986645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986645 prefixEnd_986645 := by exact prefixLift 986645
  have htrace : WordTrace (prefixWord ++ tailWord_986645) baseStart_986645 baseEnd_986645 := by
    simpa [prefixWord, tailWord_986645, baseEnd_986645] using wordTrace_append hprefix tailTrace_986645
  have hstable : (prefixWord ++ tailWord_986645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986645).length < 2 ^ (prefixWord ++ tailWord_986645).sum := by decide
  have hdescent : baseEnd_986645 < baseStart_986645 := by decide
  rcases family_descends (prefixWord ++ tailWord_986645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986710 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_986710 : Nat := 118140960795 + 986710 * 2 ^ 59
def prefixEnd_986710 : Nat := 4983230072969 + 3 ^ 40 * 986710 * 2
def baseEnd_986710 : Nat := 225180665154639878349871

theorem tailTrace_986710 : CollatzResearch.WordTrace tailWord_986710 prefixEnd_986710 225180665154639878349871 := by
  unfold tailWord_986710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249266890957853843550849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23992180170217107664542389 2249266890957853843550849)
  ·
    refine ⟨1686950168218390382663137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2249266890957853843550849 1686950168218390382663137)
    ·
      refine ⟨1265212626163792786997353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1686950168218390382663137 1265212626163792786997353)
      ·
        refine ⟨948909469622844590248015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1265212626163792786997353 948909469622844590248015)
        ·
          refine ⟨1423364204434266885372023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948909469622844590248015 1423364204434266885372023)
          ·
            refine ⟨2135046306651400328058035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423364204434266885372023 2135046306651400328058035)
            ·
              refine ⟨3202569459977100492087053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135046306651400328058035 3202569459977100492087053)
              ·
                refine ⟨1200963547491412684532645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3202569459977100492087053 1200963547491412684532645)
                ·
                  refine ⟨225180665154639878349871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200963547491412684532645 225180665154639878349871)
                  ·
                    rfl

theorem cell21_986710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_986710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986710 prefixEnd_986710 := by exact prefixLift 986710
  have htrace : WordTrace (prefixWord ++ tailWord_986710) baseStart_986710 baseEnd_986710 := by
    simpa [prefixWord, tailWord_986710, baseEnd_986710] using wordTrace_append hprefix tailTrace_986710
  have hstable : (prefixWord ++ tailWord_986710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986710).length < 2 ^ (prefixWord ++ tailWord_986710).sum := by decide
  have hdescent : baseEnd_986710 < baseStart_986710 := by decide
  rcases family_descends (prefixWord ++ tailWord_986710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986763 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 5]
def baseStart_986763 : Nat := 118140960795 + 986763 * 2 ^ 59
def prefixEnd_986763 : Nat := 4983230072969 + 3 ^ 40 * 986763 * 2
def baseEnd_986763 : Nat := 225192760476723563966429

theorem tailTrace_986763 : CollatzResearch.WordTrace tailWord_986763 prefixEnd_986763 225192760476723563966429 := by
  unfold tailWord_986763
  simp only [CollatzResearch.WordTrace]
  refine ⟨35990203324133651548492943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23993468882755767698995295 35990203324133651548492943)
  ·
    refine ⟨53985304986200477322739415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35990203324133651548492943 53985304986200477322739415)
    ·
      refine ⟨80977957479300715984109123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53985304986200477322739415 80977957479300715984109123)
      ·
        refine ⟨121466936218951073976163685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80977957479300715984109123 121466936218951073976163685)
        ·
          refine ⟨22775050541053326370530691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121466936218951073976163685 22775050541053326370530691)
          ·
            refine ⟨34162575811579989555796037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22775050541053326370530691 34162575811579989555796037)
            ·
              refine ⟨6405482964671248041711757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34162575811579989555796037 6405482964671248041711757)
              ·
                refine ⟨2402056111751718015641909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6405482964671248041711757 2402056111751718015641909)
                ·
                  refine ⟨225192760476723563966429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402056111751718015641909 225192760476723563966429)
                  ·
                    rfl

theorem cell21_986763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_986763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986763 prefixEnd_986763 := by exact prefixLift 986763
  have htrace : WordTrace (prefixWord ++ tailWord_986763) baseStart_986763 baseEnd_986763 := by
    simpa [prefixWord, tailWord_986763, baseEnd_986763] using wordTrace_append hprefix tailTrace_986763
  have hstable : (prefixWord ++ tailWord_986763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986763).length < 2 ^ (prefixWord ++ tailWord_986763).sum := by decide
  have hdescent : baseEnd_986763 < baseStart_986763 := by decide
  rcases family_descends (prefixWord ++ tailWord_986763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986766 : List Nat := [4, 1, 1, 3, 1, 4, 1, 6]
def baseStart_986766 : Nat := 118140960795 + 986766 * 2 ^ 59
def prefixEnd_986766 : Nat := 4983230072969 + 3 ^ 40 * 986766 * 2
def baseEnd_986766 : Nat := 75064481705865408472141

theorem tailTrace_986766 : CollatzResearch.WordTrace tailWord_986766 prefixEnd_986766 75064481705865408472141 := by
  unfold tailWord_986766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498789092890347882606519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23993541828748522040568101 4498789092890347882606519)
  ·
    refine ⟨6748183639335521823909779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4498789092890347882606519 6748183639335521823909779)
    ·
      refine ⟨10122275459003282735864669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748183639335521823909779 10122275459003282735864669)
      ·
        refine ⟨3795853297126231025949251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10122275459003282735864669 3795853297126231025949251)
        ·
          refine ⟨5693779945689346538923877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795853297126231025949251 5693779945689346538923877)
          ·
            refine ⟨1067583739816752476048227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5693779945689346538923877 1067583739816752476048227)
            ·
              refine ⟨1601375609725128714072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067583739816752476048227 1601375609725128714072341)
              ·
                refine ⟨75064481705865408472141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1601375609725128714072341 75064481705865408472141)
                ·
                  rfl

theorem cell21_986766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_986766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986766 prefixEnd_986766 := by exact prefixLift 986766
  have htrace : WordTrace (prefixWord ++ tailWord_986766) baseStart_986766 baseEnd_986766 := by
    simpa [prefixWord, tailWord_986766, baseEnd_986766] using wordTrace_append hprefix tailTrace_986766
  have hstable : (prefixWord ++ tailWord_986766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986766).length < 2 ^ (prefixWord ++ tailWord_986766).sum := by decide
  have hdescent : baseEnd_986766 < baseStart_986766 := by decide
  rcases family_descends (prefixWord ++ tailWord_986766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986783 : List Nat := [1, 1, 2, 7, 1, 1, 3, 5]
def baseStart_986783 : Nat := 118140960795 + 986783 * 2 ^ 59
def prefixEnd_986783 : Nat := 4983230072969 + 3 ^ 40 * 986783 * 2
def baseEnd_986783 : Nat := 75065774916402657877685

theorem tailTrace_986783 : CollatzResearch.WordTrace tailWord_986783 prefixEnd_986783 75065774916402657877685 := by
  unfold tailWord_986783
  simp only [CollatzResearch.WordTrace]
  refine ⟨35990932784061194964221003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23993955189374129976147335 35990932784061194964221003)
  ·
    refine ⟨53986399176091792446331505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35990932784061194964221003 53986399176091792446331505)
    ·
      refine ⟨40489799382068844334748629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53986399176091792446331505 40489799382068844334748629)
      ·
        refine ⟨948979673017238539095671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 40489799382068844334748629 948979673017238539095671)
        ·
          refine ⟨1423469509525857808643507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948979673017238539095671 1423469509525857808643507)
          ·
            refine ⟨2135204264288786712965261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423469509525857808643507 2135204264288786712965261)
            ·
              refine ⟨800701599108295017361973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2135204264288786712965261 800701599108295017361973)
              ·
                refine ⟨75065774916402657877685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 800701599108295017361973 75065774916402657877685)
                ·
                  rfl

theorem cell21_986783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 5].length) (baseStart_986783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986783 prefixEnd_986783 := by exact prefixLift 986783
  have htrace : WordTrace (prefixWord ++ tailWord_986783) baseStart_986783 baseEnd_986783 := by
    simpa [prefixWord, tailWord_986783, baseEnd_986783] using wordTrace_append hprefix tailTrace_986783
  have hstable : (prefixWord ++ tailWord_986783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986783).length < 2 ^ (prefixWord ++ tailWord_986783).sum := by decide
  have hdescent : baseEnd_986783 < baseStart_986783 := by decide
  rcases family_descends (prefixWord ++ tailWord_986783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986839 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 5]
def baseStart_986839 : Nat := 118140960795 + 986839 * 2 ^ 59
def prefixEnd_986839 : Nat := 4983230072969 + 3 ^ 40 * 986839 * 2
def baseEnd_986839 : Nat := 225210104712164320699607

theorem tailTrace_986839 : CollatzResearch.WordTrace tailWord_986839 prefixEnd_986839 225210104712164320699607 := by
  unfold tailWord_986839
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992975271858316528259571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23995316847905544352173047 35992975271858316528259571)
  ·
    refine ⟨53989462907787474792389357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35992975271858316528259571 53989462907787474792389357)
    ·
      refine ⟨20246048590420303047146009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53989462907787474792389357 20246048590420303047146009)
      ·
        refine ⟨15184536442815227285359507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20246048590420303047146009 15184536442815227285359507)
        ·
          refine ⟨22776804664222840928039261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15184536442815227285359507 22776804664222840928039261)
          ·
            refine ⟨8541301749083565348014723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22776804664222840928039261 8541301749083565348014723)
            ·
              refine ⟨12811952623625348022022085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541301749083565348014723 12811952623625348022022085)
              ·
                refine ⟨2402241116929752754129141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12811952623625348022022085 2402241116929752754129141)
                ·
                  refine ⟨225210104712164320699607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402241116929752754129141 225210104712164320699607)
                  ·
                    rfl

theorem cell21_986839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_986839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986839 prefixEnd_986839 := by exact prefixLift 986839
  have htrace : WordTrace (prefixWord ++ tailWord_986839) baseStart_986839 baseEnd_986839 := by
    simpa [prefixWord, tailWord_986839, baseEnd_986839] using wordTrace_append hprefix tailTrace_986839
  have hstable : (prefixWord ++ tailWord_986839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986839).length < 2 ^ (prefixWord ++ tailWord_986839).sum := by decide
  have hdescent : baseEnd_986839 < baseStart_986839 := by decide
  rcases family_descends (prefixWord ++ tailWord_986839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986842 : List Nat := [3, 1, 1, 2, 2, 5, 2, 5]
def baseStart_986842 : Nat := 118140960795 + 986842 * 2 ^ 59
def prefixEnd_986842 : Nat := 4983230072969 + 3 ^ 40 * 986842 * 2
def baseEnd_986842 : Nat := 75070263117678994049867

theorem tailTrace_986842 : CollatzResearch.WordTrace tailWord_986842 prefixEnd_986842 75070263117678994049867 := by
  unfold tailWord_986842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8998271172711862010154695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23995389793898298693745853 8998271172711862010154695)
  ·
    refine ⟨13497406759067793015232043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8998271172711862010154695 13497406759067793015232043)
    ·
      refine ⟨20246110138601689522848065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13497406759067793015232043 20246110138601689522848065)
      ·
        refine ⟨15184582603951267142136049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20246110138601689522848065 15184582603951267142136049)
        ·
          refine ⟨11388436952963450356602037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15184582603951267142136049 11388436952963450356602037)
          ·
            refine ⟨1067665964340323470931441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11388436952963450356602037 1067665964340323470931441)
            ·
              refine ⟨800749473255242603198581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067665964340323470931441 800749473255242603198581)
              ·
                refine ⟨75070263117678994049867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 800749473255242603198581 75070263117678994049867)
                ·
                  rfl

theorem cell21_986842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_986842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986842 prefixEnd_986842 := by exact prefixLift 986842
  have htrace : WordTrace (prefixWord ++ tailWord_986842) baseStart_986842 baseEnd_986842 := by
    simpa [prefixWord, tailWord_986842, baseEnd_986842] using wordTrace_append hprefix tailTrace_986842
  have hstable : (prefixWord ++ tailWord_986842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986842).length < 2 ^ (prefixWord ++ tailWord_986842).sum := by decide
  have hdescent : baseEnd_986842 < baseStart_986842 := by decide
  rcases family_descends (prefixWord ++ tailWord_986842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986980 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_986980 : Nat := 118140960795 + 986980 * 2 ^ 59
def prefixEnd_986980 : Nat := 4983230072969 + 3 ^ 40 * 986980 * 2
def baseEnd_986980 : Nat := 225242282833179408849319

theorem tailTrace_986980 : CollatzResearch.WordTrace tailWord_986980 prefixEnd_986980 225242282833179408849319 := by
  unfold tailWord_986980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17999058982173748804571197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23998745309564998406094929 17999058982173748804571197)
  ·
    refine ⟨6749647118315155801714199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17999058982173748804571197 6749647118315155801714199)
    ·
      refine ⟨10124470677472733702571299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6749647118315155801714199 10124470677472733702571299)
      ·
        refine ⟨15186706016209100553856949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10124470677472733702571299 15186706016209100553856949)
        ·
          refine ⟨1423753689019603176924089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15186706016209100553856949 1423753689019603176924089)
          ·
            refine ⟨1067815266764702382693067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423753689019603176924089 1067815266764702382693067)
            ·
              refine ⟨1601722900147053574039601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067815266764702382693067 1601722900147053574039601)
              ·
                refine ⟨1201292175110290180529701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601722900147053574039601 1201292175110290180529701)
                ·
                  refine ⟨225242282833179408849319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201292175110290180529701 225242282833179408849319)
                  ·
                    rfl

theorem cell21_986980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_986980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_986980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_986980 prefixEnd_986980 := by exact prefixLift 986980
  have htrace : WordTrace (prefixWord ++ tailWord_986980) baseStart_986980 baseEnd_986980 := by
    simpa [prefixWord, tailWord_986980, baseEnd_986980] using wordTrace_append hprefix tailTrace_986980
  have hstable : (prefixWord ++ tailWord_986980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986980).length < 2 ^ (prefixWord ++ tailWord_986980).sum := by decide
  have hdescent : baseEnd_986980 < baseStart_986980 := by decide
  rcases family_descends (prefixWord ++ tailWord_986980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987042 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_987042 : Nat := 118140960795 + 987042 * 2 ^ 59
def prefixEnd_987042 : Nat := 4983230072969 + 3 ^ 40 * 987042 * 2
def baseEnd_987042 : Nat := 225256432077881078815859

theorem tailTrace_987042 : CollatzResearch.WordTrace tailWord_987042 prefixEnd_987042 225256432077881078815859 := by
  unfold tailWord_987042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000094822530720549474845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24000252860081921465266253 9000094822530720549474845)
  ·
    refine ⟨3375035558449020206053067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9000094822530720549474845 3375035558449020206053067)
    ·
      refine ⟨5062553337673530309079601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375035558449020206053067 5062553337673530309079601)
      ·
        refine ⟨3796915003255147731809701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5062553337673530309079601 3796915003255147731809701)
        ·
          refine ⟨711921563110340199714319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3796915003255147731809701 711921563110340199714319)
          ·
            refine ⟨1067882344665510299571479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711921563110340199714319 1067882344665510299571479)
            ·
              refine ⟨1601823516998265449357219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067882344665510299571479 1601823516998265449357219)
              ·
                refine ⟨2402735275497398174035829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601823516998265449357219 2402735275497398174035829)
                ·
                  refine ⟨225256432077881078815859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402735275497398174035829 225256432077881078815859)
                  ·
                    rfl

theorem cell21_987042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_987042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987042 prefixEnd_987042 := by exact prefixLift 987042
  have htrace : WordTrace (prefixWord ++ tailWord_987042) baseStart_987042 baseEnd_987042 := by
    simpa [prefixWord, tailWord_987042, baseEnd_987042] using wordTrace_append hprefix tailTrace_987042
  have hstable : (prefixWord ++ tailWord_987042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987042).length < 2 ^ (prefixWord ++ tailWord_987042).sum := by decide
  have hdescent : baseEnd_987042 < baseStart_987042 := by decide
  rcases family_descends (prefixWord ++ tailWord_987042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987129 : List Nat := [1, 2, 1, 3, 1, 5, 3, 5]
def baseStart_987129 : Nat := 118140960795 + 987129 * 2 ^ 59
def prefixEnd_987129 : Nat := 4983230072969 + 3 ^ 40 * 987129 * 2
def baseEnd_987129 : Nat := 75092095554396086955227

theorem tailTrace_987129 : CollatzResearch.WordTrace tailWord_987129 prefixEnd_987129 75092095554396086955227 := by
  unfold tailWord_987129
  simp only [CollatzResearch.WordTrace]
  refine ⟨36003552440807696056316441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24002368293871797370877627 36003552440807696056316441)
  ·
    refine ⟨27002664330605772042237331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36003552440807696056316441 27002664330605772042237331)
    ·
      refine ⟨40503996495908658063355997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27002664330605772042237331 40503996495908658063355997)
      ·
        refine ⟨15188998685965746773758499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40503996495908658063355997 15188998685965746773758499)
        ·
          refine ⟨22783498028948620160637749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15188998685965746773758499 22783498028948620160637749)
          ·
            refine ⟨2135952940213933140059789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22783498028948620160637749 2135952940213933140059789)
            ·
              refine ⟨800982352580224927522421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2135952940213933140059789 800982352580224927522421)
              ·
                refine ⟨75092095554396086955227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 800982352580224927522421 75092095554396086955227)
                ·
                  rfl

theorem cell21_987129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 5].length) (baseStart_987129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987129 prefixEnd_987129 := by exact prefixLift 987129
  have htrace : WordTrace (prefixWord ++ tailWord_987129) baseStart_987129 baseEnd_987129 := by
    simpa [prefixWord, tailWord_987129, baseEnd_987129] using wordTrace_append hprefix tailTrace_987129
  have hstable : (prefixWord ++ tailWord_987129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987129).length < 2 ^ (prefixWord ++ tailWord_987129).sum := by decide
  have hdescent : baseEnd_987129 < baseStart_987129 := by decide
  rcases family_descends (prefixWord ++ tailWord_987129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987149 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 6]
def baseStart_987149 : Nat := 118140960795 + 987149 * 2 ^ 59
def prefixEnd_987149 : Nat := 4983230072969 + 3 ^ 40 * 987149 * 2
def baseEnd_987149 : Nat := 225280850935672670532307

theorem tailTrace_987149 : CollatzResearch.WordTrace tailWord_987149 prefixEnd_987149 225280850935672670532307 := by
  unfold tailWord_987149
  simp only [CollatzResearch.WordTrace]
  refine ⟨36004281900735239472044501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24002854600490159648029667 36004281900735239472044501)
  ·
    refine ⟨843850357048482175126043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36004281900735239472044501 843850357048482175126043)
    ·
      refine ⟨1265775535572723262689065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843850357048482175126043 1265775535572723262689065)
      ·
        refine ⟨949331651679542447016799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1265775535572723262689065 949331651679542447016799)
        ·
          refine ⟨1423997477519313670525199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949331651679542447016799 1423997477519313670525199)
          ·
            refine ⟨2135996216278970505787799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423997477519313670525199 2135996216278970505787799)
            ·
              refine ⟨3203994324418455758681699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135996216278970505787799 3203994324418455758681699)
              ·
                refine ⟨4805991486627683638022549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203994324418455758681699 4805991486627683638022549)
                ·
                  refine ⟨225280850935672670532307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4805991486627683638022549 225280850935672670532307)
                  ·
                    rfl

theorem cell21_987149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_987149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987149 prefixEnd_987149 := by exact prefixLift 987149
  have htrace : WordTrace (prefixWord ++ tailWord_987149) baseStart_987149 baseEnd_987149 := by
    simpa [prefixWord, tailWord_987149, baseEnd_987149] using wordTrace_append hprefix tailTrace_987149
  have hstable : (prefixWord ++ tailWord_987149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987149).length < 2 ^ (prefixWord ++ tailWord_987149).sum := by decide
  have hdescent : baseEnd_987149 < baseStart_987149 := by decide
  rcases family_descends (prefixWord ++ tailWord_987149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987160 : List Nat := [2, 1, 2, 3, 2, 1, 1, 6, 3]
def baseStart_987160 : Nat := 118140960795 + 987160 * 2 ^ 59
def prefixEnd_987160 : Nat := 4983230072969 + 3 ^ 40 * 987160 * 2
def baseEnd_987160 : Nat := 225283361285539095848951

theorem tailTrace_987160 : CollatzResearch.WordTrace tailWord_987160 prefixEnd_987160 225283361285539095848951 := by
  unfold tailWord_987160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18002341551847694175347467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24003122069130258900463289 18002341551847694175347467)
  ·
    refine ⟨27003512327771541263021201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18002341551847694175347467 27003512327771541263021201)
    ·
      refine ⟨20252634245828655947265901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27003512327771541263021201 20252634245828655947265901)
      ·
        refine ⟨7594737842185745980224713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20252634245828655947265901 7594737842185745980224713)
        ·
          refine ⟨5696053381639309485168535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7594737842185745980224713 5696053381639309485168535)
          ·
            refine ⟨8544080072458964227752803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696053381639309485168535 8544080072458964227752803)
            ·
              refine ⟨12816120108688446341629205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544080072458964227752803 12816120108688446341629205)
              ·
                refine ⟨600755630094770922263869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12816120108688446341629205 600755630094770922263869)
                ·
                  refine ⟨225283361285539095848951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600755630094770922263869 225283361285539095848951)
                  ·
                    rfl

theorem cell21_987160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_987160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987160 prefixEnd_987160 := by exact prefixLift 987160
  have htrace : WordTrace (prefixWord ++ tailWord_987160) baseStart_987160 baseEnd_987160 := by
    simpa [prefixWord, tailWord_987160, baseEnd_987160] using wordTrace_append hprefix tailTrace_987160
  have hstable : (prefixWord ++ tailWord_987160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987160).length < 2 ^ (prefixWord ++ tailWord_987160).sum := by decide
  have hdescent : baseEnd_987160 < baseStart_987160 := by decide
  rcases family_descends (prefixWord ++ tailWord_987160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987222 : List Nat := [5, 2, 2, 1, 1, 1, 1, 8]
def baseStart_987222 : Nat := 118140960795 + 987222 * 2 ^ 59
def prefixEnd_987222 : Nat := 4983230072969 + 3 ^ 40 * 987222 * 2
def baseEnd_987222 : Nat := 75099170176746921938497

theorem tailTrace_987222 : CollatzResearch.WordTrace tailWord_987222 prefixEnd_987222 75099170176746921938497 := by
  unfold tailWord_987222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250434026841923308715745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24004629619647181959634613 2250434026841923308715745)
  ·
    refine ⟨1687825520131442481536809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2250434026841923308715745 1687825520131442481536809)
    ·
      refine ⟨1265869140098581861152607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1687825520131442481536809 1265869140098581861152607)
      ·
        refine ⟨1898803710147872791728911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265869140098581861152607 1898803710147872791728911)
        ·
          refine ⟨2848205565221809187593367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898803710147872791728911 2848205565221809187593367)
          ·
            refine ⟨4272308347832713781390051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848205565221809187593367 4272308347832713781390051)
            ·
              refine ⟨6408462521749070672085077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272308347832713781390051 6408462521749070672085077)
              ·
                refine ⟨75099170176746921938497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6408462521749070672085077 75099170176746921938497)
                ·
                  rfl

theorem cell21_987222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_987222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987222 prefixEnd_987222 := by exact prefixLift 987222
  have htrace : WordTrace (prefixWord ++ tailWord_987222) baseStart_987222 baseEnd_987222 := by
    simpa [prefixWord, tailWord_987222, baseEnd_987222] using wordTrace_append hprefix tailTrace_987222
  have hstable : (prefixWord ++ tailWord_987222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987222).length < 2 ^ (prefixWord ++ tailWord_987222).sum := by decide
  have hdescent : baseEnd_987222 < baseStart_987222 := by decide
  rcases family_descends (prefixWord ++ tailWord_987222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987295 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 7]
def baseStart_987295 : Nat := 118140960795 + 987295 * 2 ^ 59
def prefixEnd_987295 : Nat := 4983230072969 + 3 ^ 40 * 987295 * 2
def baseEnd_987295 : Nat := 225314170124808861098675

theorem tailTrace_987295 : CollatzResearch.WordTrace tailWord_987295 prefixEnd_987295 225314170124808861098675 := by
  unfold tailWord_987295
  simp only [CollatzResearch.WordTrace]
  refine ⟨36009606958206306406859339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24006404638804204271239559 36009606958206306406859339)
  ·
    refine ⟨54014410437309459610289009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36009606958206306406859339 54014410437309459610289009)
    ·
      refine ⟨40510807827982094707716757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54014410437309459610289009 40510807827982094707716757)
      ·
        refine ⟨1898944116936660689424223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40510807827982094707716757 1898944116936660689424223)
        ·
          refine ⟨2848416175404991034136335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898944116936660689424223 2848416175404991034136335)
          ·
            refine ⟨4272624263107486551204503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848416175404991034136335 4272624263107486551204503)
            ·
              refine ⟨6408936394661229826806755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272624263107486551204503 6408936394661229826806755)
              ·
                refine ⟨9613404591991844740210133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408936394661229826806755 9613404591991844740210133)
                ·
                  refine ⟨225314170124808861098675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9613404591991844740210133 225314170124808861098675)
                  ·
                    rfl

theorem cell21_987295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_987295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987295 prefixEnd_987295 := by exact prefixLift 987295
  have htrace : WordTrace (prefixWord ++ tailWord_987295) baseStart_987295 baseEnd_987295 := by
    simpa [prefixWord, tailWord_987295, baseEnd_987295] using wordTrace_append hprefix tailTrace_987295
  have hstable : (prefixWord ++ tailWord_987295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987295).length < 2 ^ (prefixWord ++ tailWord_987295).sum := by decide
  have hdescent : baseEnd_987295 < baseStart_987295 := by decide
  rcases family_descends (prefixWord ++ tailWord_987295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987298 : List Nat := [3, 3, 1, 3, 1, 2, 3, 5]
def baseStart_987298 : Nat := 118140960795 + 987298 * 2 ^ 59
def prefixEnd_987298 : Nat := 4983230072969 + 3 ^ 40 * 987298 * 2
def baseEnd_987298 : Nat := 75104951588560507516223

theorem tailTrace_987298 : CollatzResearch.WordTrace tailWord_987298 prefixEnd_987298 75104951588560507516223 := by
  unfold tailWord_987298
  simp only [CollatzResearch.WordTrace]
  refine ⟨9002429094298859479804637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24006477584796958612812365 9002429094298859479804637)
  ·
    refine ⟨3375910910362072304926739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9002429094298859479804637 3375910910362072304926739)
    ·
      refine ⟨5063866365543108457390109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375910910362072304926739 5063866365543108457390109)
      ·
        refine ⟨1898949887078665671521291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5063866365543108457390109 1898949887078665671521291)
        ·
          refine ⟨2848424830617998507281937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898949887078665671521291 2848424830617998507281937)
          ·
            refine ⟨2136318622963498880461453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2848424830617998507281937 2136318622963498880461453)
            ·
              refine ⟨801119483611312080173045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2136318622963498880461453 801119483611312080173045)
              ·
                refine ⟨75104951588560507516223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 801119483611312080173045 75104951588560507516223)
                ·
                  rfl

theorem cell21_987298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_987298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987298 prefixEnd_987298 := by exact prefixLift 987298
  have htrace : WordTrace (prefixWord ++ tailWord_987298) baseStart_987298 baseEnd_987298 := by
    simpa [prefixWord, tailWord_987298, baseEnd_987298] using wordTrace_append hprefix tailTrace_987298
  have hstable : (prefixWord ++ tailWord_987298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987298).length < 2 ^ (prefixWord ++ tailWord_987298).sum := by decide
  have hdescent : baseEnd_987298 < baseStart_987298 := by decide
  rcases family_descends (prefixWord ++ tailWord_987298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987323 : List Nat := [1, 1, 1, 1, 1, 2, 14]
def baseStart_987323 : Nat := 118140960795 + 987323 * 2 ^ 59
def prefixEnd_987323 : Nat := 4983230072969 + 3 ^ 40 * 987323 * 2
def baseEnd_987323 : Nat := 25035617789587448292439

theorem tailTrace_987323 : CollatzResearch.WordTrace tailWord_987323 prefixEnd_987323 25035617789587448292439 := by
  unfold tailWord_987323
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010628202104867188878623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24007085468069911459252415 36010628202104867188878623)
  ·
    refine ⟨54015942303157300783317935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36010628202104867188878623 54015942303157300783317935)
    ·
      refine ⟨81023913454735951174976903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54015942303157300783317935 81023913454735951174976903)
      ·
        refine ⟨121535870182103926762465355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81023913454735951174976903 121535870182103926762465355)
        ·
          refine ⟨182303805273155890143698033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121535870182103926762465355 182303805273155890143698033)
          ·
            refine ⟨136727853954866917607773525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182303805273155890143698033 136727853954866917607773525)
            ·
              refine ⟨25035617789587448292439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 136727853954866917607773525 25035617789587448292439)
              ·
                rfl

theorem cell21_987323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 14].length) (baseStart_987323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987323 prefixEnd_987323 := by exact prefixLift 987323
  have htrace : WordTrace (prefixWord ++ tailWord_987323) baseStart_987323 baseEnd_987323 := by
    simpa [prefixWord, tailWord_987323, baseEnd_987323] using wordTrace_append hprefix tailTrace_987323
  have hstable : (prefixWord ++ tailWord_987323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987323).length < 2 ^ (prefixWord ++ tailWord_987323).sum := by decide
  have hdescent : baseEnd_987323 < baseStart_987323 := by decide
  rcases family_descends (prefixWord ++ tailWord_987323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987329 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 5]
def baseStart_987329 : Nat := 118140960795 + 987329 * 2 ^ 59
def prefixEnd_987329 : Nat := 4983230072969 + 3 ^ 40 * 987329 * 2
def baseEnd_987329 : Nat := 225321929388032357531939

theorem tailTrace_987329 : CollatzResearch.WordTrace tailWord_987329 prefixEnd_987329 225321929388032357531939 := by
  unfold tailWord_987329
  simp only [CollatzResearch.WordTrace]
  refine ⟨36010847040083130213597041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24007231360055420142398027 36010847040083130213597041)
  ·
    refine ⟨27008135280062347660197781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36010847040083130213597041 27008135280062347660197781)
    ·
      refine ⟨1266006341252922546571771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27008135280062347660197781 1266006341252922546571771)
      ·
        refine ⟨1899009511879383819857657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266006341252922546571771 1899009511879383819857657)
        ·
          refine ⟨1424257133909537864893243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899009511879383819857657 1424257133909537864893243)
          ·
            refine ⟨2136385700864306797339865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424257133909537864893243 2136385700864306797339865)
            ·
              refine ⟨1602289275648230098004899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136385700864306797339865 1602289275648230098004899)
              ·
                refine ⟨2403433913472345147007349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602289275648230098004899 2403433913472345147007349)
                ·
                  refine ⟨225321929388032357531939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2403433913472345147007349 225321929388032357531939)
                  ·
                    rfl

theorem cell21_987329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_987329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987329 prefixEnd_987329 := by exact prefixLift 987329
  have htrace : WordTrace (prefixWord ++ tailWord_987329) baseStart_987329 baseEnd_987329 := by
    simpa [prefixWord, tailWord_987329, baseEnd_987329] using wordTrace_append hprefix tailTrace_987329
  have hstable : (prefixWord ++ tailWord_987329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987329).length < 2 ^ (prefixWord ++ tailWord_987329).sum := by decide
  have hdescent : baseEnd_987329 < baseStart_987329 := by decide
  rcases family_descends (prefixWord ++ tailWord_987329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987357 : List Nat := [1, 4, 3, 2, 1, 2, 1, 7]
def baseStart_987357 : Nat := 118140960795 + 987357 * 2 ^ 59
def prefixEnd_987357 : Nat := 4983230072969 + 3 ^ 40 * 987357 * 2
def baseEnd_987357 : Nat := 75109439789836843688405

theorem tailTrace_987357 : CollatzResearch.WordTrace tailWord_987357 prefixEnd_987357 75109439789836843688405 := by
  unfold tailWord_987357
  simp only [CollatzResearch.WordTrace]
  refine ⟨36011868283981690995616325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24007912189321127330410883 36011868283981690995616325)
  ·
    refine ⟨6752225303246567061678061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36011868283981690995616325 6752225303246567061678061)
    ·
      refine ⟨2532084488717462648129273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6752225303246567061678061 2532084488717462648129273)
      ·
        refine ⟨1899063366538096986096955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2532084488717462648129273 1899063366538096986096955)
        ·
          refine ⟨2848595049807145479145433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899063366538096986096955 2848595049807145479145433)
          ·
            refine ⟨2136446287355359109359075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2848595049807145479145433 2136446287355359109359075)
            ·
              refine ⟨3204669431033038664038613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136446287355359109359075 3204669431033038664038613)
              ·
                refine ⟨75109439789836843688405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3204669431033038664038613 75109439789836843688405)
                ·
                  rfl

theorem cell21_987357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 7].length) (baseStart_987357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987357 prefixEnd_987357 := by exact prefixLift 987357
  have htrace : WordTrace (prefixWord ++ tailWord_987357) baseStart_987357 baseEnd_987357 := by
    simpa [prefixWord, tailWord_987357, baseEnd_987357] using wordTrace_append hprefix tailTrace_987357
  have hstable : (prefixWord ++ tailWord_987357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987357).length < 2 ^ (prefixWord ++ tailWord_987357).sum := by decide
  have hdescent : baseEnd_987357 < baseStart_987357 := by decide
  rcases family_descends (prefixWord ++ tailWord_987357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987363 : List Nat := [1, 1, 1, 8, 2, 1, 1, 3, 3]
def baseStart_987363 : Nat := 118140960795 + 987363 * 2 ^ 59
def prefixEnd_987363 : Nat := 4983230072969 + 3 ^ 40 * 987363 * 2
def baseEnd_987363 : Nat := 225329688651255853965203

theorem tailTrace_987363 : CollatzResearch.WordTrace tailWord_987363 prefixEnd_987363 225329688651255853965203 := by
  unfold tailWord_987363
  simp only [CollatzResearch.WordTrace]
  refine ⟨36012087121959954020334743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24008058081306636013556495 36012087121959954020334743)
  ·
    refine ⟨54018130682939931030502115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36012087121959954020334743 54018130682939931030502115)
    ·
      refine ⟨81027196024409896545753173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54018130682939931030502115 81027196024409896545753173)
      ·
        refine ⟨949537453411053475145545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 81027196024409896545753173 949537453411053475145545)
        ·
          refine ⟨712153090058290106359159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949537453411053475145545 712153090058290106359159)
          ·
            refine ⟨1068229635087435159538739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712153090058290106359159 1068229635087435159538739)
            ·
              refine ⟨1602344452631152739308109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068229635087435159538739 1602344452631152739308109)
              ·
                refine ⟨600879169736682277240541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602344452631152739308109 600879169736682277240541)
                ·
                  refine ⟨225329688651255853965203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600879169736682277240541 225329688651255853965203)
                  ·
                    rfl

theorem cell21_987363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 3].length) (baseStart_987363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987363 prefixEnd_987363 := by exact prefixLift 987363
  have htrace : WordTrace (prefixWord ++ tailWord_987363) baseStart_987363 baseEnd_987363 := by
    simpa [prefixWord, tailWord_987363, baseEnd_987363] using wordTrace_append hprefix tailTrace_987363
  have hstable : (prefixWord ++ tailWord_987363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987363).length < 2 ^ (prefixWord ++ tailWord_987363).sum := by decide
  have hdescent : baseEnd_987363 < baseStart_987363 := by decide
  rcases family_descends (prefixWord ++ tailWord_987363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987388 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_987388 : Nat := 118140960795 + 987388 * 2 ^ 59
def prefixEnd_987388 : Nat := 4983230072969 + 3 ^ 40 * 987388 * 2
def baseEnd_987388 : Nat := 225335393991861366048485

theorem tailTrace_987388 : CollatzResearch.WordTrace tailWord_987388 prefixEnd_987388 225335393991861366048485 := by
  unfold tailWord_987388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006499473434691644997409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24008665964579588859996545 18006499473434691644997409)
  ·
    refine ⟨13504874605076018733748057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18006499473434691644997409 13504874605076018733748057)
    ·
      refine ⟨10128655953807014050311043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13504874605076018733748057 10128655953807014050311043)
      ·
        refine ⟨15192983930710521075466565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10128655953807014050311043 15192983930710521075466565)
        ·
          refine ⟨2848684487008222701649981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15192983930710521075466565 2848684487008222701649981)
          ·
            refine ⟨1068256682628083513118743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2848684487008222701649981 1068256682628083513118743)
            ·
              refine ⟨1602385023942125269678115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068256682628083513118743 1602385023942125269678115)
              ·
                refine ⟨2403577535913187904517173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602385023942125269678115 2403577535913187904517173)
                ·
                  refine ⟨225335393991861366048485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2403577535913187904517173 225335393991861366048485)
                  ·
                    rfl

theorem cell21_987388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_987388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987388 prefixEnd_987388 := by exact prefixLift 987388
  have htrace : WordTrace (prefixWord ++ tailWord_987388) baseStart_987388 baseEnd_987388 := by
    simpa [prefixWord, tailWord_987388, baseEnd_987388] using wordTrace_append hprefix tailTrace_987388
  have hstable : (prefixWord ++ tailWord_987388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987388).length < 2 ^ (prefixWord ++ tailWord_987388).sum := by decide
  have hdescent : baseEnd_987388 < baseStart_987388 := by decide
  rcases family_descends (prefixWord ++ tailWord_987388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987495 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 4]
def baseStart_987495 : Nat := 118140960795 + 987495 * 2 ^ 59
def prefixEnd_987495 : Nat := 4983230072969 + 3 ^ 40 * 987495 * 2
def baseEnd_987495 : Nat := 225359812849652957764933

theorem tailTrace_987495 : CollatzResearch.WordTrace tailWord_987495 prefixEnd_987495 225359812849652957764933 := by
  unfold tailWord_987495
  simp only [CollatzResearch.WordTrace]
  refine ⟨36016901557481740564139939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24011267704987827042759959 36016901557481740564139939)
  ·
    refine ⟨54025352336222610846209909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36016901557481740564139939 54025352336222610846209909)
    ·
      refine ⟨5064876781520869766832179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54025352336222610846209909 5064876781520869766832179)
      ·
        refine ⟨7597315172281304650248269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064876781520869766832179 7597315172281304650248269)
        ·
          refine ⟨2848993189605489243843101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7597315172281304650248269 2848993189605489243843101)
          ·
            refine ⟨1068372446102058466441163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2848993189605489243843101 1068372446102058466441163)
            ·
              refine ⟨1602558669153087699661745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068372446102058466441163 1602558669153087699661745)
              ·
                refine ⟨1201919001864815774746309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602558669153087699661745 1201919001864815774746309)
                ·
                  refine ⟨225359812849652957764933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201919001864815774746309 225359812849652957764933)
                  ·
                    rfl

theorem cell21_987495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4].length) (baseStart_987495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987495 prefixEnd_987495 := by exact prefixLift 987495
  have htrace : WordTrace (prefixWord ++ tailWord_987495) baseStart_987495 baseEnd_987495 := by
    simpa [prefixWord, tailWord_987495, baseEnd_987495] using wordTrace_append hprefix tailTrace_987495
  have hstable : (prefixWord ++ tailWord_987495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987495).length < 2 ^ (prefixWord ++ tailWord_987495).sum := by decide
  have hdescent : baseEnd_987495 < baseStart_987495 := by decide
  rcases family_descends (prefixWord ++ tailWord_987495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987554 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_987554 : Nat := 118140960795 + 987554 * 2 ^ 59
def prefixEnd_987554 : Nat := 4983230072969 + 3 ^ 40 * 987554 * 2
def baseEnd_987554 : Nat := 225373277453481966281479

theorem tailTrace_987554 : CollatzResearch.WordTrace tailWord_987554 prefixEnd_987554 225373277453481966281479 := by
  unfold tailWord_987554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004763366066998410134429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24012702309511995760358477 9004763366066998410134429)
  ·
    refine ⟨3376786262275124403800411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9004763366066998410134429 3376786262275124403800411)
    ·
      refine ⟨5065179393412686605700617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376786262275124403800411 5065179393412686605700617)
      ·
        refine ⟨3798884545059514954275463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5065179393412686605700617 3798884545059514954275463)
        ·
          refine ⟨5698326817589272431413195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798884545059514954275463 5698326817589272431413195)
          ·
            refine ⟨8547490226383908647119793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698326817589272431413195 8547490226383908647119793)
            ·
              refine ⟨6410617669787931485339845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8547490226383908647119793 6410617669787931485339845)
              ·
                refine ⟨1201990813085237153501221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6410617669787931485339845 1201990813085237153501221)
                ·
                  refine ⟨225373277453481966281479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201990813085237153501221 225373277453481966281479)
                  ·
                    rfl

theorem cell21_987554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_987554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987554 prefixEnd_987554 := by exact prefixLift 987554
  have htrace : WordTrace (prefixWord ++ tailWord_987554) baseStart_987554 baseEnd_987554 := by
    simpa [prefixWord, tailWord_987554, baseEnd_987554] using wordTrace_append hprefix tailTrace_987554
  have hstable : (prefixWord ++ tailWord_987554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987554).length < 2 ^ (prefixWord ++ tailWord_987554).sum := by decide
  have hdescent : baseEnd_987554 < baseStart_987554 := by decide
  rcases family_descends (prefixWord ++ tailWord_987554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987599 : List Nat := [1, 1, 2, 1, 1, 4, 1, 7, 3]
def baseStart_987599 : Nat := 118140960795 + 987599 * 2 ^ 59
def prefixEnd_987599 : Nat := 4983230072969 + 3 ^ 40 * 987599 * 2
def baseEnd_987599 : Nat := 225383547066571888031387

theorem tailTrace_987599 : CollatzResearch.WordTrace tailWord_987599 prefixEnd_987599 225383547066571888031387 := by
  unfold tailWord_987599
  simp only [CollatzResearch.WordTrace]
  refine ⟨36020694749104966325925851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24013796499403310883950567 36020694749104966325925851)
  ·
    refine ⟨54031042123657449488888777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36020694749104966325925851 54031042123657449488888777)
    ·
      refine ⟨40523281592743087116666583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54031042123657449488888777 40523281592743087116666583)
      ·
        refine ⟨60784922389114630674999875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40523281592743087116666583 60784922389114630674999875)
        ·
          refine ⟨91177383583671946012499813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60784922389114630674999875 91177383583671946012499813)
          ·
            refine ⟨17095759421938489877343715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91177383583671946012499813 17095759421938489877343715)
            ·
              refine ⟨25643639132907734816015573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17095759421938489877343715 25643639132907734816015573)
              ·
                refine ⟨601022792177525034750365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25643639132907734816015573 601022792177525034750365)
                ·
                  refine ⟨225383547066571888031387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601022792177525034750365 225383547066571888031387)
                  ·
                    rfl

theorem cell21_987599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 3].length) (baseStart_987599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987599 prefixEnd_987599 := by exact prefixLift 987599
  have htrace : WordTrace (prefixWord ++ tailWord_987599) baseStart_987599 baseEnd_987599 := by
    simpa [prefixWord, tailWord_987599, baseEnd_987599] using wordTrace_append hprefix tailTrace_987599
  have hstable : (prefixWord ++ tailWord_987599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987599).length < 2 ^ (prefixWord ++ tailWord_987599).sum := by decide
  have hdescent : baseEnd_987599 < baseStart_987599 := by decide
  rcases family_descends (prefixWord ++ tailWord_987599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987630 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_987630 : Nat := 118140960795 + 987630 * 2 ^ 59
def prefixEnd_987630 : Nat := 4983230072969 + 3 ^ 40 * 987630 * 2
def baseEnd_987630 : Nat := 225390621688922723014657

theorem tailTrace_987630 : CollatzResearch.WordTrace tailWord_987630 prefixEnd_987630 225390621688922723014657 := by
  unfold tailWord_987630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502728176499082327538043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24014550274661772413536229 4502728176499082327538043)
  ·
    refine ⟨6754092264748623491307065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4502728176499082327538043 6754092264748623491307065)
    ·
      refine ⟨5065569198561467618480299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6754092264748623491307065 5065569198561467618480299)
      ·
        refine ⟨7598353797842201427720449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065569198561467618480299 7598353797842201427720449)
        ·
          refine ⟨5698765348381651070790337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7598353797842201427720449 5698765348381651070790337)
          ·
            refine ⟨4274074011286238303092753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5698765348381651070790337 4274074011286238303092753)
            ·
              refine ⟨3205555508464678727319565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4274074011286238303092753 3205555508464678727319565)
              ·
                refine ⟨1202083315674254522744837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3205555508464678727319565 1202083315674254522744837)
                ·
                  refine ⟨225390621688922723014657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202083315674254522744837 225390621688922723014657)
                  ·
                    rfl

theorem cell21_987630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_987630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987630 prefixEnd_987630 := by exact prefixLift 987630
  have htrace : WordTrace (prefixWord ++ tailWord_987630) baseStart_987630 baseEnd_987630 := by
    simpa [prefixWord, tailWord_987630, baseEnd_987630] using wordTrace_append hprefix tailTrace_987630
  have hstable : (prefixWord ++ tailWord_987630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987630).length < 2 ^ (prefixWord ++ tailWord_987630).sum := by decide
  have hdescent : baseEnd_987630 < baseStart_987630 := by decide
  rcases family_descends (prefixWord ++ tailWord_987630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987650 : List Nat := [3, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_987650 : Nat := 118140960795 + 987650 * 2 ^ 59
def prefixEnd_987650 : Nat := 4983230072969 + 3 ^ 40 * 987650 * 2
def baseEnd_987650 : Nat := 225395185961407132681283

theorem tailTrace_987650 : CollatzResearch.WordTrace tailWord_987650 prefixEnd_987650 225395185961407132681283 := by
  unfold tailWord_987650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005638717980050509008101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24015036581280134690688269 9005638717980050509008101)
  ·
    refine ⟨1688557259621259470439019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9005638717980050509008101 1688557259621259470439019)
    ·
      refine ⟨2532835889431889205658529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688557259621259470439019 2532835889431889205658529)
      ·
        refine ⟨1899626917073916904243897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2532835889431889205658529 1899626917073916904243897)
        ·
          refine ⟨1424720187805437678182923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899626917073916904243897 1424720187805437678182923)
          ·
            refine ⟨2137080281708156517274385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424720187805437678182923 2137080281708156517274385)
            ·
              refine ⟨1602810211281117387955789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137080281708156517274385 1602810211281117387955789)
              ·
                refine ⟨601053829230419020483421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602810211281117387955789 601053829230419020483421)
                ·
                  refine ⟨225395185961407132681283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601053829230419020483421 225395185961407132681283)
                  ·
                    rfl

theorem cell21_987650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_987650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987650 prefixEnd_987650 := by exact prefixLift 987650
  have htrace : WordTrace (prefixWord ++ tailWord_987650) baseStart_987650 baseEnd_987650 := by
    simpa [prefixWord, tailWord_987650, baseEnd_987650] using wordTrace_append hprefix tailTrace_987650
  have hstable : (prefixWord ++ tailWord_987650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987650).length < 2 ^ (prefixWord ++ tailWord_987650).sum := by decide
  have hdescent : baseEnd_987650 < baseStart_987650 := by decide
  rcases family_descends (prefixWord ++ tailWord_987650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987658 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_987658 : Nat := 118140960795 + 987658 * 2 ^ 59
def prefixEnd_987658 : Nat := 4983230072969 + 3 ^ 40 * 987658 * 2
def baseEnd_987658 : Nat := 225397011670400896547933

theorem tailTrace_987658 : CollatzResearch.WordTrace tailWord_987658 prefixEnd_987658 225397011670400896547933 := by
  unfold tailWord_987658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005711663972804850580907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24015231103927479601549085 9005711663972804850580907)
  ·
    refine ⟨13508567495959207275871361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9005711663972804850580907 13508567495959207275871361)
    ·
      refine ⟨10131425621969405456903521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13508567495959207275871361 10131425621969405456903521)
      ·
        refine ⟨7598569216477054092677641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10131425621969405456903521 7598569216477054092677641)
        ·
          refine ⟨5698926912357790569508231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7598569216477054092677641 5698926912357790569508231)
          ·
            refine ⟨8548390368536685854262347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698926912357790569508231 8548390368536685854262347)
            ·
              refine ⟨12822585552805028781393521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548390368536685854262347 12822585552805028781393521)
              ·
                refine ⟨9616939164603771586045141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12822585552805028781393521 9616939164603771586045141)
                ·
                  refine ⟨225397011670400896547933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9616939164603771586045141 225397011670400896547933)
                  ·
                    rfl

theorem cell21_987658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_987658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987658 prefixEnd_987658 := by exact prefixLift 987658
  have htrace : WordTrace (prefixWord ++ tailWord_987658) baseStart_987658 baseEnd_987658 := by
    simpa [prefixWord, tailWord_987658, baseEnd_987658] using wordTrace_append hprefix tailTrace_987658
  have hstable : (prefixWord ++ tailWord_987658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987658).length < 2 ^ (prefixWord ++ tailWord_987658).sum := by decide
  have hdescent : baseEnd_987658 < baseStart_987658 := by decide
  rcases family_descends (prefixWord ++ tailWord_987658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987703 : List Nat := [1, 1, 3, 1, 2, 3, 3, 7]
def baseStart_987703 : Nat := 118140960795 + 987703 * 2 ^ 59
def prefixEnd_987703 : Nat := 4983230072969 + 3 ^ 40 * 987703 * 2
def baseEnd_987703 : Nat := 75135760427830272765947

theorem tailTrace_987703 : CollatzResearch.WordTrace tailWord_987703 prefixEnd_987703 75135760427830272765947 := by
  unfold tailWord_987703
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024487940728192087711763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24016325293818794725141175 36024487940728192087711763)
  ·
    refine ⟨54036731911092288131567645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36024487940728192087711763 54036731911092288131567645)
    ·
      refine ⟨20263774466659608049337867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54036731911092288131567645 20263774466659608049337867)
      ·
        refine ⟨30395661699989412074006801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20263774466659608049337867 30395661699989412074006801)
        ·
          refine ⟨22796746274992059055505101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30395661699989412074006801 22796746274992059055505101)
          ·
            refine ⟨8548779853122022145814413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22796746274992059055505101 8548779853122022145814413)
            ·
              refine ⟨3205792444920758304680405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8548779853122022145814413 3205792444920758304680405)
              ·
                refine ⟨75135760427830272765947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3205792444920758304680405 75135760427830272765947)
                ·
                  rfl

theorem cell21_987703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_987703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987703 prefixEnd_987703 := by exact prefixLift 987703
  have htrace : WordTrace (prefixWord ++ tailWord_987703) baseStart_987703 baseEnd_987703 := by
    simpa [prefixWord, tailWord_987703, baseEnd_987703] using wordTrace_append hprefix tailTrace_987703
  have hstable : (prefixWord ++ tailWord_987703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987703).length < 2 ^ (prefixWord ++ tailWord_987703).sum := by decide
  have hdescent : baseEnd_987703 < baseStart_987703 := by decide
  rcases family_descends (prefixWord ++ tailWord_987703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987709 : List Nat := [1, 4, 1, 3, 2, 3, 1, 3, 3]
def baseStart_987709 : Nat := 118140960795 + 987709 * 2 ^ 59
def prefixEnd_987709 : Nat := 4983230072969 + 3 ^ 40 * 987709 * 2
def baseEnd_987709 : Nat := 225408650565236141197829

theorem tailTrace_987709 : CollatzResearch.WordTrace tailWord_987709 prefixEnd_987709 225408650565236141197829 := by
  unfold tailWord_987709
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024706778706455112430181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24016471185804303408286787 36024706778706455112430181)
  ·
    refine ⟨6754632521007460333580659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36024706778706455112430181 6754632521007460333580659)
    ·
      refine ⟨10131948781511190500370989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6754632521007460333580659 10131948781511190500370989)
      ·
        refine ⟨3799480793066696437639121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10131948781511190500370989 3799480793066696437639121)
        ·
          refine ⟨2849610594800022328229341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799480793066696437639121 2849610594800022328229341)
          ·
            refine ⟨1068603973050008373086003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2849610594800022328229341 1068603973050008373086003)
            ·
              refine ⟨1602905959575012559629005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068603973050008373086003 1602905959575012559629005)
              ·
                refine ⟨601089734840629709860877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602905959575012559629005 601089734840629709860877)
                ·
                  refine ⟨225408650565236141197829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601089734840629709860877 225408650565236141197829)
                  ·
                    rfl

theorem cell21_987709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_987709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987709 prefixEnd_987709 := by exact prefixLift 987709
  have htrace : WordTrace (prefixWord ++ tailWord_987709) baseStart_987709 baseEnd_987709 := by
    simpa [prefixWord, tailWord_987709, baseEnd_987709] using wordTrace_append hprefix tailTrace_987709
  have hstable : (prefixWord ++ tailWord_987709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987709).length < 2 ^ (prefixWord ++ tailWord_987709).sum := by decide
  have hdescent : baseEnd_987709 < baseStart_987709 := by decide
  rcases family_descends (prefixWord ++ tailWord_987709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987740 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_987740 : Nat := 118140960795 + 987740 * 2 ^ 59
def prefixEnd_987740 : Nat := 4983230072969 + 3 ^ 40 * 987740 * 2
def baseEnd_987740 : Nat := 225415725187586976181099

theorem tailTrace_987740 : CollatzResearch.WordTrace tailWord_987740 prefixEnd_987740 225415725187586976181099 := by
  unfold tailWord_987740
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012918720797073703404337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24017224961062764937872449 18012918720797073703404337)
  ·
    refine ⟨13509689040597805277553253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18012918720797073703404337 13509689040597805277553253)
    ·
      refine ⟨2533066695112088489541235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13509689040597805277553253 2533066695112088489541235)
      ·
        refine ⟨3799600042668132734311853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533066695112088489541235 3799600042668132734311853)
        ·
          refine ⟨1424850016000549775366945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3799600042668132734311853 1424850016000549775366945)
          ·
            refine ⟨1068637512000412331525209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424850016000549775366945 1068637512000412331525209)
            ·
              refine ⟨801478134000309248643907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068637512000412331525209 801478134000309248643907)
              ·
                refine ⟨1202217201000463872965861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801478134000309248643907 1202217201000463872965861)
                ·
                  refine ⟨225415725187586976181099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202217201000463872965861 225415725187586976181099)
                  ·
                    rfl

theorem cell21_987740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_987740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987740 prefixEnd_987740 := by exact prefixLift 987740
  have htrace : WordTrace (prefixWord ++ tailWord_987740) baseStart_987740 baseEnd_987740 := by
    simpa [prefixWord, tailWord_987740, baseEnd_987740] using wordTrace_append hprefix tailTrace_987740
  have hstable : (prefixWord ++ tailWord_987740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987740).length < 2 ^ (prefixWord ++ tailWord_987740).sum := by decide
  have hdescent : baseEnd_987740 < baseStart_987740 := by decide
  rcases family_descends (prefixWord ++ tailWord_987740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987824 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_987824 : Nat := 118140960795 + 987824 * 2 ^ 59
def prefixEnd_987824 : Nat := 4983230072969 + 3 ^ 40 * 987824 * 2
def baseEnd_987824 : Nat := 225434895132021496780927

theorem tailTrace_987824 : CollatzResearch.WordTrace tailWord_987824 prefixEnd_987824 225434895132021496780927 := by
  unfold tailWord_987824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014450586644914876433263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24019267448859886501911017 18014450586644914876433263)
  ·
    refine ⟨27021675879967372314649895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18014450586644914876433263 27021675879967372314649895)
    ·
      refine ⟨40532513819951058471974843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27021675879967372314649895 40532513819951058471974843)
      ·
        refine ⟨60798770729926587707962265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40532513819951058471974843 60798770729926587707962265)
        ·
          refine ⟨45599078047444940780971699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60798770729926587707962265 45599078047444940780971699)
          ·
            refine ⟨68398617071167411171457549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45599078047444940780971699 68398617071167411171457549)
            ·
              refine ⟨25649481401687779189296581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68398617071167411171457549 25649481401687779189296581)
              ·
                refine ⟨4809277762816458597993109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25649481401687779189296581 4809277762816458597993109)
                ·
                  refine ⟨225434895132021496780927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4809277762816458597993109 225434895132021496780927)
                  ·
                    rfl

theorem cell21_987824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_987824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987824 prefixEnd_987824 := by exact prefixLift 987824
  have htrace : WordTrace (prefixWord ++ tailWord_987824) baseStart_987824 baseEnd_987824 := by
    simpa [prefixWord, tailWord_987824, baseEnd_987824] using wordTrace_append hprefix tailTrace_987824
  have hstable : (prefixWord ++ tailWord_987824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987824).length < 2 ^ (prefixWord ++ tailWord_987824).sum := by decide
  have hdescent : baseEnd_987824 < baseStart_987824 := by decide
  rcases family_descends (prefixWord ++ tailWord_987824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987827 : List Nat := [1, 1, 1, 2, 3, 4, 1, 5, 3]
def baseStart_987827 : Nat := 118140960795 + 987827 * 2 ^ 59
def prefixEnd_987827 : Nat := 4983230072969 + 3 ^ 40 * 987827 * 2
def baseEnd_987827 : Nat := 225435579772894158230921

theorem tailTrace_987827 : CollatzResearch.WordTrace tailWord_987827 prefixEnd_987827 225435579772894158230921 := by
  unfold tailWord_987827
  simp only [CollatzResearch.WordTrace]
  refine ⟨36029010592278961265225735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24019340394852640843483823 36029010592278961265225735)
  ·
    refine ⟨54043515888418441897838603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36029010592278961265225735 54043515888418441897838603)
    ·
      refine ⟨81065273832627662846757905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54043515888418441897838603 81065273832627662846757905)
      ·
        refine ⟨60798955374470747135068429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81065273832627662846757905 60798955374470747135068429)
        ·
          refine ⟨22799608265426530175650661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60798955374470747135068429 22799608265426530175650661)
          ·
            refine ⟨4274926549767474407934499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22799608265426530175650661 4274926549767474407934499)
            ·
              refine ⟨6412389824651211611901749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274926549767474407934499 6412389824651211611901749)
              ·
                refine ⟨601161546061051088615789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6412389824651211611901749 601161546061051088615789)
                ·
                  refine ⟨225435579772894158230921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601161546061051088615789 225435579772894158230921)
                  ·
                    rfl

theorem cell21_987827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 3].length) (baseStart_987827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987827 prefixEnd_987827 := by exact prefixLift 987827
  have htrace : WordTrace (prefixWord ++ tailWord_987827) baseStart_987827 baseEnd_987827 := by
    simpa [prefixWord, tailWord_987827, baseEnd_987827] using wordTrace_append hprefix tailTrace_987827
  have hstable : (prefixWord ++ tailWord_987827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987827).length < 2 ^ (prefixWord ++ tailWord_987827).sum := by decide
  have hdescent : baseEnd_987827 < baseStart_987827 := by decide
  rcases family_descends (prefixWord ++ tailWord_987827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987844 : List Nat := [2, 3, 3, 1, 1, 2, 2, 4, 3]
def baseStart_987844 : Nat := 118140960795 + 987844 * 2 ^ 59
def prefixEnd_987844 : Nat := 4983230072969 + 3 ^ 40 * 987844 * 2
def baseEnd_987844 : Nat := 225439459404505906447553

theorem tailTrace_987844 : CollatzResearch.WordTrace tailWord_987844 prefixEnd_987844 225439459404505906447553 := by
  unfold tailWord_987844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014815316608686584297293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24019753755478248779063057 18014815316608686584297293)
  ·
    refine ⟨6755555743728257469111485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18014815316608686584297293 6755555743728257469111485)
    ·
      refine ⟨2533333403898096550916807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6755555743728257469111485 2533333403898096550916807)
      ·
        refine ⟨3800000105847144826375211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533333403898096550916807 3800000105847144826375211)
        ·
          refine ⟨5700000158770717239562817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800000105847144826375211 5700000158770717239562817)
          ·
            refine ⟨4275000119078037929672113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5700000158770717239562817 4275000119078037929672113)
            ·
              refine ⟨3206250089308528447254085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275000119078037929672113 3206250089308528447254085)
              ·
                refine ⟨601171891745349083860141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3206250089308528447254085 601171891745349083860141)
                ·
                  refine ⟨225439459404505906447553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601171891745349083860141 225439459404505906447553)
                  ·
                    rfl

theorem cell21_987844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_987844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987844 prefixEnd_987844 := by exact prefixLift 987844
  have htrace : WordTrace (prefixWord ++ tailWord_987844) baseStart_987844 baseEnd_987844 := by
    simpa [prefixWord, tailWord_987844, baseEnd_987844] using wordTrace_append hprefix tailTrace_987844
  have hstable : (prefixWord ++ tailWord_987844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987844).length < 2 ^ (prefixWord ++ tailWord_987844).sum := by decide
  have hdescent : baseEnd_987844 < baseStart_987844 := by decide
  rcases family_descends (prefixWord ++ tailWord_987844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987945 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 7]
def baseStart_987945 : Nat := 118140960795 + 987945 * 2 ^ 59
def prefixEnd_987945 : Nat := 4983230072969 + 3 ^ 40 * 987945 * 2
def baseEnd_987945 : Nat := 225462508980552175264013

theorem tailTrace_987945 : CollatzResearch.WordTrace tailWord_987945 prefixEnd_987945 225462508980552175264013 := by
  unfold tailWord_987945
  simp only [CollatzResearch.WordTrace]
  refine ⟨36033314405851467418021289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24022209603900978278680859 36033314405851467418021289)
  ·
    refine ⟨27024985804388600563515967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36033314405851467418021289 27024985804388600563515967)
    ·
      refine ⟨40537478706582900845273951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27024985804388600563515967 40537478706582900845273951)
      ·
        refine ⟨60806218059874351267910927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40537478706582900845273951 60806218059874351267910927)
        ·
          refine ⟨91209327089811526901866391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60806218059874351267910927 91209327089811526901866391)
          ·
            refine ⟨136813990634717290352799587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91209327089811526901866391 136813990634717290352799587)
            ·
              refine ⟨205220985952075935529199381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136813990634717290352799587 205220985952075935529199381)
              ·
                refine ⟨9619733716503559477931221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205220985952075935529199381 9619733716503559477931221)
                ·
                  refine ⟨225462508980552175264013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9619733716503559477931221 225462508980552175264013)
                  ·
                    rfl

theorem cell21_987945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_987945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987945 prefixEnd_987945 := by exact prefixLift 987945
  have htrace : WordTrace (prefixWord ++ tailWord_987945) baseStart_987945 baseEnd_987945 := by
    simpa [prefixWord, tailWord_987945, baseEnd_987945] using wordTrace_append hprefix tailTrace_987945
  have hstable : (prefixWord ++ tailWord_987945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987945).length < 2 ^ (prefixWord ++ tailWord_987945).sum := by decide
  have hdescent : baseEnd_987945 < baseStart_987945 := by decide
  rcases family_descends (prefixWord ++ tailWord_987945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987965 : List Nat := [1, 4, 1, 4, 2, 2, 1, 6]
def baseStart_987965 : Nat := 118140960795 + 987965 * 2 ^ 59
def prefixEnd_987965 : Nat := 4983230072969 + 3 ^ 40 * 987965 * 2
def baseEnd_987965 : Nat := 75155691084345528310213

theorem tailTrace_987965 : CollatzResearch.WordTrace tailWord_987965 prefixEnd_987965 75155691084345528310213 := by
  unfold tailWord_987965
  simp only [CollatzResearch.WordTrace]
  refine ⟨36034043865779010833749349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24022695910519340555832899 36034043865779010833749349)
  ·
    refine ⟨6756383224833564531328003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36034043865779010833749349 6756383224833564531328003)
    ·
      refine ⟨10134574837250346796992005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6756383224833564531328003 10134574837250346796992005)
      ·
        refine ⟨1900232781984440024436001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10134574837250346796992005 1900232781984440024436001)
        ·
          refine ⟨1425174586488330018327001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1900232781984440024436001 1425174586488330018327001)
          ·
            refine ⟨1068880939866247513745251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425174586488330018327001 1068880939866247513745251)
            ·
              refine ⟨1603321409799371270617877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068880939866247513745251 1603321409799371270617877)
              ·
                refine ⟨75155691084345528310213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1603321409799371270617877 75155691084345528310213)
                ·
                  rfl

theorem cell21_987965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 6].length) (baseStart_987965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987965 prefixEnd_987965 := by exact prefixLift 987965
  have htrace : WordTrace (prefixWord ++ tailWord_987965) baseStart_987965 baseEnd_987965 := by
    simpa [prefixWord, tailWord_987965, baseEnd_987965] using wordTrace_append hprefix tailTrace_987965
  have hstable : (prefixWord ++ tailWord_987965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987965).length < 2 ^ (prefixWord ++ tailWord_987965).sum := by decide
  have hdescent : baseEnd_987965 < baseStart_987965 := by decide
  rcases family_descends (prefixWord ++ tailWord_987965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987996 : List Nat := [2, 2, 4, 2, 1, 1, 1, 5, 3]
def baseStart_987996 : Nat := 118140960795 + 987996 * 2 ^ 59
def prefixEnd_987996 : Nat := 4983230072969 + 3 ^ 40 * 987996 * 2
def baseEnd_987996 : Nat := 225474147875387419913909

theorem tailTrace_987996 : CollatzResearch.WordTrace tailWord_987996 prefixEnd_987996 225474147875387419913909 := by
  unfold tailWord_987996
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017587264333351564063921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24023449685777802085418561 18017587264333351564063921)
  ·
    refine ⟨13513190448250013673047941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18017587264333351564063921 13513190448250013673047941)
    ·
      refine ⟨2533723209046877563696489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13513190448250013673047941 2533723209046877563696489)
      ·
        refine ⟨1900292406785158172772367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2533723209046877563696489 1900292406785158172772367)
        ·
          refine ⟨2850438610177737259158551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900292406785158172772367 2850438610177737259158551)
          ·
            refine ⟨4275657915266605888737827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850438610177737259158551 4275657915266605888737827)
            ·
              refine ⟨6413486872899908833106741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275657915266605888737827 6413486872899908833106741)
              ·
                refine ⟨601264394334366453103757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6413486872899908833106741 601264394334366453103757)
                ·
                  refine ⟨225474147875387419913909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601264394334366453103757 225474147875387419913909)
                  ·
                    rfl

theorem cell21_987996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_987996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_987996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_987996 prefixEnd_987996 := by exact prefixLift 987996
  have htrace : WordTrace (prefixWord ++ tailWord_987996) baseStart_987996 baseEnd_987996 := by
    simpa [prefixWord, tailWord_987996, baseEnd_987996] using wordTrace_append hprefix tailTrace_987996
  have hstable : (prefixWord ++ tailWord_987996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987996).length < 2 ^ (prefixWord ++ tailWord_987996).sum := by decide
  have hdescent : baseEnd_987996 < baseStart_987996 := by decide
  rcases family_descends (prefixWord ++ tailWord_987996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988007 : List Nat := [1, 1, 5, 1, 2, 3, 8]
def baseStart_988007 : Nat := 118140960795 + 988007 * 2 ^ 59
def prefixEnd_988007 : Nat := 4983230072969 + 3 ^ 40 * 988007 * 2
def baseEnd_988007 : Nat := 25052962025028205025617

theorem tailTrace_988007 : CollatzResearch.WordTrace tailWord_988007 prefixEnd_988007 25052962025028205025617 := by
  unfold tailWord_988007
  simp only [CollatzResearch.WordTrace]
  refine ⟨36035575731626852006778275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24023717154417901337852183 36035575731626852006778275)
  ·
    refine ⟨54053363597440278010167413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36035575731626852006778275 54053363597440278010167413)
    ·
      refine ⟨5067502837260026063453195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54053363597440278010167413 5067502837260026063453195)
      ·
        refine ⟨7601254255890039095179793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067502837260026063453195 7601254255890039095179793)
        ·
          refine ⟨5700940691917529321384845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7601254255890039095179793 5700940691917529321384845)
          ·
            refine ⟨2137852759469073495519317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5700940691917529321384845 2137852759469073495519317)
            ·
              refine ⟨25052962025028205025617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2137852759469073495519317 25052962025028205025617)
              ·
                rfl

theorem cell21_988007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 8].length) (baseStart_988007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988007 prefixEnd_988007 := by exact prefixLift 988007
  have htrace : WordTrace (prefixWord ++ tailWord_988007) baseStart_988007 baseEnd_988007 := by
    simpa [prefixWord, tailWord_988007, baseEnd_988007] using wordTrace_append hprefix tailTrace_988007
  have hstable : (prefixWord ++ tailWord_988007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988007).length < 2 ^ (prefixWord ++ tailWord_988007).sum := by decide
  have hdescent : baseEnd_988007 < baseStart_988007 := by decide
  rcases family_descends (prefixWord ++ tailWord_988007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988131 : List Nat := [1, 1, 1, 6, 1, 1, 3, 4, 3]
def baseStart_988131 : Nat := 118140960795 + 988131 * 2 ^ 59
def prefixEnd_988131 : Nat := 4983230072969 + 3 ^ 40 * 988131 * 2
def baseEnd_988131 : Nat := 225504956714657185163633

theorem tailTrace_988131 : CollatzResearch.WordTrace tailWord_988131 prefixEnd_988131 225504956714657185163633 := by
  unfold tailWord_988131
  simp only [CollatzResearch.WordTrace]
  refine ⟨36040098383177621184292247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24026732255451747456194831 36040098383177621184292247)
  ·
    refine ⟨54060147574766431776438371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36040098383177621184292247 54060147574766431776438371)
    ·
      refine ⟨81090221362149647664657557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54060147574766431776438371 81090221362149647664657557)
      ·
        refine ⟨3801104126350764734280823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81090221362149647664657557 3801104126350764734280823)
        ·
          refine ⟨5701656189526147101421235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801104126350764734280823 5701656189526147101421235)
          ·
            refine ⟨8552484284289220652131853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5701656189526147101421235 8552484284289220652131853)
            ·
              refine ⟨3207181606608457744549445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8552484284289220652131853 3207181606608457744549445)
              ·
                refine ⟨601346551239085827103021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3207181606608457744549445 601346551239085827103021)
                ·
                  refine ⟨225504956714657185163633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601346551239085827103021 225504956714657185163633)
                  ·
                    rfl

theorem cell21_988131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 3].length) (baseStart_988131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988131 prefixEnd_988131 := by exact prefixLift 988131
  have htrace : WordTrace (prefixWord ++ tailWord_988131) baseStart_988131 baseEnd_988131 := by
    simpa [prefixWord, tailWord_988131, baseEnd_988131] using wordTrace_append hprefix tailTrace_988131
  have hstable : (prefixWord ++ tailWord_988131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988131).length < 2 ^ (prefixWord ++ tailWord_988131).sum := by decide
  have hdescent : baseEnd_988131 < baseStart_988131 := by decide
  rcases family_descends (prefixWord ++ tailWord_988131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988145 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 4]
def baseStart_988145 : Nat := 118140960795 + 988145 * 2 ^ 59
def prefixEnd_988145 : Nat := 4983230072969 + 3 ^ 40 * 988145 * 2
def baseEnd_988145 : Nat := 225508151705396271930271

theorem tailTrace_988145 : CollatzResearch.WordTrace tailWord_988145 prefixEnd_988145 225508151705396271930271 := by
  unfold tailWord_988145
  simp only [CollatzResearch.WordTrace]
  refine ⟨36040609005126901575301889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24027072670084601050201259 36040609005126901575301889)
  ·
    refine ⟨27030456753845176181476417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36040609005126901575301889 27030456753845176181476417)
    ·
      refine ⟨20272842565383882136107313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27030456753845176181476417 20272842565383882136107313)
      ·
        refine ⟨15204631924037911602080485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20272842565383882136107313 15204631924037911602080485)
        ·
          refine ⟨2850868485757108425390091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15204631924037911602080485 2850868485757108425390091)
          ·
            refine ⟨4276302728635662638085137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850868485757108425390091 4276302728635662638085137)
            ·
              refine ⟨3207227046476746978563853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4276302728635662638085137 3207227046476746978563853)
              ·
                refine ⟨1202710142428780116961445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3207227046476746978563853 1202710142428780116961445)
                ·
                  refine ⟨225508151705396271930271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202710142428780116961445 225508151705396271930271)
                  ·
                    rfl

theorem cell21_988145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_988145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988145 prefixEnd_988145 := by exact prefixLift 988145
  have htrace : WordTrace (prefixWord ++ tailWord_988145) baseStart_988145 baseEnd_988145 := by
    simpa [prefixWord, tailWord_988145, baseEnd_988145] using wordTrace_append hprefix tailTrace_988145
  have hstable : (prefixWord ++ tailWord_988145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988145).length < 2 ^ (prefixWord ++ tailWord_988145).sum := by decide
  have hdescent : baseEnd_988145 < baseStart_988145 := by decide
  rcases family_descends (prefixWord ++ tailWord_988145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988249 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 5]
def baseStart_988249 : Nat := 118140960795 + 988249 * 2 ^ 59
def prefixEnd_988249 : Nat := 4983230072969 + 3 ^ 40 * 988249 * 2
def baseEnd_988249 : Nat := 225531885922315202196725

theorem tailTrace_988249 : CollatzResearch.WordTrace tailWord_988249 prefixEnd_988249 225531885922315202196725 := by
  unfold tailWord_988249
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044402196750127337087801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24029601464500084891391867 36044402196750127337087801)
  ·
    refine ⟨27033301647562595502815851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36044402196750127337087801 27033301647562595502815851)
    ·
      refine ⟨40549952471343893254223777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27033301647562595502815851 40549952471343893254223777)
      ·
        refine ⟨30412464353507919940667833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40549952471343893254223777 30412464353507919940667833)
        ·
          refine ⟨22809348265130939955500875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30412464353507919940667833 22809348265130939955500875)
          ·
            refine ⟨34214022397696409933251313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22809348265130939955500875 34214022397696409933251313)
            ·
              refine ⟨25660516798272307449938485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34214022397696409933251313 25660516798272307449938485)
              ·
                refine ⟨2405673449838028823431733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25660516798272307449938485 2405673449838028823431733)
                ·
                  refine ⟨225531885922315202196725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2405673449838028823431733 225531885922315202196725)
                  ·
                    rfl

theorem cell21_988249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_988249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988249 prefixEnd_988249 := by exact prefixLift 988249
  have htrace : WordTrace (prefixWord ++ tailWord_988249) baseStart_988249 baseEnd_988249 := by
    simpa [prefixWord, tailWord_988249, baseEnd_988249] using wordTrace_append hprefix tailTrace_988249
  have hstable : (prefixWord ++ tailWord_988249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988249).length < 2 ^ (prefixWord ++ tailWord_988249).sum := by decide
  have hdescent : baseEnd_988249 < baseStart_988249 := by decide
  rcases family_descends (prefixWord ++ tailWord_988249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988286 : List Nat := [4, 2, 4, 1, 2, 8]
def baseStart_988286 : Nat := 118140960795 + 988286 * 2 ^ 59
def prefixEnd_988286 : Nat := 4983230072969 + 3 ^ 40 * 988286 * 2
def baseEnd_988286 : Nat := 8353345549126346669629

theorem tailTrace_988286 : CollatzResearch.WordTrace tailWord_988286 prefixEnd_988286 8353345549126346669629 := by
  unfold tailWord_988286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4505718962202010332023089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24030501131744055104123141 4505718962202010332023089)
  ·
    refine ⟨3379289221651507749017317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4505718962202010332023089 3379289221651507749017317)
    ·
      refine ⟨633616729059657702940747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3379289221651507749017317 633616729059657702940747)
      ·
        refine ⟨950425093589486554411121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633616729059657702940747 950425093589486554411121)
        ·
          refine ⟨712818820192114915808341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950425093589486554411121 712818820192114915808341)
          ·
            refine ⟨8353345549126346669629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 712818820192114915808341 8353345549126346669629)
            ·
              rfl

theorem cell21_988286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 8].length) (baseStart_988286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988286 prefixEnd_988286 := by exact prefixLift 988286
  have htrace : WordTrace (prefixWord ++ tailWord_988286) baseStart_988286 baseEnd_988286 := by
    simpa [prefixWord, tailWord_988286, baseEnd_988286] using wordTrace_append hprefix tailTrace_988286
  have hstable : (prefixWord ++ tailWord_988286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988286).length < 2 ^ (prefixWord ++ tailWord_988286).sum := by decide
  have hdescent : baseEnd_988286 < baseStart_988286 := by decide
  rcases family_descends (prefixWord ++ tailWord_988286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988297 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 4]
def baseStart_988297 : Nat := 118140960795 + 988297 * 2 ^ 59
def prefixEnd_988297 : Nat := 4983230072969 + 3 ^ 40 * 988297 * 2
def baseEnd_988297 : Nat := 225542840176277785396627

theorem tailTrace_988297 : CollatzResearch.WordTrace tailWord_988297 prefixEnd_988297 225542840176277785396627 := by
  unfold tailWord_988297
  simp only [CollatzResearch.WordTrace]
  refine ⟨36046152900576231534835145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24030768600384154356556763 36046152900576231534835145)
  ·
    refine ⟨27034614675432173651126359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36046152900576231534835145 27034614675432173651126359)
    ·
      refine ⟨40551922013148260476689539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27034614675432173651126359 40551922013148260476689539)
      ·
        refine ⟨60827883019722390715034309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40551922013148260476689539 60827883019722390715034309)
        ·
          refine ⟨11405228066197948259068933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60827883019722390715034309 11405228066197948259068933)
          ·
            refine ⟨2138480262412115298575425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11405228066197948259068933 2138480262412115298575425)
            ·
              refine ⟨1603860196809086473931569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138480262412115298575425 1603860196809086473931569)
              ·
                refine ⟨1202895147606814855448677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603860196809086473931569 1202895147606814855448677)
                ·
                  refine ⟨225542840176277785396627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202895147606814855448677 225542840176277785396627)
                  ·
                    rfl

theorem cell21_988297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_988297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988297 prefixEnd_988297 := by exact prefixLift 988297
  have htrace : WordTrace (prefixWord ++ tailWord_988297) baseStart_988297 baseEnd_988297 := by
    simpa [prefixWord, tailWord_988297, baseEnd_988297] using wordTrace_append hprefix tailTrace_988297
  have hstable : (prefixWord ++ tailWord_988297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988297).length < 2 ^ (prefixWord ++ tailWord_988297).sum := by decide
  have hdescent : baseEnd_988297 < baseStart_988297 := by decide
  rcases family_descends (prefixWord ++ tailWord_988297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988311 : List Nat := [1, 1, 3, 3, 3, 1, 3, 6]
def baseStart_988311 : Nat := 118140960795 + 988311 * 2 ^ 59
def prefixEnd_988311 : Nat := 4983230072969 + 3 ^ 40 * 988311 * 2
def baseEnd_988311 : Nat := 75182011722338957387755

theorem tailTrace_988311 : CollatzResearch.WordTrace tailWord_988311 prefixEnd_988311 75182011722338957387755 := by
  unfold tailWord_988311
  simp only [CollatzResearch.WordTrace]
  refine ⟨36046663522525511925844787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24031109015017007950563191 36046663522525511925844787)
  ·
    refine ⟨54069995283788267888767181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36046663522525511925844787 54069995283788267888767181)
    ·
      refine ⟨20276248231420600458287693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54069995283788267888767181 20276248231420600458287693)
      ·
        refine ⟨7603593086782725171857885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20276248231420600458287693 7603593086782725171857885)
        ·
          refine ⟨2851347407543521939446707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7603593086782725171857885 2851347407543521939446707)
          ·
            refine ⟨4277021111315282909170061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851347407543521939446707 4277021111315282909170061)
            ·
              refine ⟨1603882916743231090938773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4277021111315282909170061 1603882916743231090938773)
              ·
                refine ⟨75182011722338957387755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1603882916743231090938773 75182011722338957387755)
                ·
                  rfl

theorem cell21_988311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 6].length) (baseStart_988311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988311 prefixEnd_988311 := by exact prefixLift 988311
  have htrace : WordTrace (prefixWord ++ tailWord_988311) baseStart_988311 baseEnd_988311 := by
    simpa [prefixWord, tailWord_988311, baseEnd_988311] using wordTrace_append hprefix tailTrace_988311
  have hstable : (prefixWord ++ tailWord_988311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988311).length < 2 ^ (prefixWord ++ tailWord_988311).sum := by decide
  have hdescent : baseEnd_988311 < baseStart_988311 := by decide
  rcases family_descends (prefixWord ++ tailWord_988311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988325 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 7]
def baseStart_988325 : Nat := 118140960795 + 988325 * 2 ^ 59
def prefixEnd_988325 : Nat := 4983230072969 + 3 ^ 40 * 988325 * 2
def baseEnd_988325 : Nat := 225549230157755958929903

theorem tailTrace_988325 : CollatzResearch.WordTrace tailWord_988325 prefixEnd_988325 225549230157755958929903 := by
  unfold tailWord_988325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36047174144474792316854429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24031449429649861544569619 36047174144474792316854429)
  ·
    refine ⟨13517690304178047118820411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36047174144474792316854429 13517690304178047118820411)
    ·
      refine ⟨20276535456267070678230617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13517690304178047118820411 20276535456267070678230617)
      ·
        refine ⟨15207401592200303008672963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20276535456267070678230617 15207401592200303008672963)
        ·
          refine ⟨22811102388300454513009445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15207401592200303008672963 22811102388300454513009445)
          ·
            refine ⟨4277081697806335221189271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22811102388300454513009445 4277081697806335221189271)
            ·
              refine ⟨6415622546709502831783907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277081697806335221189271 6415622546709502831783907)
              ·
                refine ⟨9623433820064254247675861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415622546709502831783907 9623433820064254247675861)
                ·
                  refine ⟨225549230157755958929903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9623433820064254247675861 225549230157755958929903)
                  ·
                    rfl

theorem cell21_988325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_988325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988325 prefixEnd_988325 := by exact prefixLift 988325
  have htrace : WordTrace (prefixWord ++ tailWord_988325) baseStart_988325 baseEnd_988325 := by
    simpa [prefixWord, tailWord_988325, baseEnd_988325] using wordTrace_append hprefix tailTrace_988325
  have hstable : (prefixWord ++ tailWord_988325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988325).length < 2 ^ (prefixWord ++ tailWord_988325).sum := by decide
  have hdescent : baseEnd_988325 < baseStart_988325 := by decide
  rcases family_descends (prefixWord ++ tailWord_988325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988525 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 4]
def baseStart_988525 : Nat := 118140960795 + 988525 * 2 ^ 59
def prefixEnd_988525 : Nat := 4983230072969 + 3 ^ 40 * 988525 * 2
def baseEnd_988525 : Nat := 225594872882600055596161

theorem tailTrace_988525 : CollatzResearch.WordTrace tailWord_988525 prefixEnd_988525 225594872882600055596161 := by
  unfold tailWord_988525
  simp only [CollatzResearch.WordTrace]
  refine ⟨36054468743750226474135029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24036312495833484316090019 36054468743750226474135029)
  ·
    refine ⟨3380106444726583731950159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36054468743750226474135029 3380106444726583731950159)
    ·
      refine ⟨5070159667089875597925239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3380106444726583731950159 5070159667089875597925239)
      ·
        refine ⟨7605239500634813396887859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070159667089875597925239 7605239500634813396887859)
        ·
          refine ⟨11407859250952220095331789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605239500634813396887859 11407859250952220095331789)
          ·
            refine ⟨4277947219107082535749421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11407859250952220095331789 4277947219107082535749421)
            ·
              refine ⟨1604230207165155950906033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4277947219107082535749421 1604230207165155950906033)
              ·
                refine ⟨1203172655373866963179525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604230207165155950906033 1203172655373866963179525)
                ·
                  refine ⟨225594872882600055596161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203172655373866963179525 225594872882600055596161)
                  ·
                    rfl

theorem cell21_988525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_988525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988525 prefixEnd_988525 := by exact prefixLift 988525
  have htrace : WordTrace (prefixWord ++ tailWord_988525) baseStart_988525 baseEnd_988525 := by
    simpa [prefixWord, tailWord_988525, baseEnd_988525] using wordTrace_append hprefix tailTrace_988525
  have hstable : (prefixWord ++ tailWord_988525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988525).length < 2 ^ (prefixWord ++ tailWord_988525).sum := by decide
  have hdescent : baseEnd_988525 < baseStart_988525 := by decide
  rcases family_descends (prefixWord ++ tailWord_988525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988562 : List Nat := [3, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_988562 : Nat := 118140960795 + 988562 * 2 ^ 59
def prefixEnd_988562 : Nat := 4983230072969 + 3 ^ 40 * 988562 * 2
def baseEnd_988562 : Nat := 225603316786696213479419

theorem tailTrace_988562 : CollatzResearch.WordTrace tailWord_988562 prefixEnd_988562 225603316786696213479419 := by
  unfold tailWord_988562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013954561154045448307985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24037212163077454528821293 9013954561154045448307985)
  ·
    refine ⟨6760465920865534086230989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9013954561154045448307985 6760465920865534086230989)
    ·
      refine ⟨2535174720324575282336621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6760465920865534086230989 2535174720324575282336621)
      ·
        refine ⟨950690520121715730876233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2535174720324575282336621 950690520121715730876233)
        ·
          refine ⟨713017890091286798157175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950690520121715730876233 713017890091286798157175)
          ·
            refine ⟨1069526835136930197235763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713017890091286798157175 1069526835136930197235763)
            ·
              refine ⟨1604290252705395295853645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069526835136930197235763 1604290252705395295853645)
              ·
                refine ⟨601608844764523235945117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1604290252705395295853645 601608844764523235945117)
                ·
                  refine ⟨225603316786696213479419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601608844764523235945117 225603316786696213479419)
                  ·
                    rfl

theorem cell21_988562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_988562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988562 prefixEnd_988562 := by exact prefixLift 988562
  have htrace : WordTrace (prefixWord ++ tailWord_988562) baseStart_988562 baseEnd_988562 := by
    simpa [prefixWord, tailWord_988562, baseEnd_988562] using wordTrace_append hprefix tailTrace_988562
  have hstable : (prefixWord ++ tailWord_988562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988562).length < 2 ^ (prefixWord ++ tailWord_988562).sum := by decide
  have hdescent : baseEnd_988562 < baseStart_988562 := by decide
  rcases family_descends (prefixWord ++ tailWord_988562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988601 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 4]
def baseStart_988601 : Nat := 118140960795 + 988601 * 2 ^ 59
def prefixEnd_988601 : Nat := 4983230072969 + 3 ^ 40 * 988601 * 2
def baseEnd_988601 : Nat := 225612217118040812329339

theorem tailTrace_988601 : CollatzResearch.WordTrace tailWord_988601 prefixEnd_988601 225612217118040812329339 := by
  unfold tailWord_988601
  simp only [CollatzResearch.WordTrace]
  refine ⟨36057240691474891453901657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24038160460983260969267771 36057240691474891453901657)
  ·
    refine ⟨27042930518606168590426243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36057240691474891453901657 27042930518606168590426243)
    ·
      refine ⟨40564395777909252885639365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27042930518606168590426243 40564395777909252885639365)
      ·
        refine ⟨7605824208357984916057381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40564395777909252885639365 7605824208357984916057381)
        ·
          refine ⟨1426092039067122171760759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7605824208357984916057381 1426092039067122171760759)
          ·
            refine ⟨2139138058600683257641139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426092039067122171760759 2139138058600683257641139)
            ·
              refine ⟨3208707087901024886461709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139138058600683257641139 3208707087901024886461709)
              ·
                refine ⟨1203265157962884332423141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208707087901024886461709 1203265157962884332423141)
                ·
                  refine ⟨225612217118040812329339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203265157962884332423141 225612217118040812329339)
                  ·
                    rfl

theorem cell21_988601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_988601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988601 prefixEnd_988601 := by exact prefixLift 988601
  have htrace : WordTrace (prefixWord ++ tailWord_988601) baseStart_988601 baseEnd_988601 := by
    simpa [prefixWord, tailWord_988601, baseEnd_988601] using wordTrace_append hprefix tailTrace_988601
  have hstable : (prefixWord ++ tailWord_988601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988601).length < 2 ^ (prefixWord ++ tailWord_988601).sum := by decide
  have hdescent : baseEnd_988601 < baseStart_988601 := by decide
  rcases family_descends (prefixWord ++ tailWord_988601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988705 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 5]
def baseStart_988705 : Nat := 118140960795 + 988705 * 2 ^ 59
def prefixEnd_988705 : Nat := 4983230072969 + 3 ^ 40 * 988705 * 2
def baseEnd_988705 : Nat := 225635951334959742595793

theorem tailTrace_988705 : CollatzResearch.WordTrace tailWord_988705 prefixEnd_988705 225635951334959742595793 := by
  unfold tailWord_988705
  simp only [CollatzResearch.WordTrace]
  refine ⟨36061033883098117215687569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24040689255398744810458379 36061033883098117215687569)
  ·
    refine ⟨27045775412323587911765677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36061033883098117215687569 27045775412323587911765677)
    ·
      refine ⟨10142165779621345466912129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27045775412323587911765677 10142165779621345466912129)
      ·
        refine ⟨7606624334716009100184097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10142165779621345466912129 7606624334716009100184097)
        ·
          refine ⟨5704968251037006825138073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606624334716009100184097 5704968251037006825138073)
          ·
            refine ⟨4278726188277755118853555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704968251037006825138073 4278726188277755118853555)
            ·
              refine ⟨6418089282416632678280333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278726188277755118853555 6418089282416632678280333)
              ·
                refine ⟨2406783480906237254355125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6418089282416632678280333 2406783480906237254355125)
                ·
                  refine ⟨225635951334959742595793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2406783480906237254355125 225635951334959742595793)
                  ·
                    rfl

theorem cell21_988705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_988705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988705 prefixEnd_988705 := by exact prefixLift 988705
  have htrace : WordTrace (prefixWord ++ tailWord_988705) baseStart_988705 baseEnd_988705 := by
    simpa [prefixWord, tailWord_988705, baseEnd_988705] using wordTrace_append hprefix tailTrace_988705
  have hstable : (prefixWord ++ tailWord_988705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988705).length < 2 ^ (prefixWord ++ tailWord_988705).sum := by decide
  have hdescent : baseEnd_988705 < baseStart_988705 := by decide
  rcases family_descends (prefixWord ++ tailWord_988705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988812 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_988812 : Nat := 118140960795 + 988812 * 2 ^ 59
def prefixEnd_988812 : Nat := 4983230072969 + 3 ^ 40 * 988812 * 2
def baseEnd_988812 : Nat := 225660370192751334312241

theorem tailTrace_988812 : CollatzResearch.WordTrace tailWord_988812 prefixEnd_988812 225660370192751334312241 := by
  unfold tailWord_988812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032468246855237244916345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24043290995806982993221793 18032468246855237244916345)
  ·
    refine ⟨13524351185141427933687259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18032468246855237244916345 13524351185141427933687259)
    ·
      refine ⟨20286526777712141900530889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13524351185141427933687259 20286526777712141900530889)
      ·
        refine ⟨15214895083284106425398167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20286526777712141900530889 15214895083284106425398167)
        ·
          refine ⟨22822342624926159638097251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214895083284106425398167 22822342624926159638097251)
          ·
            refine ⟨34233513937389239457145877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22822342624926159638097251 34233513937389239457145877)
            ·
              refine ⟨1604695965815120599553713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34233513937389239457145877 1604695965815120599553713)
              ·
                refine ⟨1203521974361340449665285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604695965815120599553713 1203521974361340449665285)
                ·
                  refine ⟨225660370192751334312241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203521974361340449665285 225660370192751334312241)
                  ·
                    rfl

theorem cell21_988812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_988812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988812 prefixEnd_988812 := by exact prefixLift 988812
  have htrace : WordTrace (prefixWord ++ tailWord_988812) baseStart_988812 baseEnd_988812 := by
    simpa [prefixWord, tailWord_988812, baseEnd_988812] using wordTrace_append hprefix tailTrace_988812
  have hstable : (prefixWord ++ tailWord_988812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988812).length < 2 ^ (prefixWord ++ tailWord_988812).sum := by decide
  have hdescent : baseEnd_988812 < baseStart_988812 := by decide
  rcases family_descends (prefixWord ++ tailWord_988812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988871 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 6]
def baseStart_988871 : Nat := 118140960795 + 988871 * 2 ^ 59
def prefixEnd_988871 : Nat := 4983230072969 + 3 ^ 40 * 988871 * 2
def baseEnd_988871 : Nat := 225673834796580342828787

theorem tailTrace_988871 : CollatzResearch.WordTrace tailWord_988871 prefixEnd_988871 225673834796580342828787 := by
  unfold tailWord_988871
  simp only [CollatzResearch.WordTrace]
  refine ⟨36067088400496727566230467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24044725600331151710820311 36067088400496727566230467)
  ·
    refine ⟨54100632600745091349345701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36067088400496727566230467 54100632600745091349345701)
    ·
      refine ⟨10143868612639704628002319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54100632600745091349345701 10143868612639704628002319)
      ·
        refine ⟨15215802918959556942003479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143868612639704628002319 15215802918959556942003479)
        ·
          refine ⟨22823704378439335413005219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15215802918959556942003479 22823704378439335413005219)
          ·
            refine ⟨34235556567659003119507829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22823704378439335413005219 34235556567659003119507829)
            ·
              refine ⟨3209583428218031542453859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34235556567659003119507829 3209583428218031542453859)
              ·
                refine ⟨4814375142327047313680789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209583428218031542453859 4814375142327047313680789)
                ·
                  refine ⟨225673834796580342828787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4814375142327047313680789 225673834796580342828787)
                  ·
                    rfl

theorem cell21_988871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_988871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988871 prefixEnd_988871 := by exact prefixLift 988871
  have htrace : WordTrace (prefixWord ++ tailWord_988871) baseStart_988871 baseEnd_988871 := by
    simpa [prefixWord, tailWord_988871, baseEnd_988871] using wordTrace_append hprefix tailTrace_988871
  have hstable : (prefixWord ++ tailWord_988871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988871).length < 2 ^ (prefixWord ++ tailWord_988871).sum := by decide
  have hdescent : baseEnd_988871 < baseStart_988871 := by decide
  rcases family_descends (prefixWord ++ tailWord_988871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988874 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_988874 : Nat := 118140960795 + 988874 * 2 ^ 59
def prefixEnd_988874 : Nat := 4983230072969 + 3 ^ 40 * 988874 * 2
def baseEnd_988874 : Nat := 225674519437453004278781

theorem tailTrace_988874 : CollatzResearch.WordTrace tailWord_988874 prefixEnd_988874 225674519437453004278781 := by
  unfold tailWord_988874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016799454871464769647419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24044798546323906052393117 9016799454871464769647419)
  ·
    refine ⟨13525199182307197154471129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9016799454871464769647419 13525199182307197154471129)
    ·
      refine ⟨10143899386730397865853347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13525199182307197154471129 10143899386730397865853347)
      ·
        refine ⟨15215849080095596798780021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143899386730397865853347 15215849080095596798780021)
        ·
          refine ⟨1426485851258962199885627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15215849080095596798780021 1426485851258962199885627)
          ·
            refine ⟨2139728776888443299828441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426485851258962199885627 2139728776888443299828441)
            ·
              refine ⟨1604796582666332474871331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139728776888443299828441 1604796582666332474871331)
              ·
                refine ⟨2407194873999498712306997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604796582666332474871331 2407194873999498712306997)
                ·
                  refine ⟨225674519437453004278781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2407194873999498712306997 225674519437453004278781)
                  ·
                    rfl

theorem cell21_988874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_988874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988874 prefixEnd_988874 := by exact prefixLift 988874
  have htrace : WordTrace (prefixWord ++ tailWord_988874) baseStart_988874 baseEnd_988874 := by
    simpa [prefixWord, tailWord_988874, baseEnd_988874] using wordTrace_append hprefix tailTrace_988874
  have hstable : (prefixWord ++ tailWord_988874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988874).length < 2 ^ (prefixWord ++ tailWord_988874).sum := by decide
  have hdescent : baseEnd_988874 < baseStart_988874 := by decide
  rcases family_descends (prefixWord ++ tailWord_988874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988981 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 4]
def baseStart_988981 : Nat := 118140960795 + 988981 * 2 ^ 59
def prefixEnd_988981 : Nat := 4983230072969 + 3 ^ 40 * 988981 * 2
def baseEnd_988981 : Nat := 225698938295244595995229

theorem tailTrace_988981 : CollatzResearch.WordTrace tailWord_988981 prefixEnd_988981 225698938295244595995229 := by
  unfold tailWord_988981
  simp only [CollatzResearch.WordTrace]
  refine ⟨36071100430098216352734797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24047400286732144235156531 36071100430098216352734797)
  ·
    refine ⟨13526662661286831132275549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36071100430098216352734797 13526662661286831132275549)
    ·
      refine ⟨5072498497982561674603331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13526662661286831132275549 5072498497982561674603331)
      ·
        refine ⟨7608747746973842511904997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072498497982561674603331 7608747746973842511904997)
        ·
          refine ⟨1426640202557595470982187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7608747746973842511904997 1426640202557595470982187)
          ·
            refine ⟨2139960303836393206473281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426640202557595470982187 2139960303836393206473281)
            ·
              refine ⟨1604970227877294904854961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139960303836393206473281 1604970227877294904854961)
              ·
                refine ⟨1203727670907971178641221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604970227877294904854961 1203727670907971178641221)
                ·
                  refine ⟨225698938295244595995229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203727670907971178641221 225698938295244595995229)
                  ·
                    rfl

theorem cell21_988981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_988981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988981 prefixEnd_988981 := by exact prefixLift 988981
  have htrace : WordTrace (prefixWord ++ tailWord_988981) baseStart_988981 baseEnd_988981 := by
    simpa [prefixWord, tailWord_988981, baseEnd_988981] using wordTrace_append hprefix tailTrace_988981
  have hstable : (prefixWord ++ tailWord_988981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988981).length < 2 ^ (prefixWord ++ tailWord_988981).sum := by decide
  have hdescent : baseEnd_988981 < baseStart_988981 := by decide
  rcases family_descends (prefixWord ++ tailWord_988981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988998 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_988998 : Nat := 118140960795 + 988998 * 2 ^ 59
def prefixEnd_988998 : Nat := 4983230072969 + 3 ^ 40 * 988998 * 2
def baseEnd_988998 : Nat := 225702817926856344211861

theorem tailTrace_988998 : CollatzResearch.WordTrace tailWord_988998 prefixEnd_988998 225702817926856344211861 := by
  unfold tailWord_988998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127241264719894633003239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24047813647357752170735765 1127241264719894633003239)
  ·
    refine ⟨1690861897079841949504859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1127241264719894633003239 1690861897079841949504859)
    ·
      refine ⟨2536292845619762924257289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1690861897079841949504859 2536292845619762924257289)
      ·
        refine ⟨1902219634214822193192967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2536292845619762924257289 1902219634214822193192967)
        ·
          refine ⟨2853329451322233289789451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902219634214822193192967 2853329451322233289789451)
          ·
            refine ⟨4279994176983349934684177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853329451322233289789451 4279994176983349934684177)
            ·
              refine ⟨3209995632737512451013133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4279994176983349934684177 3209995632737512451013133)
              ·
                refine ⟨1203748362276567169129925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3209995632737512451013133 1203748362276567169129925)
                ·
                  refine ⟨225702817926856344211861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203748362276567169129925 225702817926856344211861)
                  ·
                    rfl

theorem cell21_988998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_988998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_988998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_988998 prefixEnd_988998 := by exact prefixLift 988998
  have htrace : WordTrace (prefixWord ++ tailWord_988998) baseStart_988998 baseEnd_988998 := by
    simpa [prefixWord, tailWord_988998, baseEnd_988998] using wordTrace_append hprefix tailTrace_988998
  have hstable : (prefixWord ++ tailWord_988998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988998).length < 2 ^ (prefixWord ++ tailWord_988998).sum := by decide
  have hdescent : baseEnd_988998 < baseStart_988998 := by decide
  rcases family_descends (prefixWord ++ tailWord_988998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989009 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 5]
def baseStart_989009 : Nat := 118140960795 + 989009 * 2 ^ 59
def prefixEnd_989009 : Nat := 4983230072969 + 3 ^ 40 * 989009 * 2
def baseEnd_989009 : Nat := 225705328276722769528505

theorem tailTrace_989009 : CollatzResearch.WordTrace tailWord_989009 prefixEnd_989009 225705328276722769528505 := by
  unfold tailWord_989009
  simp only [CollatzResearch.WordTrace]
  refine ⟨36072121673996777134754081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24048081115997851423169387 36072121673996777134754081)
  ·
    refine ⟨27054091255497582851065561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36072121673996777134754081 27054091255497582851065561)
    ·
      refine ⟨20290568441623187138299171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27054091255497582851065561 20290568441623187138299171)
      ·
        refine ⟨30435852662434780707448757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20290568441623187138299171 30435852662434780707448757)
        ·
          refine ⟨2853361187103260691323321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30435852662434780707448757 2853361187103260691323321)
          ·
            refine ⟨2140020890327445518492491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2853361187103260691323321 2140020890327445518492491)
            ·
              refine ⟨3210031335491168277738737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140020890327445518492491 3210031335491168277738737)
              ·
                refine ⟨2407523501618376208304053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210031335491168277738737 2407523501618376208304053)
                ·
                  refine ⟨225705328276722769528505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2407523501618376208304053 225705328276722769528505)
                  ·
                    rfl

theorem cell21_989009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_989009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989009 prefixEnd_989009 := by exact prefixLift 989009
  have htrace : WordTrace (prefixWord ++ tailWord_989009) baseStart_989009 baseEnd_989009 := by
    simpa [prefixWord, tailWord_989009, baseEnd_989009] using wordTrace_append hprefix tailTrace_989009
  have hstable : (prefixWord ++ tailWord_989009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989009).length < 2 ^ (prefixWord ++ tailWord_989009).sum := by decide
  have hdescent : baseEnd_989009 < baseStart_989009 := by decide
  rcases family_descends (prefixWord ++ tailWord_989009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989108 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 4]
def baseStart_989108 : Nat := 118140960795 + 989108 * 2 ^ 59
def prefixEnd_989108 : Nat := 4983230072969 + 3 ^ 40 * 989108 * 2
def baseEnd_989108 : Nat := 225727921425520597378303

theorem tailTrace_989108 : CollatzResearch.WordTrace tailWord_989108 prefixEnd_989108 225727921425520597378303 := by
  unfold tailWord_989108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18037866250319058521303989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24050488333758744695071985 18037866250319058521303989)
  ·
    refine ⟨1691049960967411736372249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18037866250319058521303989 1691049960967411736372249)
    ·
      refine ⟨1268287470725558802279187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691049960967411736372249 1268287470725558802279187)
      ·
        refine ⟨1902431206088338203418781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268287470725558802279187 1902431206088338203418781)
        ·
          refine ⟨713411702283126826282043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1902431206088338203418781 713411702283126826282043)
          ·
            refine ⟨1070117553424690239423065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713411702283126826282043 1070117553424690239423065)
            ·
              refine ⟨802588165068517679567299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070117553424690239423065 802588165068517679567299)
              ·
                refine ⟨1203882247602776519350949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802588165068517679567299 1203882247602776519350949)
                ·
                  refine ⟨225727921425520597378303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203882247602776519350949 225727921425520597378303)
                  ·
                    rfl

theorem cell21_989108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_989108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989108 prefixEnd_989108 := by exact prefixLift 989108
  have htrace : WordTrace (prefixWord ++ tailWord_989108) baseStart_989108 baseEnd_989108 := by
    simpa [prefixWord, tailWord_989108, baseEnd_989108] using wordTrace_append hprefix tailTrace_989108
  have hstable : (prefixWord ++ tailWord_989108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989108).length < 2 ^ (prefixWord ++ tailWord_989108).sum := by decide
  have hdescent : baseEnd_989108 < baseStart_989108 := by decide
  rcases family_descends (prefixWord ++ tailWord_989108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989240 : List Nat := [2, 1, 2, 1, 7, 1, 2, 5]
def baseStart_989240 : Nat := 118140960795 + 989240 * 2 ^ 59
def prefixEnd_989240 : Nat := 4983230072969 + 3 ^ 40 * 989240 * 2
def baseEnd_989240 : Nat := 75252681874639233726011

theorem tailTrace_989240 : CollatzResearch.WordTrace tailWord_989240 prefixEnd_989240 75252681874639233726011 := by
  unfold tailWord_989240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040273468079951793206587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24053697957439935724275449 18040273468079951793206587)
  ·
    refine ⟨27060410202119927689809881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18040273468079951793206587 27060410202119927689809881)
    ·
      refine ⟨20295307651589945767357411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27060410202119927689809881 20295307651589945767357411)
      ·
        refine ⟨30442961477384918651036117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20295307651589945767357411 30442961477384918651036117)
        ·
          refine ⟨713506909626209030883659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30442961477384918651036117 713506909626209030883659)
          ·
            refine ⟨1070260364439313546325489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713506909626209030883659 1070260364439313546325489)
            ·
              refine ⟨802695273329485159744117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070260364439313546325489 802695273329485159744117)
              ·
                refine ⟨75252681874639233726011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 802695273329485159744117 75252681874639233726011)
                ·
                  rfl

theorem cell21_989240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_989240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989240 prefixEnd_989240 := by exact prefixLift 989240
  have htrace : WordTrace (prefixWord ++ tailWord_989240) baseStart_989240 baseEnd_989240 := by
    simpa [prefixWord, tailWord_989240, baseEnd_989240] using wordTrace_append hprefix tailTrace_989240
  have hstable : (prefixWord ++ tailWord_989240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989240).length < 2 ^ (prefixWord ++ tailWord_989240).sum := by decide
  have hdescent : baseEnd_989240 < baseStart_989240 := by decide
  rcases family_descends (prefixWord ++ tailWord_989240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989285 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 4]
def baseStart_989285 : Nat := 118140960795 + 989285 * 2 ^ 59
def prefixEnd_989285 : Nat := 4983230072969 + 3 ^ 40 * 989285 * 2
def baseEnd_989285 : Nat := 225768315237007622927941

theorem tailTrace_989285 : CollatzResearch.WordTrace tailWord_989285 prefixEnd_989285 225768315237007622927941 := by
  unfold tailWord_989285
  simp only [CollatzResearch.WordTrace]
  refine ⟨36082188220996876271801309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24054792147331250847867539 36082188220996876271801309)
  ·
    refine ⟨13530820582873828601925491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36082188220996876271801309 13530820582873828601925491)
    ·
      refine ⟨20296230874310742902888237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13530820582873828601925491 20296230874310742902888237)
      ·
        refine ⟨7611086577866528588583089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20296230874310742902888237 7611086577866528588583089)
        ·
          refine ⟨5708314933399896441437317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7611086577866528588583089 5708314933399896441437317)
          ·
            refine ⟨1070309050012480582769497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5708314933399896441437317 1070309050012480582769497)
            ·
              refine ⟨802731787509360437077123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070309050012480582769497 802731787509360437077123)
              ·
                refine ⟨1204097681264040655615685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802731787509360437077123 1204097681264040655615685)
                ·
                  refine ⟨225768315237007622927941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204097681264040655615685 225768315237007622927941)
                  ·
                    rfl

theorem cell21_989285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_989285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989285 prefixEnd_989285 := by exact prefixLift 989285
  have htrace : WordTrace (prefixWord ++ tailWord_989285) baseStart_989285 baseEnd_989285 := by
    simpa [prefixWord, tailWord_989285, baseEnd_989285] using wordTrace_append hprefix tailTrace_989285
  have hstable : (prefixWord ++ tailWord_989285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989285).length < 2 ^ (prefixWord ++ tailWord_989285).sum := by decide
  have hdescent : baseEnd_989285 < baseStart_989285 := by decide
  rcases family_descends (prefixWord ++ tailWord_989285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989330 : List Nat := [3, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_989330 : Nat := 118140960795 + 989330 * 2 ^ 59
def prefixEnd_989330 : Nat := 4983230072969 + 3 ^ 40 * 989330 * 2
def baseEnd_989330 : Nat := 225778584850097544677849

theorem tailTrace_989330 : CollatzResearch.WordTrace tailWord_989330 prefixEnd_989330 225778584850097544677849 := by
  unfold tailWord_989330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020957376458462239297361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24055886337222565971459629 9020957376458462239297361)
  ·
    refine ⟨6765718032343846679473021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9020957376458462239297361 6765718032343846679473021)
    ·
      refine ⟨2537144262128942504802383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6765718032343846679473021 2537144262128942504802383)
      ·
        refine ⟨3805716393193413757203575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537144262128942504802383 3805716393193413757203575)
        ·
          refine ⟨5708574589790120635805363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805716393193413757203575 5708574589790120635805363)
          ·
            refine ⟨8562861884685180953708045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708574589790120635805363 8562861884685180953708045)
            ·
              refine ⟨3211073206756942857640517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8562861884685180953708045 3211073206756942857640517)
              ·
                refine ⟨602076226266926785807597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3211073206756942857640517 602076226266926785807597)
                ·
                  refine ⟨225778584850097544677849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602076226266926785807597 225778584850097544677849)
                  ·
                    rfl

theorem cell21_989330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_989330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989330 prefixEnd_989330 := by exact prefixLift 989330
  have htrace : WordTrace (prefixWord ++ tailWord_989330) baseStart_989330 baseEnd_989330 := by
    simpa [prefixWord, tailWord_989330, baseEnd_989330] using wordTrace_append hprefix tailTrace_989330
  have hstable : (prefixWord ++ tailWord_989330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989330).length < 2 ^ (prefixWord ++ tailWord_989330).sum := by decide
  have hdescent : baseEnd_989330 < baseStart_989330 := by decide
  rcases family_descends (prefixWord ++ tailWord_989330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989378 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_989378 : Nat := 118140960795 + 989378 * 2 ^ 59
def prefixEnd_989378 : Nat := 4983230072969 + 3 ^ 40 * 989378 * 2
def baseEnd_989378 : Nat := 225789539104060127877751

theorem tailTrace_989378 : CollatzResearch.WordTrace tailWord_989378 prefixEnd_989378 225789539104060127877751 := by
  unfold tailWord_989378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9021395052414988288734197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24057053473106635436624525 9021395052414988288734197)
  ·
    refine ⟨845755786163905152068831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9021395052414988288734197 845755786163905152068831)
    ·
      refine ⟨1268633679245857728103247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845755786163905152068831 1268633679245857728103247)
      ·
        refine ⟨1902950518868786592154871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268633679245857728103247 1902950518868786592154871)
        ·
          refine ⟨2854425778303179888232307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902950518868786592154871 2854425778303179888232307)
          ·
            refine ⟨4281638667454769832348461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854425778303179888232307 4281638667454769832348461)
            ·
              refine ⟨1605614500295538687130673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4281638667454769832348461 1605614500295538687130673)
              ·
                refine ⟨1204210875221654015348005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605614500295538687130673 1204210875221654015348005)
                ·
                  refine ⟨225789539104060127877751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204210875221654015348005 225789539104060127877751)
                  ·
                    rfl

theorem cell21_989378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_989378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989378 prefixEnd_989378 := by exact prefixLift 989378
  have htrace : WordTrace (prefixWord ++ tailWord_989378) baseStart_989378 baseEnd_989378 := by
    simpa [prefixWord, tailWord_989378, baseEnd_989378] using wordTrace_append hprefix tailTrace_989378
  have hstable : (prefixWord ++ tailWord_989378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989378).length < 2 ^ (prefixWord ++ tailWord_989378).sum := by decide
  have hdescent : baseEnd_989378 < baseStart_989378 := by decide
  rcases family_descends (prefixWord ++ tailWord_989378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989524 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_989524 : Nat := 118140960795 + 989524 * 2 ^ 59
def prefixEnd_989524 : Nat := 4983230072969 + 3 ^ 40 * 989524 * 2
def baseEnd_989524 : Nat := 225822858293196318444119

theorem tailTrace_989524 : CollatzResearch.WordTrace tailWord_989524 prefixEnd_989524 225822858293196318444119 := by
  unfold tailWord_989524
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045452633565510044875813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24060603511420680059834417 18045452633565510044875813)
  ·
    refine ⟨3383522368793533133414215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18045452633565510044875813 3383522368793533133414215)
    ·
      refine ⟨5075283553190299700121323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3383522368793533133414215 5075283553190299700121323)
      ·
        refine ⟨7612925329785449550181985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075283553190299700121323 7612925329785449550181985)
        ·
          refine ⟨5709693997339087162636489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7612925329785449550181985 5709693997339087162636489)
          ·
            refine ⟨4282270498004315371977367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5709693997339087162636489 4282270498004315371977367)
            ·
              refine ⟨6423405747006473057966051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282270498004315371977367 6423405747006473057966051)
              ·
                refine ⟨9635108620509709586949077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423405747006473057966051 9635108620509709586949077)
                ·
                  refine ⟨225822858293196318444119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9635108620509709586949077 225822858293196318444119)
                  ·
                    rfl

theorem cell21_989524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_989524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989524 prefixEnd_989524 := by exact prefixLift 989524
  have htrace : WordTrace (prefixWord ++ tailWord_989524) baseStart_989524 baseEnd_989524 := by
    simpa [prefixWord, tailWord_989524, baseEnd_989524] using wordTrace_append hprefix tailTrace_989524
  have hstable : (prefixWord ++ tailWord_989524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989524).length < 2 ^ (prefixWord ++ tailWord_989524).sum := by decide
  have hdescent : baseEnd_989524 < baseStart_989524 := by decide
  rcases family_descends (prefixWord ++ tailWord_989524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989541 : List Nat := [1, 3, 1, 3, 1, 3, 1, 5, 3]
def baseStart_989541 : Nat := 118140960795 + 989541 * 2 ^ 59
def prefixEnd_989541 : Nat := 4983230072969 + 3 ^ 40 * 989541 * 2
def baseEnd_989541 : Nat := 225826737924808066660751

theorem tailTrace_989541 : CollatzResearch.WordTrace tailWord_989541 prefixEnd_989541 225826737924808066660751 := by
  unfold tailWord_989541
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091525308069431993120477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24061016872046287995413651 36091525308069431993120477)
  ·
    refine ⟨13534321990526036997420179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36091525308069431993120477 13534321990526036997420179)
    ·
      refine ⟨20301482985789055496130269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13534321990526036997420179 20301482985789055496130269)
      ·
        refine ⟨7613056119670895811048851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20301482985789055496130269 7613056119670895811048851)
        ·
          refine ⟨11419584179506343716573277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613056119670895811048851 11419584179506343716573277)
          ·
            refine ⟨4282344067314878893714979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11419584179506343716573277 4282344067314878893714979)
            ·
              refine ⟨6423516100972318340572469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282344067314878893714979 6423516100972318340572469)
              ·
                refine ⟨602204634466154844428669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6423516100972318340572469 602204634466154844428669)
                ·
                  refine ⟨225826737924808066660751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602204634466154844428669 225826737924808066660751)
                  ·
                    rfl

theorem cell21_989541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_989541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989541 prefixEnd_989541 := by exact prefixLift 989541
  have htrace : WordTrace (prefixWord ++ tailWord_989541) baseStart_989541 baseEnd_989541 := by
    simpa [prefixWord, tailWord_989541, baseEnd_989541] using wordTrace_append hprefix tailTrace_989541
  have hstable : (prefixWord ++ tailWord_989541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989541).length < 2 ^ (prefixWord ++ tailWord_989541).sum := by decide
  have hdescent : baseEnd_989541 < baseStart_989541 := by decide
  rcases family_descends (prefixWord ++ tailWord_989541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989572 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_989572 : Nat := 118140960795 + 989572 * 2 ^ 59
def prefixEnd_989572 : Nat := 4983230072969 + 3 ^ 40 * 989572 * 2
def baseEnd_989572 : Nat := 225833812547158901644021

theorem tailTrace_989572 : CollatzResearch.WordTrace tailWord_989572 prefixEnd_989572 225833812547158901644021 := by
  unfold tailWord_989572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18046327985478562143749485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24061770647304749524999313 18046327985478562143749485)
  ·
    refine ⟨6767372994554460803906057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18046327985478562143749485 6767372994554460803906057)
    ·
      refine ⟨5075529745915845602929543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6767372994554460803906057 5075529745915845602929543)
      ·
        refine ⟨7613294618873768404394315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075529745915845602929543 7613294618873768404394315)
        ·
          refine ⟨11419941928310652606591473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613294618873768404394315 11419941928310652606591473)
          ·
            refine ⟨8564956446232989454943605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11419941928310652606591473 8564956446232989454943605)
            ·
              refine ⟨802964666834342761400963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8564956446232989454943605 802964666834342761400963)
              ·
                refine ⟨1204447000251514142101445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802964666834342761400963 1204447000251514142101445)
                ·
                  refine ⟨225833812547158901644021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204447000251514142101445 225833812547158901644021)
                  ·
                    rfl

theorem cell21_989572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_989572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989572 prefixEnd_989572 := by exact prefixLift 989572
  have htrace : WordTrace (prefixWord ++ tailWord_989572) baseStart_989572 baseEnd_989572 := by
    simpa [prefixWord, tailWord_989572, baseEnd_989572] using wordTrace_append hprefix tailTrace_989572
  have hstable : (prefixWord ++ tailWord_989572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989572).length < 2 ^ (prefixWord ++ tailWord_989572).sum := by decide
  have hdescent : baseEnd_989572 < baseStart_989572 := by decide
  rcases family_descends (prefixWord ++ tailWord_989572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989617 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 5]
def baseStart_989617 : Nat := 118140960795 + 989617 * 2 ^ 59
def prefixEnd_989617 : Nat := 4983230072969 + 3 ^ 40 * 989617 * 2
def baseEnd_989617 : Nat := 225844082160248823393929

theorem tailTrace_989617 : CollatzResearch.WordTrace tailWord_989617 prefixEnd_989617 225844082160248823393929 := by
  unfold tailWord_989617
  simp only [CollatzResearch.WordTrace]
  refine ⟨36094297255794096972887105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24062864837196064648591403 36094297255794096972887105)
  ·
    refine ⟨27070722941845572729665329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36094297255794096972887105 27070722941845572729665329)
    ·
      refine ⟨20303042206384179547248997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27070722941845572729665329 20303042206384179547248997)
      ·
        refine ⟨3806820413697033665109187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20303042206384179547248997 3806820413697033665109187)
        ·
          refine ⟨5710230620545550497663781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806820413697033665109187 5710230620545550497663781)
          ·
            refine ⟨1070668241352290718311959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5710230620545550497663781 1070668241352290718311959)
            ·
              refine ⟨1606002362028436077467939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070668241352290718311959 1606002362028436077467939)
              ·
                refine ⟨2409003543042654116201909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606002362028436077467939 2409003543042654116201909)
                ·
                  refine ⟨225844082160248823393929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2409003543042654116201909 225844082160248823393929)
                  ·
                    rfl

theorem cell21_989617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_989617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989617 prefixEnd_989617 := by exact prefixLift 989617
  have htrace : WordTrace (prefixWord ++ tailWord_989617) baseStart_989617 baseEnd_989617 := by
    simpa [prefixWord, tailWord_989617, baseEnd_989617] using wordTrace_append hprefix tailTrace_989617
  have hstable : (prefixWord ++ tailWord_989617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989617).length < 2 ^ (prefixWord ++ tailWord_989617).sum := by decide
  have hdescent : baseEnd_989617 < baseStart_989617 := by decide
  rcases family_descends (prefixWord ++ tailWord_989617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989620 : List Nat := [2, 5, 2, 2, 1, 1, 2, 6]
def baseStart_989620 : Nat := 118140960795 + 989620 * 2 ^ 59
def prefixEnd_989620 : Nat := 4983230072969 + 3 ^ 40 * 989620 * 2
def baseEnd_989620 : Nat := 75281588933707161614641

theorem tailTrace_989620 : CollatzResearch.WordTrace tailWord_989620 prefixEnd_989620 75281588933707161614641 := by
  unfold tailWord_989620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047203337391614242623157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24062937783188818990164209 18047203337391614242623157)
  ·
    refine ⟨1691925312880463835245921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18047203337391614242623157 1691925312880463835245921)
    ·
      refine ⟨1268943984660347876434441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691925312880463835245921 1268943984660347876434441)
      ·
        refine ⟨951707988495260907325831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268943984660347876434441 951707988495260907325831)
        ·
          refine ⟨1427561982742891360988747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951707988495260907325831 1427561982742891360988747)
          ·
            refine ⟨2141342974114337041483121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427561982742891360988747 2141342974114337041483121)
            ·
              refine ⟨1606007230585752781112341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141342974114337041483121 1606007230585752781112341)
              ·
                refine ⟨75281588933707161614641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1606007230585752781112341 75281588933707161614641)
                ·
                  rfl

theorem cell21_989620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_989620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989620 prefixEnd_989620 := by exact prefixLift 989620
  have htrace : WordTrace (prefixWord ++ tailWord_989620) baseStart_989620 baseEnd_989620 := by
    simpa [prefixWord, tailWord_989620, baseEnd_989620] using wordTrace_append hprefix tailTrace_989620
  have hstable : (prefixWord ++ tailWord_989620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989620).length < 2 ^ (prefixWord ++ tailWord_989620).sum := by decide
  have hdescent : baseEnd_989620 < baseStart_989620 := by decide
  rcases family_descends (prefixWord ++ tailWord_989620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989710 : List Nat := [4, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_989710 : Nat := 118140960795 + 989710 * 2 ^ 59
def prefixEnd_989710 : Nat := 4983230072969 + 3 ^ 40 * 989710 * 2
def baseEnd_989710 : Nat := 225865306027301328343739

theorem tailTrace_989710 : CollatzResearch.WordTrace tailWord_989710 prefixEnd_989710 225865306027301328343739 := by
  unfold tailWord_989710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512211155557146732002823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24065126162971449237348389 4512211155557146732002823)
  ·
    refine ⟨6768316733335720098004235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4512211155557146732002823 6768316733335720098004235)
    ·
      refine ⟨10152475100003580147006353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768316733335720098004235 10152475100003580147006353)
      ·
        refine ⟨7614356325002685110254765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10152475100003580147006353 7614356325002685110254765)
        ·
          refine ⟨2855383621876006916345537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7614356325002685110254765 2855383621876006916345537)
          ·
            refine ⟨2141537716407005187259153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2855383621876006916345537 2141537716407005187259153)
            ·
              refine ⟨1606153287305253890444365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141537716407005187259153 1606153287305253890444365)
              ·
                refine ⟨602307482739470208916637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1606153287305253890444365 602307482739470208916637)
                ·
                  refine ⟨225865306027301328343739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602307482739470208916637 225865306027301328343739)
                  ·
                    rfl

theorem cell21_989710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_989710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989710 prefixEnd_989710 := by exact prefixLift 989710
  have htrace : WordTrace (prefixWord ++ tailWord_989710) baseStart_989710 baseEnd_989710 := by
    simpa [prefixWord, tailWord_989710, baseEnd_989710] using wordTrace_append hprefix tailTrace_989710
  have hstable : (prefixWord ++ tailWord_989710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989710).length < 2 ^ (prefixWord ++ tailWord_989710).sum := by decide
  have hdescent : baseEnd_989710 < baseStart_989710 := by decide
  rcases family_descends (prefixWord ++ tailWord_989710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989724 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_989724 : Nat := 118140960795 + 989724 * 2 ^ 59
def prefixEnd_989724 : Nat := 4983230072969 + 3 ^ 40 * 989724 * 2
def baseEnd_989724 : Nat := 225868501018040415110377

theorem tailTrace_989724 : CollatzResearch.WordTrace tailWord_989724 prefixEnd_989724 225868501018040415110377 := by
  unfold tailWord_989724
  simp only [CollatzResearch.WordTrace]
  refine ⟨18049099933203227123516113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24065466577604302831354817 18049099933203227123516113)
  ·
    refine ⟨13536824949902420342637085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18049099933203227123516113 13536824949902420342637085)
    ·
      refine ⟨5076309356213407628488907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13536824949902420342637085 5076309356213407628488907)
      ·
        refine ⟨7614464034320111442733361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076309356213407628488907 7614464034320111442733361)
        ·
          refine ⟨5710848025740083582050021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7614464034320111442733361 5710848025740083582050021)
          ·
            refine ⟨1070784004826265671634379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5710848025740083582050021 1070784004826265671634379)
            ·
              refine ⟨1606176007239398507451569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070784004826265671634379 1606176007239398507451569)
              ·
                refine ⟨1204632005429548880588677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606176007239398507451569 1204632005429548880588677)
                ·
                  refine ⟨225868501018040415110377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204632005429548880588677 225868501018040415110377)
                  ·
                    rfl

theorem cell21_989724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_989724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989724 prefixEnd_989724 := by exact prefixLift 989724
  have htrace : WordTrace (prefixWord ++ tailWord_989724) baseStart_989724 baseEnd_989724 := by
    simpa [prefixWord, tailWord_989724, baseEnd_989724] using wordTrace_append hprefix tailTrace_989724
  have hstable : (prefixWord ++ tailWord_989724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989724).length < 2 ^ (prefixWord ++ tailWord_989724).sum := by decide
  have hdescent : baseEnd_989724 < baseStart_989724 := by decide
  rcases family_descends (prefixWord ++ tailWord_989724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989800 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_989800 : Nat := 118140960795 + 989800 * 2 ^ 59
def prefixEnd_989800 : Nat := 4983230072969 + 3 ^ 40 * 989800 * 2
def baseEnd_989800 : Nat := 225885845253481171843555

theorem tailTrace_989800 : CollatzResearch.WordTrace tailWord_989800 prefixEnd_989800 225885845253481171843555 := by
  unfold tailWord_989800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050485907065559613399427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24067314542754079484532569 18050485907065559613399427)
  ·
    refine ⟨27075728860598339420099141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18050485907065559613399427 27075728860598339420099141)
    ·
      refine ⟨5076699161362188641268589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27075728860598339420099141 5076699161362188641268589)
      ·
        refine ⟨1903762185510820740475721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5076699161362188641268589 1903762185510820740475721)
        ·
          refine ⟨1427821639133115555356791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1903762185510820740475721 1427821639133115555356791)
          ·
            refine ⟨2141732458699673333035187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427821639133115555356791 2141732458699673333035187)
            ·
              refine ⟨3212598688049509999552781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141732458699673333035187 3212598688049509999552781)
              ·
                refine ⟨1204724508018566249832293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3212598688049509999552781 1204724508018566249832293)
                ·
                  refine ⟨225885845253481171843555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204724508018566249832293 225885845253481171843555)
                  ·
                    rfl

theorem cell21_989800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_989800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989800 prefixEnd_989800 := by exact prefixLift 989800
  have htrace : WordTrace (prefixWord ++ tailWord_989800) baseStart_989800 baseEnd_989800 := by
    simpa [prefixWord, tailWord_989800, baseEnd_989800] using wordTrace_append hprefix tailTrace_989800
  have hstable : (prefixWord ++ tailWord_989800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989800).length < 2 ^ (prefixWord ++ tailWord_989800).sum := by decide
  have hdescent : baseEnd_989800 < baseStart_989800 := by decide
  rcases family_descends (prefixWord ++ tailWord_989800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989938 : List Nat := [3, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_989938 : Nat := 118140960795 + 989938 * 2 ^ 59
def prefixEnd_989938 : Nat := 4983230072969 + 3 ^ 40 * 989938 * 2
def baseEnd_989938 : Nat := 225917338733623598543273

theorem tailTrace_989938 : CollatzResearch.WordTrace tailWord_989938 prefixEnd_989938 225917338733623598543273 := by
  unfold tailWord_989938
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026501271907792198830617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24070670058420779196881645 9026501271907792198830617)
  ·
    refine ⟨6769875953930844149122963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9026501271907792198830617 6769875953930844149122963)
    ·
      refine ⟨10154813930896266223684445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6769875953930844149122963 10154813930896266223684445)
      ·
        refine ⟨3808055224086099833881667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10154813930896266223684445 3808055224086099833881667)
        ·
          refine ⟨5712082836129149750822501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808055224086099833881667 5712082836129149750822501)
          ·
            refine ⟨1071015531774215578279219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5712082836129149750822501 1071015531774215578279219)
            ·
              refine ⟨1606523297661323367418829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071015531774215578279219 1606523297661323367418829)
              ·
                refine ⟨602446236622996262782061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1606523297661323367418829 602446236622996262782061)
                ·
                  refine ⟨225917338733623598543273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602446236622996262782061 225917338733623598543273)
                  ·
                    rfl

theorem cell21_989938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_989938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989938 prefixEnd_989938 := by exact prefixLift 989938
  have htrace : WordTrace (prefixWord ++ tailWord_989938) baseStart_989938 baseEnd_989938 := by
    simpa [prefixWord, tailWord_989938, baseEnd_989938] using wordTrace_append hprefix tailTrace_989938
  have hstable : (prefixWord ++ tailWord_989938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989938).length < 2 ^ (prefixWord ++ tailWord_989938).sum := by decide
  have hdescent : baseEnd_989938 < baseStart_989938 := by decide
  rcases family_descends (prefixWord ++ tailWord_989938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989977 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 8]
def baseStart_989977 : Nat := 118140960795 + 989977 * 2 ^ 59
def prefixEnd_989977 : Nat := 4983230072969 + 3 ^ 40 * 989977 * 2
def baseEnd_989977 : Nat := 225926239064968197393193

theorem tailTrace_989977 : CollatzResearch.WordTrace tailWord_989977 prefixEnd_989977 225926239064968197393193 := by
  unfold tailWord_989977
  simp only [CollatzResearch.WordTrace]
  refine ⟨36107427534489878455992185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24071618356326585637328123 36107427534489878455992185)
  ·
    refine ⟨27080570650867408841994139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36107427534489878455992185 27080570650867408841994139)
    ·
      refine ⟨40620855976301113262991209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27080570650867408841994139 40620855976301113262991209)
      ·
        refine ⟨30465641982225834947243407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40620855976301113262991209 30465641982225834947243407)
        ·
          refine ⟨45698462973338752420865111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30465641982225834947243407 45698462973338752420865111)
          ·
            refine ⟨68547694460008128631297667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45698462973338752420865111 68547694460008128631297667)
            ·
              refine ⟨102821541690012192946946501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68547694460008128631297667 102821541690012192946946501)
              ·
                refine ⟨19279039066877286177552469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102821541690012192946946501 19279039066877286177552469)
                ·
                  refine ⟨225926239064968197393193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19279039066877286177552469 225926239064968197393193)
                  ·
                    rfl

theorem cell21_989977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_989977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_989977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_989977 prefixEnd_989977 := by exact prefixLift 989977
  have htrace : WordTrace (prefixWord ++ tailWord_989977) baseStart_989977 baseEnd_989977 := by
    simpa [prefixWord, tailWord_989977, baseEnd_989977] using wordTrace_append hprefix tailTrace_989977
  have hstable : (prefixWord ++ tailWord_989977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989977).length < 2 ^ (prefixWord ++ tailWord_989977).sum := by decide
  have hdescent : baseEnd_989977 < baseStart_989977 := by decide
  rcases family_descends (prefixWord ++ tailWord_989977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990014 : List Nat := [4, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_990014 : Nat := 118140960795 + 990014 * 2 ^ 59
def prefixEnd_990014 : Nat := 4983230072969 + 3 ^ 40 * 990014 * 2
def baseEnd_990014 : Nat := 225934682969064355276451

theorem tailTrace_990014 : CollatzResearch.WordTrace tailWord_990014 prefixEnd_990014 225934682969064355276451 := by
  unfold tailWord_990014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513597129419479221886137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24072518023570555850059397 4513597129419479221886137)
  ·
    refine ⟨3385197847064609416414603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4513597129419479221886137 3385197847064609416414603)
    ·
      refine ⟨5077796770596914124621905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385197847064609416414603 5077796770596914124621905)
      ·
        refine ⟨3808347577947685593466429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5077796770596914124621905 3808347577947685593466429)
        ·
          refine ⟨1428130341730382097549911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3808347577947685593466429 1428130341730382097549911)
          ·
            refine ⟨2142195512595573146324867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428130341730382097549911 2142195512595573146324867)
            ·
              refine ⟨3213293268893359719487301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142195512595573146324867 3213293268893359719487301)
              ·
                refine ⟨602492487917504947403869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3213293268893359719487301 602492487917504947403869)
                ·
                  refine ⟨225934682969064355276451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602492487917504947403869 225934682969064355276451)
                  ·
                    rfl

theorem cell21_990014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_990014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990014 prefixEnd_990014 := by exact prefixLift 990014
  have htrace : WordTrace (prefixWord ++ tailWord_990014) baseStart_990014 baseEnd_990014 := by
    simpa [prefixWord, tailWord_990014, baseEnd_990014] using wordTrace_append hprefix tailTrace_990014
  have hstable : (prefixWord ++ tailWord_990014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990014).length < 2 ^ (prefixWord ++ tailWord_990014).sum := by decide
  have hdescent : baseEnd_990014 < baseStart_990014 := by decide
  rcases family_descends (prefixWord ++ tailWord_990014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990025 : List Nat := [1, 2, 1, 1, 2, 7, 1, 6]
def baseStart_990025 : Nat := 118140960795 + 990025 * 2 ^ 59
def prefixEnd_990025 : Nat := 4983230072969 + 3 ^ 40 * 990025 * 2
def baseEnd_990025 : Nat := 75312397772976926864365

theorem tailTrace_990025 : CollatzResearch.WordTrace tailWord_990025 prefixEnd_990025 75312397772976926864365 := by
  unfold tailWord_990025
  simp only [CollatzResearch.WordTrace]
  refine ⟨36109178238315982653739529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24072785492210655102493019 36109178238315982653739529)
  ·
    refine ⟨27081883678736986990304647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36109178238315982653739529 27081883678736986990304647)
    ·
      refine ⟨40622825518105480485456971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27081883678736986990304647 40622825518105480485456971)
      ·
        refine ⟨60934238277158220728185457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40622825518105480485456971 60934238277158220728185457)
        ·
          refine ⟨45700678707868665546139093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60934238277158220728185457 45700678707868665546139093)
          ·
            refine ⟨1071109657215671848737635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45700678707868665546139093 1071109657215671848737635)
            ·
              refine ⟨1606664485823507773106453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071109657215671848737635 1606664485823507773106453)
              ·
                refine ⟨75312397772976926864365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1606664485823507773106453 75312397772976926864365)
                ·
                  rfl

theorem cell21_990025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 6].length) (baseStart_990025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990025 prefixEnd_990025 := by exact prefixLift 990025
  have htrace : WordTrace (prefixWord ++ tailWord_990025) baseStart_990025 baseEnd_990025 := by
    simpa [prefixWord, tailWord_990025, baseEnd_990025] using wordTrace_append hprefix tailTrace_990025
  have hstable : (prefixWord ++ tailWord_990025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990025).length < 2 ^ (prefixWord ++ tailWord_990025).sum := by decide
  have hdescent : baseEnd_990025 < baseStart_990025 := by decide
  rcases family_descends (prefixWord ++ tailWord_990025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990039 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 7]
def baseStart_990039 : Nat := 118140960795 + 990039 * 2 ^ 59
def prefixEnd_990039 : Nat := 4983230072969 + 3 ^ 40 * 990039 * 2
def baseEnd_990039 : Nat := 225940388309669867359733

theorem tailTrace_990039 : CollatzResearch.WordTrace tailWord_990039 prefixEnd_990039 225940388309669867359733 := by
  unfold tailWord_990039
  simp only [CollatzResearch.WordTrace]
  refine ⟨36109688860265263044749171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24073125906843508696499447 36109688860265263044749171)
  ·
    refine ⟨54164533290397894567123757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36109688860265263044749171 54164533290397894567123757)
    ·
      refine ⟨20311699983899210462671409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54164533290397894567123757 20311699983899210462671409)
      ·
        refine ⟨15233774987924407847003557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20311699983899210462671409 15233774987924407847003557)
        ·
          refine ⟨2856332810235826471313167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15233774987924407847003557 2856332810235826471313167)
          ·
            refine ⟨4284499215353739706969751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856332810235826471313167 4284499215353739706969751)
            ·
              refine ⟨6426748823030609560454627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284499215353739706969751 6426748823030609560454627)
              ·
                refine ⟨9640123234545914340681941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426748823030609560454627 9640123234545914340681941)
                ·
                  refine ⟨225940388309669867359733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9640123234545914340681941 225940388309669867359733)
                  ·
                    rfl

theorem cell21_990039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_990039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990039 prefixEnd_990039 := by exact prefixLift 990039
  have htrace : WordTrace (prefixWord ++ tailWord_990039) baseStart_990039 baseEnd_990039 := by
    simpa [prefixWord, tailWord_990039, baseEnd_990039] using wordTrace_append hprefix tailTrace_990039
  have hstable : (prefixWord ++ tailWord_990039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990039).length < 2 ^ (prefixWord ++ tailWord_990039).sum := by decide
  have hdescent : baseEnd_990039 < baseStart_990039 := by decide
  rcases family_descends (prefixWord ++ tailWord_990039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990084 : List Nat := [2, 3, 2, 1, 1, 1, 1, 10]
def baseStart_990084 : Nat := 118140960795 + 990084 * 2 ^ 59
def prefixEnd_990084 : Nat := 4983230072969 + 3 ^ 40 * 990084 * 2
def baseEnd_990084 : Nat := 75316885974253263036547

theorem tailTrace_990084 : CollatzResearch.WordTrace tailWord_990084 prefixEnd_990084 75316885974253263036547 := by
  unfold tailWord_990084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055665072551117865068653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24074220096734823820091537 18055665072551117865068653)
  ·
    refine ⟨6770874402206669199400745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18055665072551117865068653 6770874402206669199400745)
    ·
      refine ⟨5078155801655001899550559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6770874402206669199400745 5078155801655001899550559)
      ·
        refine ⟨7617233702482502849325839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078155801655001899550559 7617233702482502849325839)
        ·
          refine ⟨11425850553723754273988759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617233702482502849325839 11425850553723754273988759)
          ·
            refine ⟨17138775830585631410983139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425850553723754273988759 17138775830585631410983139)
            ·
              refine ⟨25708163745878447116474709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17138775830585631410983139 25708163745878447116474709)
              ·
                refine ⟨75316885974253263036547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25708163745878447116474709 75316885974253263036547)
                ·
                  rfl

theorem cell21_990084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_990084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990084 prefixEnd_990084 := by exact prefixLift 990084
  have htrace : WordTrace (prefixWord ++ tailWord_990084) baseStart_990084 baseEnd_990084 := by
    simpa [prefixWord, tailWord_990084, baseEnd_990084] using wordTrace_append hprefix tailTrace_990084
  have hstable : (prefixWord ++ tailWord_990084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990084).length < 2 ^ (prefixWord ++ tailWord_990084).sum := by decide
  have hdescent : baseEnd_990084 < baseStart_990084 := by decide
  rcases family_descends (prefixWord ++ tailWord_990084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990101 : List Nat := [1, 3, 2, 1, 1, 4, 4, 5]
def baseStart_990101 : Nat := 118140960795 + 990101 * 2 ^ 59
def prefixEnd_990101 : Nat := 4983230072969 + 3 ^ 40 * 990101 * 2
def baseEnd_990101 : Nat := 75318179184790512442091

theorem tailTrace_990101 : CollatzResearch.WordTrace tailWord_990101 prefixEnd_990101 75318179184790512442091 := by
  unfold tailWord_990101
  simp only [CollatzResearch.WordTrace]
  refine ⟨36111950186040647633506157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24074633457360431755670771 36111950186040647633506157)
  ·
    refine ⟨13541981319765242862564809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36111950186040647633506157 13541981319765242862564809)
    ·
      refine ⟨10156485989823932146923607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13541981319765242862564809 10156485989823932146923607)
      ·
        refine ⟨15234728984735898220385411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156485989823932146923607 15234728984735898220385411)
        ·
          refine ⟨22852093477103847330578117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234728984735898220385411 22852093477103847330578117)
          ·
            refine ⟨4284767526956971374483397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22852093477103847330578117 4284767526956971374483397)
            ·
              refine ⟨803393911304432132715637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4284767526956971374483397 803393911304432132715637)
              ·
                refine ⟨75318179184790512442091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 803393911304432132715637 75318179184790512442091)
                ·
                  rfl

theorem cell21_990101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 5].length) (baseStart_990101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990101 prefixEnd_990101 := by exact prefixLift 990101
  have htrace : WordTrace (prefixWord ++ tailWord_990101) baseStart_990101 baseEnd_990101 := by
    simpa [prefixWord, tailWord_990101, baseEnd_990101] using wordTrace_append hprefix tailTrace_990101
  have hstable : (prefixWord ++ tailWord_990101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990101).length < 2 ^ (prefixWord ++ tailWord_990101).sum := by decide
  have hdescent : baseEnd_990101 < baseStart_990101 := by decide
  rcases family_descends (prefixWord ++ tailWord_990101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990205 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 8]
def baseStart_990205 : Nat := 118140960795 + 990205 * 2 ^ 59
def prefixEnd_990205 : Nat := 4983230072969 + 3 ^ 40 * 990205 * 2
def baseEnd_990205 : Nat := 225978271771290467592727

theorem tailTrace_990205 : CollatzResearch.WordTrace tailWord_990205 prefixEnd_990205 225978271771290467592727 := by
  unfold tailWord_990205
  simp only [CollatzResearch.WordTrace]
  refine ⟨36115743377663873395292069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24077162251775915596861379 36115743377663873395292069)
  ·
    refine ⟨6771701883311976261617263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36115743377663873395292069 6771701883311976261617263)
    ·
      refine ⟨10157552824967964392425895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6771701883311976261617263 10157552824967964392425895)
      ·
        refine ⟨15236329237451946588638843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157552824967964392425895 15236329237451946588638843)
        ·
          refine ⟨22854493856177919882958265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236329237451946588638843 22854493856177919882958265)
          ·
            refine ⟨17140870392133439912218699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22854493856177919882958265 17140870392133439912218699)
            ·
              refine ⟨25711305588200159868328049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17140870392133439912218699 25711305588200159868328049)
              ·
                refine ⟨19283479191150119901246037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25711305588200159868328049 19283479191150119901246037)
                ·
                  refine ⟨225978271771290467592727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19283479191150119901246037 225978271771290467592727)
                  ·
                    rfl

theorem cell21_990205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_990205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990205 prefixEnd_990205 := by exact prefixLift 990205
  have htrace : WordTrace (prefixWord ++ tailWord_990205) baseStart_990205 baseEnd_990205 := by
    simpa [prefixWord, tailWord_990205, baseEnd_990205] using wordTrace_append hprefix tailTrace_990205
  have hstable : (prefixWord ++ tailWord_990205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990205).length < 2 ^ (prefixWord ++ tailWord_990205).sum := by decide
  have hdescent : baseEnd_990205 < baseStart_990205 := by decide
  rcases family_descends (prefixWord ++ tailWord_990205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990239 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 4]
def baseStart_990239 : Nat := 118140960795 + 990239 * 2 ^ 59
def prefixEnd_990239 : Nat := 4983230072969 + 3 ^ 40 * 990239 * 2
def baseEnd_990239 : Nat := 225986031034513964025991

theorem tailTrace_990239 : CollatzResearch.WordTrace tailWord_990239 prefixEnd_990239 225986031034513964025991 := by
  unfold tailWord_990239
  simp only [CollatzResearch.WordTrace]
  refine ⟨36116983459540697202029771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24077988973027131468019847 36116983459540697202029771)
  ·
    refine ⟨54175475189311045803044657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36116983459540697202029771 54175475189311045803044657)
    ·
      refine ⟨40631606391983284352283493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54175475189311045803044657 40631606391983284352283493)
      ·
        refine ⟨7618426198496865816053155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40631606391983284352283493 7618426198496865816053155)
        ·
          refine ⟨11427639297745298724079733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618426198496865816053155 11427639297745298724079733)
          ·
            refine ⟨1071341184163621755382475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11427639297745298724079733 1071341184163621755382475)
            ·
              refine ⟨1607011776245432633073713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071341184163621755382475 1607011776245432633073713)
              ·
                refine ⟨1205258832184074474805285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607011776245432633073713 1205258832184074474805285)
                ·
                  refine ⟨225986031034513964025991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205258832184074474805285 225986031034513964025991)
                  ·
                    rfl

theorem cell21_990239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 4].length) (baseStart_990239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990239 prefixEnd_990239 := by exact prefixLift 990239
  have htrace : WordTrace (prefixWord ++ tailWord_990239) baseStart_990239 baseEnd_990239 := by
    simpa [prefixWord, tailWord_990239, baseEnd_990239] using wordTrace_append hprefix tailTrace_990239
  have hstable : (prefixWord ++ tailWord_990239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990239).length < 2 ^ (prefixWord ++ tailWord_990239).sum := by decide
  have hdescent : baseEnd_990239 < baseStart_990239 := by decide
  rcases family_descends (prefixWord ++ tailWord_990239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990270 : List Nat := [4, 2, 1, 3, 1, 1, 4, 5]
def baseStart_990270 : Nat := 118140960795 + 990270 * 2 ^ 59
def prefixEnd_990270 : Nat := 4983230072969 + 3 ^ 40 * 990270 * 2
def baseEnd_990270 : Nat := 75331035218954933003087

theorem tailTrace_990270 : CollatzResearch.WordTrace tailWord_990270 prefixEnd_990270 75331035218954933003087 := by
  unfold tailWord_990270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514764265303548687051033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24078742748285592997605509 4514764265303548687051033)
  ·
    refine ⟨3386073198977661515288275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4514764265303548687051033 3386073198977661515288275)
    ·
      refine ⟨5079109798466492272932413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3386073198977661515288275 5079109798466492272932413)
      ·
        refine ⟨1904666174424934602349655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5079109798466492272932413 1904666174424934602349655)
        ·
          refine ⟨2856999261637401903524483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904666174424934602349655 2856999261637401903524483)
          ·
            refine ⟨4285498892456102855286725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856999261637401903524483 4285498892456102855286725)
            ·
              refine ⟨803531042335519285366261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4285498892456102855286725 803531042335519285366261)
              ·
                refine ⟨75331035218954933003087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 803531042335519285366261 75331035218954933003087)
                ·
                  rfl

theorem cell21_990270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_990270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990270 prefixEnd_990270 := by exact prefixLift 990270
  have htrace : WordTrace (prefixWord ++ tailWord_990270) baseStart_990270 baseEnd_990270 := by
    simpa [prefixWord, tailWord_990270, baseEnd_990270] using wordTrace_append hprefix tailTrace_990270
  have hstable : (prefixWord ++ tailWord_990270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990270).length < 2 ^ (prefixWord ++ tailWord_990270).sum := by decide
  have hdescent : baseEnd_990270 < baseStart_990270 := by decide
  rcases family_descends (prefixWord ++ tailWord_990270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990439 : List Nat := [1, 1, 5, 3, 3, 1, 2, 5]
def baseStart_990439 : Nat := 118140960795 + 990439 * 2 ^ 59
def prefixEnd_990439 : Nat := 4983230072969 + 3 ^ 40 * 990439 * 2
def baseEnd_990439 : Nat := 75343891253119353564083

theorem tailTrace_990439 : CollatzResearch.WordTrace tailWord_990439 prefixEnd_990439 75343891253119353564083 := by
  unfold tailWord_990439
  simp only [CollatzResearch.WordTrace]
  refine ⟨36124278058816131359310371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24082852039210754239540247 36124278058816131359310371)
  ·
    refine ⟨54186417088224197038965557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36124278058816131359310371 54186417088224197038965557)
    ·
      refine ⟨5079976602021018472403021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54186417088224197038965557 5079976602021018472403021)
      ·
        refine ⟨1904991225757881927151133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5079976602021018472403021 1904991225757881927151133)
        ·
          refine ⟨714371709659205722681675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1904991225757881927151133 714371709659205722681675)
          ·
            refine ⟨1071557564488808584022513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714371709659205722681675 1071557564488808584022513)
            ·
              refine ⟨803668173366606438016885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071557564488808584022513 803668173366606438016885)
              ·
                refine ⟨75343891253119353564083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 803668173366606438016885 75343891253119353564083)
                ·
                  rfl

theorem cell21_990439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 5].length) (baseStart_990439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990439 prefixEnd_990439 := by exact prefixLift 990439
  have htrace : WordTrace (prefixWord ++ tailWord_990439) baseStart_990439 baseEnd_990439 := by
    simpa [prefixWord, tailWord_990439, baseEnd_990439] using wordTrace_append hprefix tailTrace_990439
  have hstable : (prefixWord ++ tailWord_990439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990439).length < 2 ^ (prefixWord ++ tailWord_990439).sum := by decide
  have hdescent : baseEnd_990439 < baseStart_990439 := by decide
  rcases family_descends (prefixWord ++ tailWord_990439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990529 : List Nat := [1, 2, 5, 2, 1, 2, 1, 4, 3]
def baseStart_990529 : Nat := 118140960795 + 990529 * 2 ^ 59
def prefixEnd_990529 : Nat := 4983230072969 + 3 ^ 40 * 990529 * 2
def baseEnd_990529 : Nat := 226052212985537904192065

theorem tailTrace_990529 : CollatzResearch.WordTrace tailWord_990529 prefixEnd_990529 226052212985537904192065 := by
  unfold tailWord_990529
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127560628490076730086641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24085040418993384486724427 36127560628490076730086641)
  ·
    refine ⟨27095670471367557547564981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36127560628490076730086641 27095670471367557547564981)
    ·
      refine ⟨2540219106690708520084217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27095670471367557547564981 2540219106690708520084217)
      ·
        refine ⟨1905164330018031390063163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2540219106690708520084217 1905164330018031390063163)
        ·
          refine ⟨2857746495027047085094745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905164330018031390063163 2857746495027047085094745)
          ·
            refine ⟨2143309871270285313821059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857746495027047085094745 2143309871270285313821059)
            ·
              refine ⟨3214964806905427970731589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143309871270285313821059 3214964806905427970731589)
              ·
                refine ⟨602805901294767744512173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3214964806905427970731589 602805901294767744512173)
                ·
                  refine ⟨226052212985537904192065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602805901294767744512173 226052212985537904192065)
                  ·
                    rfl

theorem cell21_990529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_990529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990529 prefixEnd_990529 := by exact prefixLift 990529
  have htrace : WordTrace (prefixWord ++ tailWord_990529) baseStart_990529 baseEnd_990529 := by
    simpa [prefixWord, tailWord_990529, baseEnd_990529] using wordTrace_append hprefix tailTrace_990529
  have hstable : (prefixWord ++ tailWord_990529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990529).length < 2 ^ (prefixWord ++ tailWord_990529).sum := by decide
  have hdescent : baseEnd_990529 < baseStart_990529 := by decide
  rcases family_descends (prefixWord ++ tailWord_990529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990540 : List Nat := [2, 2, 1, 3, 2, 2, 3, 6]
def baseStart_990540 : Nat := 118140960795 + 990540 * 2 ^ 59
def prefixEnd_990540 : Nat := 4983230072969 + 3 ^ 40 * 990540 * 2
def baseEnd_990540 : Nat := 75351574445134776502903

theorem tailTrace_990540 : CollatzResearch.WordTrace tailWord_990540 prefixEnd_990540 75351574445134776502903 := by
  unfold tailWord_990540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063980915725112804368537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24085307887633483739158049 18063980915725112804368537)
  ·
    refine ⟨13547985686793834603276403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18063980915725112804368537 13547985686793834603276403)
    ·
      refine ⟨20321978530190751904914605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13547985686793834603276403 20321978530190751904914605)
      ·
        refine ⟨7620741948821531964342977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20321978530190751904914605 7620741948821531964342977)
        ·
          refine ⟨5715556461616148973257233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7620741948821531964342977 5715556461616148973257233)
          ·
            refine ⟨4286667346212111729942925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5715556461616148973257233 4286667346212111729942925)
            ·
              refine ⟨1607500254829541898728597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4286667346212111729942925 1607500254829541898728597)
              ·
                refine ⟨75351574445134776502903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1607500254829541898728597 75351574445134776502903)
                ·
                  rfl

theorem cell21_990540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_990540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990540 prefixEnd_990540 := by exact prefixLift 990540
  have htrace : WordTrace (prefixWord ++ tailWord_990540) baseStart_990540 baseEnd_990540 := by
    simpa [prefixWord, tailWord_990540, baseEnd_990540] using wordTrace_append hprefix tailTrace_990540
  have hstable : (prefixWord ++ tailWord_990540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990540).length < 2 ^ (prefixWord ++ tailWord_990540).sum := by decide
  have hdescent : baseEnd_990540 < baseStart_990540 := by decide
  rcases family_descends (prefixWord ++ tailWord_990540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990554 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_990554 : Nat := 118140960795 + 990554 * 2 ^ 59
def prefixEnd_990554 : Nat := 4983230072969 + 3 ^ 40 * 990554 * 2
def baseEnd_990554 : Nat := 226057918326143416275347

theorem tailTrace_990554 : CollatzResearch.WordTrace tailWord_990554 prefixEnd_990554 226057918326143416275347 := by
  unfold tailWord_990554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9032118113349876499936679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24085648302266337333164477 9032118113349876499936679)
  ·
    refine ⟨13548177170024814749905019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9032118113349876499936679 13548177170024814749905019)
    ·
      refine ⟨20322265755037222124857529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13548177170024814749905019 20322265755037222124857529)
      ·
        refine ⟨15241699316277916593643147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20322265755037222124857529 15241699316277916593643147)
        ·
          refine ⟨22862548974416874890464721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15241699316277916593643147 22862548974416874890464721)
          ·
            refine ⟨17146911730812656167848541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22862548974416874890464721 17146911730812656167848541)
            ·
              refine ⟨6430091899054746062943203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17146911730812656167848541 6430091899054746062943203)
              ·
                refine ⟨9645137848582119094414805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430091899054746062943203 9645137848582119094414805)
                ·
                  refine ⟨226057918326143416275347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9645137848582119094414805 226057918326143416275347)
                  ·
                    rfl

theorem cell21_990554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_990554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990554 prefixEnd_990554 := by exact prefixLift 990554
  have htrace : WordTrace (prefixWord ++ tailWord_990554) baseStart_990554 baseEnd_990554 := by
    simpa [prefixWord, tailWord_990554, baseEnd_990554] using wordTrace_append hprefix tailTrace_990554
  have hstable : (prefixWord ++ tailWord_990554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990554).length < 2 ^ (prefixWord ++ tailWord_990554).sum := by decide
  have hdescent : baseEnd_990554 < baseStart_990554 := by decide
  rcases family_descends (prefixWord ++ tailWord_990554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990698 : List Nat := [3, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_990698 : Nat := 118140960795 + 990698 * 2 ^ 59
def prefixEnd_990698 : Nat := 4983230072969 + 3 ^ 40 * 990698 * 2
def baseEnd_990698 : Nat := 226090781088031165875053

theorem tailTrace_990698 : CollatzResearch.WordTrace tailWord_990698 prefixEnd_990698 226090781088031165875053 := by
  unfold tailWord_990698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9033431141219454648247187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24089149709918545728659165 9033431141219454648247187)
  ·
    refine ⟨13550146711829181972370781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9033431141219454648247187 13550146711829181972370781)
    ·
      refine ⟨5081305016935943239639043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13550146711829181972370781 5081305016935943239639043)
      ·
        refine ⟨7621957525403914859458565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081305016935943239639043 7621957525403914859458565)
        ·
          refine ⟨1429117036013234036148481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7621957525403914859458565 1429117036013234036148481)
          ·
            refine ⟨1071837777009925527111361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429117036013234036148481 1071837777009925527111361)
            ·
              refine ⟨803878332757444145333521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071837777009925527111361 803878332757444145333521)
              ·
                refine ⟨602908749568083109000141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803878332757444145333521 602908749568083109000141)
                ·
                  refine ⟨226090781088031165875053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602908749568083109000141 226090781088031165875053)
                  ·
                    rfl

theorem cell21_990698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_990698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990698 prefixEnd_990698 := by exact prefixLift 990698
  have htrace : WordTrace (prefixWord ++ tailWord_990698) baseStart_990698 baseEnd_990698 := by
    simpa [prefixWord, tailWord_990698, baseEnd_990698] using wordTrace_append hprefix tailTrace_990698
  have hstable : (prefixWord ++ tailWord_990698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990698).length < 2 ^ (prefixWord ++ tailWord_990698).sum := by decide
  have hdescent : baseEnd_990698 < baseStart_990698 := by decide
  rcases family_descends (prefixWord ++ tailWord_990698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990709 : List Nat := [1, 3, 5, 1, 1, 1, 3, 6]
def baseStart_990709 : Nat := 118140960795 + 990709 * 2 ^ 59
def prefixEnd_990709 : Nat := 4983230072969 + 3 ^ 40 * 990709 * 2
def baseEnd_990709 : Nat := 75364430479299197063899

theorem tailTrace_990709 : CollatzResearch.WordTrace tailWord_990709 prefixEnd_990709 75364430479299197063899 := by
  unfold tailWord_990709
  simp only [CollatzResearch.WordTrace]
  refine ⟨36134125767837967471639181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24089417178558644981092787 36134125767837967471639181)
  ·
    refine ⟨13550297162939237801864693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36134125767837967471639181 13550297162939237801864693)
    ·
      refine ⟨1270340359025553543924815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13550297162939237801864693 1270340359025553543924815)
      ·
        refine ⟨1905510538538330315887223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1270340359025553543924815 1905510538538330315887223)
        ·
          refine ⟨2858265807807495473830835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905510538538330315887223 2858265807807495473830835)
          ·
            refine ⟨4287398711711243210746253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858265807807495473830835 4287398711711243210746253)
            ·
              refine ⟨1607774516891716204029845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4287398711711243210746253 1607774516891716204029845)
              ·
                refine ⟨75364430479299197063899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1607774516891716204029845 75364430479299197063899)
                ·
                  rfl

theorem cell21_990709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 6].length) (baseStart_990709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990709 prefixEnd_990709 := by exact prefixLift 990709
  have htrace : WordTrace (prefixWord ++ tailWord_990709) baseStart_990709 baseEnd_990709 := by
    simpa [prefixWord, tailWord_990709, baseEnd_990709] using wordTrace_append hprefix tailTrace_990709
  have hstable : (prefixWord ++ tailWord_990709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990709).length < 2 ^ (prefixWord ++ tailWord_990709).sum := by decide
  have hdescent : baseEnd_990709 < baseStart_990709 := by decide
  rcases family_descends (prefixWord ++ tailWord_990709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990754 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_990754 : Nat := 118140960795 + 990754 * 2 ^ 59
def prefixEnd_990754 : Nat := 4983230072969 + 3 ^ 40 * 990754 * 2
def baseEnd_990754 : Nat := 226103561050987512941605

theorem tailTrace_990754 : CollatzResearch.WordTrace tailWord_990754 prefixEnd_990754 226103561050987512941605 := by
  unfold tailWord_990754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9033941763168735039256829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24090511368449960104684877 9033941763168735039256829)
  ·
    refine ⟨3387728161188275639721311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9033941763168735039256829 3387728161188275639721311)
    ·
      refine ⟨5081592241782413459581967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387728161188275639721311 5081592241782413459581967)
      ·
        refine ⟨7622388362673620189372951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081592241782413459581967 7622388362673620189372951)
        ·
          refine ⟨11433582544010430284059427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622388362673620189372951 11433582544010430284059427)
          ·
            refine ⟨17150373816015645426089141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11433582544010430284059427 17150373816015645426089141)
            ·
              refine ⟨1607847545251466758695857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17150373816015645426089141 1607847545251466758695857)
              ·
                refine ⟨1205885658938600069021893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607847545251466758695857 1205885658938600069021893)
                ·
                  refine ⟨226103561050987512941605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205885658938600069021893 226103561050987512941605)
                  ·
                    rfl

theorem cell21_990754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_990754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990754 prefixEnd_990754 := by exact prefixLift 990754
  have htrace : WordTrace (prefixWord ++ tailWord_990754) baseStart_990754 baseEnd_990754 := by
    simpa [prefixWord, tailWord_990754, baseEnd_990754] using wordTrace_append hprefix tailTrace_990754
  have hstable : (prefixWord ++ tailWord_990754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990754).length < 2 ^ (prefixWord ++ tailWord_990754).sum := by decide
  have hdescent : baseEnd_990754 < baseStart_990754 := by decide
  rcases family_descends (prefixWord ++ tailWord_990754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990940 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_990940 : Nat := 118140960795 + 990940 * 2 ^ 59
def prefixEnd_990940 : Nat := 4983230072969 + 3 ^ 40 * 990940 * 2
def baseEnd_990940 : Nat := 226146008785092522841225

theorem tailTrace_990940 : CollatzResearch.WordTrace tailWord_990940 prefixEnd_990940 226146008785092522841225 := by
  unfold tailWord_990940
  simp only [CollatzResearch.WordTrace]
  refine ⟨18071275515000546961649137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24095034020000729282198849 18071275515000546961649137)
  ·
    refine ⟨13553456636250410221236853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18071275515000546961649137 13553456636250410221236853)
    ·
      refine ⟨1270636559648475958240955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13553456636250410221236853 1270636559648475958240955)
      ·
        refine ⟨1905954839472713937361433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1270636559648475958240955 1905954839472713937361433)
        ·
          refine ⟨1429466129604535453021075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905954839472713937361433 1429466129604535453021075)
          ·
            refine ⟨2144199194406803179531613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429466129604535453021075 2144199194406803179531613)
            ·
              refine ⟨804074697902551192324355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2144199194406803179531613 804074697902551192324355)
              ·
                refine ⟨1206112046853826788486533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804074697902551192324355 1206112046853826788486533)
                ·
                  refine ⟨226146008785092522841225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1206112046853826788486533 226146008785092522841225)
                  ·
                    rfl

theorem cell21_990940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_990940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990940 prefixEnd_990940 := by exact prefixLift 990940
  have htrace : WordTrace (prefixWord ++ tailWord_990940) baseStart_990940 baseEnd_990940 := by
    simpa [prefixWord, tailWord_990940, baseEnd_990940] using wordTrace_append hprefix tailTrace_990940
  have hstable : (prefixWord ++ tailWord_990940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990940).length < 2 ^ (prefixWord ++ tailWord_990940).sum := by decide
  have hdescent : baseEnd_990940 < baseStart_990940 := by decide
  rcases family_descends (prefixWord ++ tailWord_990940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990999 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 4]
def baseStart_990999 : Nat := 118140960795 + 990999 * 2 ^ 59
def prefixEnd_990999 : Nat := 4983230072969 + 3 ^ 40 * 990999 * 2
def baseEnd_990999 : Nat := 226159473388921531357771

theorem tailTrace_990999 : CollatzResearch.WordTrace tailWord_990999 prefixEnd_990999 226159473388921531357771 := by
  unfold tailWord_990999
  simp only [CollatzResearch.WordTrace]
  refine ⟨36144702936787346999696051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24096468624524897999797367 36144702936787346999696051)
  ·
    refine ⟨54217054405181020499544077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36144702936787346999696051 54217054405181020499544077)
    ·
      refine ⟨20331395401942882687329029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54217054405181020499544077 20331395401942882687329029)
      ·
        refine ⟨3812136637864290503874193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20331395401942882687329029 3812136637864290503874193)
        ·
          refine ⟨2859102478398217877905645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3812136637864290503874193 2859102478398217877905645)
          ·
            refine ⟨1072163429399331704214617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2859102478398217877905645 1072163429399331704214617)
            ·
              refine ⟨804122572049498778160963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072163429399331704214617 804122572049498778160963)
              ·
                refine ⟨1206183858074248167241445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804122572049498778160963 1206183858074248167241445)
                ·
                  refine ⟨226159473388921531357771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1206183858074248167241445 226159473388921531357771)
                  ·
                    rfl

theorem cell21_990999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 4].length) (baseStart_990999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_990999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_990999 prefixEnd_990999 := by exact prefixLift 990999
  have htrace : WordTrace (prefixWord ++ tailWord_990999) baseStart_990999 baseEnd_990999 := by
    simpa [prefixWord, tailWord_990999, baseEnd_990999] using wordTrace_append hprefix tailTrace_990999
  have hstable : (prefixWord ++ tailWord_990999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990999).length < 2 ^ (prefixWord ++ tailWord_990999).sum := by decide
  have hdescent : baseEnd_990999 < baseStart_990999 := by decide
  rcases family_descends (prefixWord ++ tailWord_990999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991010 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_991010 : Nat := 118140960795 + 991010 * 2 ^ 59
def prefixEnd_991010 : Nat := 4983230072969 + 3 ^ 40 * 991010 * 2
def baseEnd_991010 : Nat := 226161983738787956674415

theorem tailTrace_991010 : CollatzResearch.WordTrace tailWord_991010 prefixEnd_991010 226161983738787956674415 := by
  unfold tailWord_991010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036276034936873969586621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24096736093164997252230989 9036276034936873969586621)
  ·
    refine ⟨3388603513101327738594983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9036276034936873969586621 3388603513101327738594983)
    ·
      refine ⟨5082905269651991607892475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3388603513101327738594983 5082905269651991607892475)
      ·
        refine ⟨7624357904477987411838713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082905269651991607892475 7624357904477987411838713)
        ·
          refine ⟨5718268428358490558879035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7624357904477987411838713 5718268428358490558879035)
          ·
            refine ⟨8577402642537735838318553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718268428358490558879035 8577402642537735838318553)
            ·
              refine ⟨6433051981903301878738915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577402642537735838318553 6433051981903301878738915)
              ·
                refine ⟨9649577972854952818108373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433051981903301878738915 9649577972854952818108373)
                ·
                  refine ⟨226161983738787956674415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9649577972854952818108373 226161983738787956674415)
                  ·
                    rfl

theorem cell21_991010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_991010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991010 prefixEnd_991010 := by exact prefixLift 991010
  have htrace : WordTrace (prefixWord ++ tailWord_991010) baseStart_991010 baseEnd_991010 := by
    simpa [prefixWord, tailWord_991010, baseEnd_991010] using wordTrace_append hprefix tailTrace_991010
  have hstable : (prefixWord ++ tailWord_991010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991010).length < 2 ^ (prefixWord ++ tailWord_991010).sum := by decide
  have hdescent : baseEnd_991010 < baseStart_991010 := by decide
  rcases family_descends (prefixWord ++ tailWord_991010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991072 : List Nat := [2, 1, 1, 3, 3, 3, 3, 5]
def baseStart_991072 : Nat := 118140960795 + 991072 * 2 ^ 59
def prefixEnd_991072 : Nat := 4983230072969 + 3 ^ 40 * 991072 * 2
def baseEnd_991072 : Nat := 75392044327829875546985

theorem tailTrace_991072 : CollatzResearch.WordTrace tailWord_991072 prefixEnd_991072 75392044327829875546985 := by
  unfold tailWord_991072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18073682732761440233551735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24098243643681920311402313 18073682732761440233551735)
  ·
    refine ⟨27110524099142160350327603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18073682732761440233551735 27110524099142160350327603)
    ·
      refine ⟨40665786148713240525491405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27110524099142160350327603 40665786148713240525491405)
      ·
        refine ⟨15249669805767465197059277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40665786148713240525491405 15249669805767465197059277)
        ·
          refine ⟨5718626177162799448897229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15249669805767465197059277 5718626177162799448897229)
          ·
            refine ⟨2144484816436049793336461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5718626177162799448897229 2144484816436049793336461)
            ·
              refine ⟨804181806163518672501173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2144484816436049793336461 804181806163518672501173)
              ·
                refine ⟨75392044327829875546985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804181806163518672501173 75392044327829875546985)
                ·
                  rfl

theorem cell21_991072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_991072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991072 prefixEnd_991072 := by exact prefixLift 991072
  have htrace : WordTrace (prefixWord ++ tailWord_991072) baseStart_991072 baseEnd_991072 := by
    simpa [prefixWord, tailWord_991072, baseEnd_991072] using wordTrace_append hprefix tailTrace_991072
  have hstable : (prefixWord ++ tailWord_991072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991072).length < 2 ^ (prefixWord ++ tailWord_991072).sum := by decide
  have hdescent : baseEnd_991072 < baseStart_991072 := by decide
  rcases family_descends (prefixWord ++ tailWord_991072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991137 : List Nat := [1, 2, 3, 4, 2, 2, 1, 3, 3]
def baseStart_991137 : Nat := 118140960795 + 991137 * 2 ^ 59
def prefixEnd_991137 : Nat := 4983230072969 + 3 ^ 40 * 991137 * 2
def baseEnd_991137 : Nat := 226190966869063958057489

theorem tailTrace_991137 : CollatzResearch.WordTrace tailWord_991137 prefixEnd_991137 226190966869063958057489 := by
  unfold tailWord_991137
  simp only [CollatzResearch.WordTrace]
  refine ⟨36149736210287396568219665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24099824140191597712146443 36149736210287396568219665)
  ·
    refine ⟨27112302157715547426164749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36149736210287396568219665 27112302157715547426164749)
    ·
      refine ⟨10167113309143330284811781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27112302157715547426164749 10167113309143330284811781)
      ·
        refine ⟨1906333745464374428402209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10167113309143330284811781 1906333745464374428402209)
        ·
          refine ⟨1429750309098280821301657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1906333745464374428402209 1429750309098280821301657)
          ·
            refine ⟨1072312731823710615976243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429750309098280821301657 1072312731823710615976243)
            ·
              refine ⟨1608469097735565923964365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072312731823710615976243 1608469097735565923964365)
              ·
                refine ⟨603175911650837221486637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608469097735565923964365 603175911650837221486637)
                ·
                  refine ⟨226190966869063958057489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603175911650837221486637 226190966869063958057489)
                  ·
                    rfl

theorem cell21_991137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_991137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991137 prefixEnd_991137 := by exact prefixLift 991137
  have htrace : WordTrace (prefixWord ++ tailWord_991137) baseStart_991137 baseEnd_991137 := by
    simpa [prefixWord, tailWord_991137, baseEnd_991137] using wordTrace_append hprefix tailTrace_991137
  have hstable : (prefixWord ++ tailWord_991137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991137).length < 2 ^ (prefixWord ++ tailWord_991137).sum := by decide
  have hdescent : baseEnd_991137 < baseStart_991137 := by decide
  rcases family_descends (prefixWord ++ tailWord_991137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991207 : List Nat := [1, 1, 5, 2, 3, 9]
def baseStart_991207 : Nat := 118140960795 + 991207 * 2 ^ 59
def prefixEnd_991207 : Nat := 4983230072969 + 3 ^ 40 * 991207 * 2
def baseEnd_991207 : Nat := 8378034882324421921877

theorem tailTrace_991207 : CollatzResearch.WordTrace tailWord_991207 prefixEnd_991207 8378034882324421921877 := by
  unfold tailWord_991207
  simp only [CollatzResearch.WordTrace]
  refine ⟨36152289320033798523267875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24101526213355865682178583 36152289320033798523267875)
  ·
    refine ⟨54228433980050697784901813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36152289320033798523267875 54228433980050697784901813)
    ·
      refine ⟨5083915685629752917334545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54228433980050697784901813 5083915685629752917334545)
      ·
        refine ⟨3812936764222314688000909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5083915685629752917334545 3812936764222314688000909)
        ·
          refine ⟨1429851286583368008000341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3812936764222314688000909 1429851286583368008000341)
          ·
            refine ⟨8378034882324421921877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1429851286583368008000341 8378034882324421921877)
            ·
              rfl

theorem cell21_991207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 9].length) (baseStart_991207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991207 prefixEnd_991207 := by exact prefixLift 991207
  have htrace : WordTrace (prefixWord ++ tailWord_991207) baseStart_991207 baseEnd_991207 := by
    simpa [prefixWord, tailWord_991207, baseEnd_991207] using wordTrace_append hprefix tailTrace_991207
  have hstable : (prefixWord ++ tailWord_991207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991207).length < 2 ^ (prefixWord ++ tailWord_991207).sum := by decide
  have hdescent : baseEnd_991207 < baseStart_991207 := by decide
  rcases family_descends (prefixWord ++ tailWord_991207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991213 : List Nat := [1, 5, 1, 4, 1, 1, 1, 4, 3]
def baseStart_991213 : Nat := 118140960795 + 991213 * 2 ^ 59
def prefixEnd_991213 : Nat := 4983230072969 + 3 ^ 40 * 991213 * 2
def baseEnd_991213 : Nat := 226208311104504714790667

theorem tailTrace_991213 : CollatzResearch.WordTrace tailWord_991213 prefixEnd_991213 226208311104504714790667 := by
  unfold tailWord_991213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36152508158012061547986293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24101672105341374365324195 36152508158012061547986293)
  ·
    refine ⟨3389297639813630770123715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36152508158012061547986293 3389297639813630770123715)
    ·
      refine ⟨5083946459720446155185573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389297639813630770123715 5083946459720446155185573)
      ·
        refine ⟨953239961197583654097295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5083946459720446155185573 953239961197583654097295)
        ·
          refine ⟨1429859941796375481145943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953239961197583654097295 1429859941796375481145943)
          ·
            refine ⟨2144789912694563221718915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429859941796375481145943 2144789912694563221718915)
            ·
              refine ⟨3217184869041844832578373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144789912694563221718915 3217184869041844832578373)
              ·
                refine ⟨603222162945345906108445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3217184869041844832578373 603222162945345906108445)
                ·
                  refine ⟨226208311104504714790667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603222162945345906108445 226208311104504714790667)
                  ·
                    rfl

theorem cell21_991213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_991213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991213 prefixEnd_991213 := by exact prefixLift 991213
  have htrace : WordTrace (prefixWord ++ tailWord_991213) baseStart_991213 baseEnd_991213 := by
    simpa [prefixWord, tailWord_991213, baseEnd_991213] using wordTrace_append hprefix tailTrace_991213
  have hstable : (prefixWord ++ tailWord_991213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991213).length < 2 ^ (prefixWord ++ tailWord_991213).sum := by decide
  have hdescent : baseEnd_991213 < baseStart_991213 := by decide
  rcases family_descends (prefixWord ++ tailWord_991213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991269 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 4]
def baseStart_991269 : Nat := 118140960795 + 991269 * 2 ^ 59
def prefixEnd_991269 : Nat := 4983230072969 + 3 ^ 40 * 991269 * 2
def baseEnd_991269 : Nat := 226221091067461061857219

theorem tailTrace_991269 : CollatzResearch.WordTrace tailWord_991269 prefixEnd_991269 226221091067461061857219 := by
  unfold tailWord_991269
  simp only [CollatzResearch.WordTrace]
  refine ⟨36154550645809183112024861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24103033763872788741349907 36154550645809183112024861)
  ·
    refine ⟨13557956492178443667009323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36154550645809183112024861 13557956492178443667009323)
    ·
      refine ⟨20336934738267665500513985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13557956492178443667009323 20336934738267665500513985)
      ·
        refine ⟨15252701053700749125385489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20336934738267665500513985 15252701053700749125385489)
        ·
          refine ⟨11439525790275561844039117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15252701053700749125385489 11439525790275561844039117)
          ·
            refine ⟨4289822171353335691514669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11439525790275561844039117 4289822171353335691514669)
            ·
              refine ⟨1608683314257500884318001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4289822171353335691514669 1608683314257500884318001)
              ·
                refine ⟨1206512485693125663238501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608683314257500884318001 1206512485693125663238501)
                ·
                  refine ⟨226221091067461061857219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1206512485693125663238501 226221091067461061857219)
                  ·
                    rfl

theorem cell21_991269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_991269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991269 prefixEnd_991269 := by exact prefixLift 991269
  have htrace : WordTrace (prefixWord ++ tailWord_991269) baseStart_991269 baseEnd_991269 := by
    simpa [prefixWord, tailWord_991269, baseEnd_991269] using wordTrace_append hprefix tailTrace_991269
  have hstable : (prefixWord ++ tailWord_991269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991269).length < 2 ^ (prefixWord ++ tailWord_991269).sum := by decide
  have hdescent : baseEnd_991269 < baseStart_991269 := by decide
  rcases family_descends (prefixWord ++ tailWord_991269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991272 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_991272 : Nat := 118140960795 + 991272 * 2 ^ 59
def prefixEnd_991272 : Nat := 4983230072969 + 3 ^ 40 * 991272 * 2
def baseEnd_991272 : Nat := 226221775708333723307213

theorem tailTrace_991272 : CollatzResearch.WordTrace tailWord_991272 prefixEnd_991272 226221775708333723307213 := by
  unfold tailWord_991272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18077330032399157312192035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24103106709865543082922713 18077330032399157312192035)
  ·
    refine ⟨27115995048598735968288053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18077330032399157312192035 27115995048598735968288053)
    ·
      refine ⟨2542124535806131497027005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27115995048598735968288053 2542124535806131497027005)
      ·
        refine ⟨953296700927299311385127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2542124535806131497027005 953296700927299311385127)
        ·
          refine ⟨1429945051390948967077691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953296700927299311385127 1429945051390948967077691)
          ·
            refine ⟨2144917577086423450616537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429945051390948967077691 2144917577086423450616537)
            ·
              refine ⟨1608688182814817587962403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144917577086423450616537 1608688182814817587962403)
              ·
                refine ⟨2413032274222226381943605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608688182814817587962403 2413032274222226381943605)
                ·
                  refine ⟨226221775708333723307213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2413032274222226381943605 226221775708333723307213)
                  ·
                    rfl

theorem cell21_991272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_991272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991272 prefixEnd_991272 := by exact prefixLift 991272
  have htrace : WordTrace (prefixWord ++ tailWord_991272) baseStart_991272 baseEnd_991272 := by
    simpa [prefixWord, tailWord_991272, baseEnd_991272] using wordTrace_append hprefix tailTrace_991272
  have hstable : (prefixWord ++ tailWord_991272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991272).length < 2 ^ (prefixWord ++ tailWord_991272).sum := by decide
  have hdescent : baseEnd_991272 < baseStart_991272 := by decide
  rcases family_descends (prefixWord ++ tailWord_991272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991328 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_991328 : Nat := 118140960795 + 991328 * 2 ^ 59
def prefixEnd_991328 : Nat := 4983230072969 + 3 ^ 40 * 991328 * 2
def baseEnd_991328 : Nat := 226234555671290070373765

theorem tailTrace_991328 : CollatzResearch.WordTrace tailWord_991328 prefixEnd_991328 226234555671290070373765 := by
  unfold tailWord_991328
  simp only [CollatzResearch.WordTrace]
  refine ⟨18078351276297718094211319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24104468368396957458948425 18078351276297718094211319)
  ·
    refine ⟨27117526914446577141316979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18078351276297718094211319 27117526914446577141316979)
    ·
      refine ⟨40676290371669865711975469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27117526914446577141316979 40676290371669865711975469)
      ·
        refine ⟨15253608889376199641990801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40676290371669865711975469 15253608889376199641990801)
        ·
          refine ⟨11440206667032149731493101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15253608889376199641990801 11440206667032149731493101)
          ·
            refine ⟨4290077500137056149309913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11440206667032149731493101 4290077500137056149309913)
            ·
              refine ⟨3217558125102792111982435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4290077500137056149309913 3217558125102792111982435)
              ·
                refine ⟨4826337187654188167973653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217558125102792111982435 4826337187654188167973653)
                ·
                  refine ⟨226234555671290070373765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4826337187654188167973653 226234555671290070373765)
                  ·
                    rfl

theorem cell21_991328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_991328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991328 prefixEnd_991328 := by exact prefixLift 991328
  have htrace : WordTrace (prefixWord ++ tailWord_991328) baseStart_991328 baseEnd_991328 := by
    simpa [prefixWord, tailWord_991328, baseEnd_991328] using wordTrace_append hprefix tailTrace_991328
  have hstable : (prefixWord ++ tailWord_991328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991328).length < 2 ^ (prefixWord ++ tailWord_991328).sum := by decide
  have hdescent : baseEnd_991328 < baseStart_991328 := by decide
  rcases family_descends (prefixWord ++ tailWord_991328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991418 : List Nat := [3, 1, 1, 1, 2, 2, 2, 9]
def baseStart_991418 : Nat := 118140960795 + 991418 * 2 ^ 59
def prefixEnd_991418 : Nat := 4983230072969 + 3 ^ 40 * 991418 * 2
def baseEnd_991418 : Nat := 75418364965823304624527

theorem tailTrace_991418 : CollatzResearch.WordTrace tailWord_991418 prefixEnd_991418 75418364965823304624527 := by
  unfold tailWord_991418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039996280567345389799727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24106656748179587706132605 9039996280567345389799727)
  ·
    refine ⟨13559994420851018084699591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039996280567345389799727 13559994420851018084699591)
    ·
      refine ⟨20339991631276527127049387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13559994420851018084699591 20339991631276527127049387)
      ·
        refine ⟨30509987446914790690574081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20339991631276527127049387 30509987446914790690574081)
        ·
          refine ⟨22882490585186093017930561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30509987446914790690574081 22882490585186093017930561)
          ·
            refine ⟨17161867938889569763447921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22882490585186093017930561 17161867938889569763447921)
            ·
              refine ⟨12871400954167177322585941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17161867938889569763447921 12871400954167177322585941)
              ·
                refine ⟨75418364965823304624527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12871400954167177322585941 75418364965823304624527)
                ·
                  rfl

theorem cell21_991418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_991418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991418 prefixEnd_991418 := by exact prefixLift 991418
  have htrace : WordTrace (prefixWord ++ tailWord_991418) baseStart_991418 baseEnd_991418 := by
    simpa [prefixWord, tailWord_991418, baseEnd_991418] using wordTrace_append hprefix tailTrace_991418
  have hstable : (prefixWord ++ tailWord_991418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991418).length < 2 ^ (prefixWord ++ tailWord_991418).sum := by decide
  have hdescent : baseEnd_991418 < baseStart_991418 := by decide
  rcases family_descends (prefixWord ++ tailWord_991418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991438 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_991438 : Nat := 118140960795 + 991438 * 2 ^ 59
def prefixEnd_991438 : Nat := 4983230072969 + 3 ^ 40 * 991438 * 2
def baseEnd_991438 : Nat := 226259659169954323540207

theorem tailTrace_991438 : CollatzResearch.WordTrace tailWord_991438 prefixEnd_991438 226259659169954323540207 := by
  unfold tailWord_991438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520089322774615621865871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24107143054797949983284645 4520089322774615621865871)
  ·
    refine ⟨6780133984161923432798807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4520089322774615621865871 6780133984161923432798807)
    ·
      refine ⟨10170200976242885149198211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780133984161923432798807 10170200976242885149198211)
      ·
        refine ⟨15255301464364327723797317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10170200976242885149198211 15255301464364327723797317)
        ·
          refine ⟨2860369024568311448211997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15255301464364327723797317 2860369024568311448211997)
          ·
            refine ⟨1072638384213116793079499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2860369024568311448211997 1072638384213116793079499)
            ·
              refine ⟨1608957576319675189619249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072638384213116793079499 1608957576319675189619249)
              ·
                refine ⟨1206718182239756392214437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608957576319675189619249 1206718182239756392214437)
                ·
                  refine ⟨226259659169954323540207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1206718182239756392214437 226259659169954323540207)
                  ·
                    rfl

theorem cell21_991438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_991438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991438 prefixEnd_991438 := by exact prefixLift 991438
  have htrace : WordTrace (prefixWord ++ tailWord_991438) baseStart_991438 baseEnd_991438 := by
    simpa [prefixWord, tailWord_991438, baseEnd_991438] using wordTrace_append hprefix tailTrace_991438
  have hstable : (prefixWord ++ tailWord_991438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991438).length < 2 ^ (prefixWord ++ tailWord_991438).sum := by decide
  have hdescent : baseEnd_991438 < baseStart_991438 := by decide
  rcases family_descends (prefixWord ++ tailWord_991438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991449 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 5]
def baseStart_991449 : Nat := 118140960795 + 991449 * 2 ^ 59
def prefixEnd_991449 : Nat := 4983230072969 + 3 ^ 40 * 991449 * 2
def baseEnd_991449 : Nat := 226262169519820748856851

theorem tailTrace_991449 : CollatzResearch.WordTrace tailWord_991449 prefixEnd_991449 226262169519820748856851 := by
  unfold tailWord_991449
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161115785157073853577401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24107410523438049235718267 36161115785157073853577401)
  ·
    refine ⟨27120836838867805390183051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36161115785157073853577401 27120836838867805390183051)
    ·
      refine ⟨40681255258301708085274577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27120836838867805390183051 40681255258301708085274577)
      ·
        refine ⟨30510941443726281063955933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40681255258301708085274577 30510941443726281063955933)
        ·
          refine ⟨11441603041397355398983475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30510941443726281063955933 11441603041397355398983475)
          ·
            refine ⟨17162404562096033098475213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441603041397355398983475 17162404562096033098475213)
            ·
              refine ⟨6435901710786012411928205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17162404562096033098475213 6435901710786012411928205)
              ·
                refine ⟨2413463141544754654473077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6435901710786012411928205 2413463141544754654473077)
                ·
                  refine ⟨226262169519820748856851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2413463141544754654473077 226262169519820748856851)
                  ·
                    rfl

theorem cell21_991449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_991449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991449 prefixEnd_991449 := by exact prefixLift 991449
  have htrace : WordTrace (prefixWord ++ tailWord_991449) baseStart_991449 baseEnd_991449 := by
    simpa [prefixWord, tailWord_991449, baseEnd_991449] using wordTrace_append hprefix tailTrace_991449
  have hstable : (prefixWord ++ tailWord_991449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991449).length < 2 ^ (prefixWord ++ tailWord_991449).sum := by decide
  have hdescent : baseEnd_991449 < baseStart_991449 := by decide
  rcases family_descends (prefixWord ++ tailWord_991449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991469 : List Nat := [1, 5, 1, 2, 3, 2, 2, 5]
def baseStart_991469 : Nat := 118140960795 + 991469 * 2 ^ 59
def prefixEnd_991469 : Nat := 4983230072969 + 3 ^ 40 * 991469 * 2
def baseEnd_991469 : Nat := 75422244597435052841159

theorem tailTrace_991469 : CollatzResearch.WordTrace tailWord_991469 prefixEnd_991469 75422244597435052841159 := by
  unfold tailWord_991469
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161845245084617269305461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24107896830056411512870307 36161845245084617269305461)
  ·
    refine ⟨3390172991726682868997387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36161845245084617269305461 3390172991726682868997387)
    ·
      refine ⟨5085259487590024303496081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3390172991726682868997387 5085259487590024303496081)
      ·
        refine ⟨3813944615692518227622061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5085259487590024303496081 3813944615692518227622061)
        ·
          refine ⟨1430229230884694335358273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3813944615692518227622061 1430229230884694335358273)
          ·
            refine ⟨1072671923163520751518705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430229230884694335358273 1072671923163520751518705)
            ·
              refine ⟨804503942372640563639029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072671923163520751518705 804503942372640563639029)
              ·
                refine ⟨75422244597435052841159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804503942372640563639029 75422244597435052841159)
                ·
                  rfl

theorem cell21_991469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 5].length) (baseStart_991469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991469 prefixEnd_991469 := by exact prefixLift 991469
  have htrace : WordTrace (prefixWord ++ tailWord_991469) baseStart_991469 baseEnd_991469 := by
    simpa [prefixWord, tailWord_991469, baseEnd_991469] using wordTrace_append hprefix tailTrace_991469
  have hstable : (prefixWord ++ tailWord_991469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991469).length < 2 ^ (prefixWord ++ tailWord_991469).sum := by decide
  have hdescent : baseEnd_991469 < baseStart_991469 := by decide
  rcases family_descends (prefixWord ++ tailWord_991469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991511 : List Nat := [1, 1, 3, 4, 1, 3, 2, 6]
def baseStart_991511 : Nat := 118140960795 + 991511 * 2 ^ 59
def prefixEnd_991511 : Nat := 4983230072969 + 3 ^ 40 * 991511 * 2
def baseEnd_991511 : Nat := 75425439588174139607797

theorem tailTrace_991511 : CollatzResearch.WordTrace tailWord_991511 prefixEnd_991511 75425439588174139607797 := by
  unfold tailWord_991511
  simp only [CollatzResearch.WordTrace]
  refine ⟨36163377110932458442334387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24108918073954972294889591 36163377110932458442334387)
  ·
    refine ⟨54245065666398687663501581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36163377110932458442334387 54245065666398687663501581)
    ·
      refine ⟨20341899624899507873813093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54245065666398687663501581 20341899624899507873813093)
      ·
        refine ⟨3814106179668657726339955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20341899624899507873813093 3814106179668657726339955)
        ·
          refine ⟨5721159269502986589509933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3814106179668657726339955 5721159269502986589509933)
          ·
            refine ⟨2145434726063619971066225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5721159269502986589509933 2145434726063619971066225)
            ·
              refine ⟨1609076044547714978299669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145434726063619971066225 1609076044547714978299669)
              ·
                refine ⟨75425439588174139607797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1609076044547714978299669 75425439588174139607797)
                ·
                  rfl

theorem cell21_991511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 6].length) (baseStart_991511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991511 prefixEnd_991511 := by exact prefixLift 991511
  have htrace : WordTrace (prefixWord ++ tailWord_991511) baseStart_991511 baseEnd_991511 := by
    simpa [prefixWord, tailWord_991511, baseEnd_991511] using wordTrace_append hprefix tailTrace_991511
  have hstable : (prefixWord ++ tailWord_991511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991511).length < 2 ^ (prefixWord ++ tailWord_991511).sum := by decide
  have hdescent : baseEnd_991511 < baseStart_991511 := by decide
  rcases family_descends (prefixWord ++ tailWord_991511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991587 : List Nat := [1, 1, 1, 5, 2, 1, 5, 5]
def baseStart_991587 : Nat := 118140960795 + 991587 * 2 ^ 59
def prefixEnd_991587 : Nat := 4983230072969 + 3 ^ 40 * 991587 * 2
def baseEnd_991587 : Nat := 75431220999987725185523

theorem tailTrace_991587 : CollatzResearch.WordTrace tailWord_991587 prefixEnd_991587 75431220999987725185523 := by
  unfold tailWord_991587
  simp only [CollatzResearch.WordTrace]
  refine ⟨36166149058657123422101015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24110766039104748948067343 36166149058657123422101015)
  ·
    refine ⟨54249223587985685133151523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36166149058657123422101015 54249223587985685133151523)
    ·
      refine ⟨81373835381978527699727285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54249223587985685133151523 81373835381978527699727285)
      ·
        refine ⟨7628797067060486971849433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81373835381978527699727285 7628797067060486971849433)
        ·
          refine ⟨5721597800295365228887075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7628797067060486971849433 5721597800295365228887075)
          ·
            refine ⟨8582396700443047843330613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721597800295365228887075 8582396700443047843330613)
            ·
              refine ⟨804599690666535735312245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8582396700443047843330613 804599690666535735312245)
              ·
                refine ⟨75431220999987725185523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804599690666535735312245 75431220999987725185523)
                ·
                  rfl

theorem cell21_991587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 5].length) (baseStart_991587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991587 prefixEnd_991587 := by exact prefixLift 991587
  have htrace : WordTrace (prefixWord ++ tailWord_991587) baseStart_991587 baseEnd_991587 := by
    simpa [prefixWord, tailWord_991587, baseEnd_991587] using wordTrace_append hprefix tailTrace_991587
  have hstable : (prefixWord ++ tailWord_991587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991587).length < 2 ^ (prefixWord ++ tailWord_991587).sum := by decide
  have hdescent : baseEnd_991587 < baseStart_991587 := by decide
  rcases family_descends (prefixWord ++ tailWord_991587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991615 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 6]
def baseStart_991615 : Nat := 118140960795 + 991615 * 2 ^ 59
def prefixEnd_991615 : Nat := 4983230072969 + 3 ^ 40 * 991615 * 2
def baseEnd_991615 : Nat := 226300052981441349089845

theorem tailTrace_991615 : CollatzResearch.WordTrace tailWord_991615 prefixEnd_991615 226300052981441349089845 := by
  unfold tailWord_991615
  simp only [CollatzResearch.WordTrace]
  refine ⟨36167170302555684204120299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24111446868370456136080199 36167170302555684204120299)
  ·
    refine ⟨54250755453833526306180449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36167170302555684204120299 54250755453833526306180449)
    ·
      refine ⟨40688066590375144729635337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54250755453833526306180449 40688066590375144729635337)
      ·
        refine ⟨30516049942781358547226503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40688066590375144729635337 30516049942781358547226503)
        ·
          refine ⟨45774074914172037820839755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30516049942781358547226503 45774074914172037820839755)
          ·
            refine ⟨68661112371258056731259633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45774074914172037820839755 68661112371258056731259633)
            ·
              refine ⟨51495834278443542548444725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68661112371258056731259633 51495834278443542548444725)
              ·
                refine ⟨4827734463604082113916693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51495834278443542548444725 4827734463604082113916693)
                ·
                  refine ⟨226300052981441349089845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4827734463604082113916693 226300052981441349089845)
                  ·
                    rfl

theorem cell21_991615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_991615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991615 prefixEnd_991615 := by exact prefixLift 991615
  have htrace : WordTrace (prefixWord ++ tailWord_991615) baseStart_991615 baseEnd_991615 := by
    simpa [prefixWord, tailWord_991615, baseEnd_991615] using wordTrace_append hprefix tailTrace_991615
  have hstable : (prefixWord ++ tailWord_991615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991615).length < 2 ^ (prefixWord ++ tailWord_991615).sum := by decide
  have hdescent : baseEnd_991615 < baseStart_991615 := by decide
  rcases family_descends (prefixWord ++ tailWord_991615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991638 : List Nat := [5, 3, 1, 2, 1, 1, 1, 7]
def baseStart_991638 : Nat := 118140960795 + 991638 * 2 ^ 59
def prefixEnd_991638 : Nat := 4983230072969 + 3 ^ 40 * 991638 * 2
def baseEnd_991638 : Nat := 75435100631599473402155

theorem tailTrace_991638 : CollatzResearch.WordTrace tailWord_991638 prefixEnd_991638 75435100631599473402155 := by
  unfold tailWord_991638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260500573842022445762973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24112006120981572754805045 2260500573842022445762973)
  ·
    refine ⟨847687715190758417161115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2260500573842022445762973 847687715190758417161115)
    ·
      refine ⟨1271531572786137625741673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847687715190758417161115 1271531572786137625741673)
      ·
        refine ⟨953648679589603219306255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271531572786137625741673 953648679589603219306255)
        ·
          refine ⟨1430473019384404828959383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953648679589603219306255 1430473019384404828959383)
          ·
            refine ⟨2145709529076607243439075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430473019384404828959383 2145709529076607243439075)
            ·
              refine ⟨3218564293614910865158613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145709529076607243439075 3218564293614910865158613)
              ·
                refine ⟨75435100631599473402155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3218564293614910865158613 75435100631599473402155)
                ·
                  rfl

theorem cell21_991638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_991638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991638 prefixEnd_991638 := by exact prefixLift 991638
  have htrace : WordTrace (prefixWord ++ tailWord_991638) baseStart_991638 baseEnd_991638 := by
    simpa [prefixWord, tailWord_991638, baseEnd_991638] using wordTrace_append hprefix tailTrace_991638
  have hstable : (prefixWord ++ tailWord_991638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991638).length < 2 ^ (prefixWord ++ tailWord_991638).sum := by decide
  have hdescent : baseEnd_991638 < baseStart_991638 := by decide
  rcases family_descends (prefixWord ++ tailWord_991638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991722 : List Nat := [3, 1, 3, 1, 3, 10]
def baseStart_991722 : Nat := 118140960795 + 991722 * 2 ^ 59
def prefixEnd_991722 : Nat := 4983230072969 + 3 ^ 40 * 991722 * 2
def baseEnd_991722 : Nat := 8382387845897516326159

theorem tailTrace_991722 : CollatzResearch.WordTrace tailWord_991722 prefixEnd_991722 8382387845897516326159 := by
  unfold tailWord_991722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042768228292010369566355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24114048608778694318843613 9042768228292010369566355)
  ·
    refine ⟨13564152342438015554349533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9042768228292010369566355 13564152342438015554349533)
    ·
      refine ⟨5086557128414255832881075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13564152342438015554349533 5086557128414255832881075)
      ·
        refine ⟨7629835692621383749321613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5086557128414255832881075 7629835692621383749321613)
        ·
          refine ⟨2861188384733018905995605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7629835692621383749321613 2861188384733018905995605)
          ·
            refine ⟨8382387845897516326159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2861188384733018905995605 8382387845897516326159)
            ·
              rfl

theorem cell21_991722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 10].length) (baseStart_991722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991722 prefixEnd_991722 := by exact prefixLift 991722
  have htrace : WordTrace (prefixWord ++ tailWord_991722) baseStart_991722 baseEnd_991722 := by
    simpa [prefixWord, tailWord_991722, baseEnd_991722] using wordTrace_append hprefix tailTrace_991722
  have hstable : (prefixWord ++ tailWord_991722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991722).length < 2 ^ (prefixWord ++ tailWord_991722).sum := by decide
  have hdescent : baseEnd_991722 < baseStart_991722 := by decide
  rcases family_descends (prefixWord ++ tailWord_991722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991725 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 4]
def baseStart_991725 : Nat := 118140960795 + 991725 * 2 ^ 59
def prefixEnd_991725 : Nat := 4983230072969 + 3 ^ 40 * 991725 * 2
def baseEnd_991725 : Nat := 226325156480105602256287

theorem tailTrace_991725 : CollatzResearch.WordTrace tailWord_991725 prefixEnd_991725 226325156480105602256287 := by
  unfold tailWord_991725
  simp only [CollatzResearch.WordTrace]
  refine ⟨36171182332157172990624629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24114121554771448660416419 36171182332157172990624629)
  ·
    refine ⟨3391048343639734967871059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36171182332157172990624629 3391048343639734967871059)
    ·
      refine ⟨5086572515459602451806589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391048343639734967871059 5086572515459602451806589)
      ·
        refine ⟨1907464693297350919427471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5086572515459602451806589 1907464693297350919427471)
        ·
          refine ⟨2861197039946026379141207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907464693297350919427471 2861197039946026379141207)
          ·
            refine ⟨4291795559919039568711811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861197039946026379141207 4291795559919039568711811)
            ·
              refine ⟨6437693339878559353067717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291795559919039568711811 6437693339878559353067717)
              ·
                refine ⟨1207067501227229878700197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6437693339878559353067717 1207067501227229878700197)
                ·
                  refine ⟨226325156480105602256287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207067501227229878700197 226325156480105602256287)
                  ·
                    rfl

theorem cell21_991725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_991725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991725 prefixEnd_991725 := by exact prefixLift 991725
  have htrace : WordTrace (prefixWord ++ tailWord_991725) baseStart_991725 baseEnd_991725 := by
    simpa [prefixWord, tailWord_991725, baseEnd_991725] using wordTrace_append hprefix tailTrace_991725
  have hstable : (prefixWord ++ tailWord_991725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991725).length < 2 ^ (prefixWord ++ tailWord_991725).sum := by decide
  have hdescent : baseEnd_991725 < baseStart_991725 := by decide
  rcases family_descends (prefixWord ++ tailWord_991725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991770 : List Nat := [3, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_991770 : Nat := 118140960795 + 991770 * 2 ^ 59
def prefixEnd_991770 : Nat := 4983230072969 + 3 ^ 40 * 991770 * 2
def baseEnd_991770 : Nat := 226335426093195524006195

theorem tailTrace_991770 : CollatzResearch.WordTrace tailWord_991770 prefixEnd_991770 226335426093195524006195 := by
  unfold tailWord_991770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9043205904248536419003191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24115215744662763784008509 9043205904248536419003191)
  ·
    refine ⟨13564808856372804628504787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9043205904248536419003191 13564808856372804628504787)
    ·
      refine ⟨20347213284559206942757181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13564808856372804628504787 20347213284559206942757181)
      ·
        refine ⟨7630204981709702603533943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20347213284559206942757181 7630204981709702603533943)
        ·
          refine ⟨11445307472564553905300915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7630204981709702603533943 11445307472564553905300915)
          ·
            refine ⟨17167961208846830857951373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11445307472564553905300915 17167961208846830857951373)
            ·
              refine ⟨6437985453317561571731765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17167961208846830857951373 6437985453317561571731765)
              ·
                refine ⟨603561136248521397349853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6437985453317561571731765 603561136248521397349853)
                ·
                  refine ⟨226335426093195524006195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603561136248521397349853 226335426093195524006195)
                  ·
                    rfl

theorem cell21_991770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_991770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991770 prefixEnd_991770 := by exact prefixLift 991770
  have htrace : WordTrace (prefixWord ++ tailWord_991770) baseStart_991770 baseEnd_991770 := by
    simpa [prefixWord, tailWord_991770, baseEnd_991770] using wordTrace_append hprefix tailTrace_991770
  have hstable : (prefixWord ++ tailWord_991770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991770).length < 2 ^ (prefixWord ++ tailWord_991770).sum := by decide
  have hdescent : baseEnd_991770 < baseStart_991770 := by decide
  rcases family_descends (prefixWord ++ tailWord_991770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991801 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 4]
def baseStart_991801 : Nat := 118140960795 + 991801 * 2 ^ 59
def prefixEnd_991801 : Nat := 4983230072969 + 3 ^ 40 * 991801 * 2
def baseEnd_991801 : Nat := 226342500715546358989465

theorem tailTrace_991801 : CollatzResearch.WordTrace tailWord_991801 prefixEnd_991801 226342500715546358989465 := by
  unfold tailWord_991801
  simp only [CollatzResearch.WordTrace]
  refine ⟨36173954279881837970391257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24115969519921225313594171 36173954279881837970391257)
  ·
    refine ⟨27130465709911378477793443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36173954279881837970391257 27130465709911378477793443)
    ·
      refine ⟨40695698564867067716690165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27130465709911378477793443 40695698564867067716690165)
      ·
        refine ⟨3815221740456287598439703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40695698564867067716690165 3815221740456287598439703)
        ·
          refine ⟨5722832610684431397659555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815221740456287598439703 5722832610684431397659555)
          ·
            refine ⟨8584248916026647096489333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722832610684431397659555 8584248916026647096489333)
            ·
              refine ⟨804773335877498165295875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8584248916026647096489333 804773335877498165295875)
              ·
                refine ⟨1207160003816247247943813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804773335877498165295875 1207160003816247247943813)
                ·
                  refine ⟨226342500715546358989465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207160003816247247943813 226342500715546358989465)
                  ·
                    rfl

theorem cell21_991801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_991801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991801 prefixEnd_991801 := by exact prefixLift 991801
  have htrace : WordTrace (prefixWord ++ tailWord_991801) baseStart_991801 baseEnd_991801 := by
    simpa [prefixWord, tailWord_991801, baseEnd_991801] using wordTrace_append hprefix tailTrace_991801
  have hstable : (prefixWord ++ tailWord_991801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991801).length < 2 ^ (prefixWord ++ tailWord_991801).sum := by decide
  have hdescent : baseEnd_991801 < baseStart_991801 := by decide
  rcases family_descends (prefixWord ++ tailWord_991801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991815 : List Nat := [1, 1, 4, 1, 4, 1, 4, 5]
def baseStart_991815 : Nat := 118140960795 + 991815 * 2 ^ 59
def prefixEnd_991815 : Nat := 4983230072969 + 3 ^ 40 * 991815 * 2
def baseEnd_991815 : Nat := 75448565235428481918701

theorem tailTrace_991815 : CollatzResearch.WordTrace tailWord_991815 prefixEnd_991815 75448565235428481918701 := by
  unfold tailWord_991815
  simp only [CollatzResearch.WordTrace]
  refine ⟨36174464901831118361400899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24116309934554078907600599 36174464901831118361400899)
  ·
    refine ⟨54261697352746677542101349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36174464901831118361400899 54261697352746677542101349)
    ·
      refine ⟨10174068253640002039144003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54261697352746677542101349 10174068253640002039144003)
      ·
        refine ⟨15261102380460003058716005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174068253640002039144003 15261102380460003058716005)
        ·
          refine ⟨2861456696336250573509251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15261102380460003058716005 2861456696336250573509251)
          ·
            refine ⟨4292185044504375860263877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861456696336250573509251 4292185044504375860263877)
            ·
              refine ⟨804784695844570473799477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4292185044504375860263877 804784695844570473799477)
              ·
                refine ⟨75448565235428481918701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804784695844570473799477 75448565235428481918701)
                ·
                  rfl

theorem cell21_991815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 5].length) (baseStart_991815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991815 prefixEnd_991815 := by exact prefixLift 991815
  have htrace : WordTrace (prefixWord ++ tailWord_991815) baseStart_991815 baseEnd_991815 := by
    simpa [prefixWord, tailWord_991815, baseEnd_991815] using wordTrace_append hprefix tailTrace_991815
  have hstable : (prefixWord ++ tailWord_991815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991815).length < 2 ^ (prefixWord ++ tailWord_991815).sum := by decide
  have hdescent : baseEnd_991815 < baseStart_991815 := by decide
  rcases family_descends (prefixWord ++ tailWord_991815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991838 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_991838 : Nat := 118140960795 + 991838 * 2 ^ 59
def prefixEnd_991838 : Nat := 4983230072969 + 3 ^ 40 * 991838 * 2
def baseEnd_991838 : Nat := 226350944619642516872723

theorem tailTrace_991838 : CollatzResearch.WordTrace tailWord_991838 prefixEnd_991838 226350944619642516872723 := by
  unfold tailWord_991838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521912972593474161186021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24116869187165195526325445 4521912972593474161186021)
  ·
    refine ⟨847858682361276405222379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4521912972593474161186021 847858682361276405222379)
    ·
      refine ⟨1271788023541914607833569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847858682361276405222379 1271788023541914607833569)
      ·
        refine ⟨953841017656435955875177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271788023541914607833569 953841017656435955875177)
        ·
          refine ⟨715380763242326966906383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953841017656435955875177 715380763242326966906383)
          ·
            refine ⟨1073071144863490450359575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715380763242326966906383 1073071144863490450359575)
            ·
              refine ⟨1609606717295235675539363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073071144863490450359575 1609606717295235675539363)
              ·
                refine ⟨2414410075942853513309045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609606717295235675539363 2414410075942853513309045)
                ·
                  refine ⟨226350944619642516872723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2414410075942853513309045 226350944619642516872723)
                  ·
                    rfl

theorem cell21_991838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_991838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991838 prefixEnd_991838 := by exact prefixLift 991838
  have htrace : WordTrace (prefixWord ++ tailWord_991838) baseStart_991838 baseEnd_991838 := by
    simpa [prefixWord, tailWord_991838, baseEnd_991838] using wordTrace_append hprefix tailTrace_991838
  have hstable : (prefixWord ++ tailWord_991838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991838).length < 2 ^ (prefixWord ++ tailWord_991838).sum := by decide
  have hdescent : baseEnd_991838 < baseStart_991838 := by decide
  rcases family_descends (prefixWord ++ tailWord_991838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991843 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 6]
def baseStart_991843 : Nat := 118140960795 + 991843 * 2 ^ 59
def prefixEnd_991843 : Nat := 4983230072969 + 3 ^ 40 * 991843 * 2
def baseEnd_991843 : Nat := 226352085687763619289379

theorem tailTrace_991843 : CollatzResearch.WordTrace tailWord_991843 prefixEnd_991843 226352085687763619289379 := by
  unfold tailWord_991843
  simp only [CollatzResearch.WordTrace]
  refine ⟨36175486145729679143420183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24116990763819786095613455 36175486145729679143420183)
  ·
    refine ⟨54263229218594518715130275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36175486145729679143420183 54263229218594518715130275)
    ·
      refine ⟨81394843827891778072695413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54263229218594518715130275 81394843827891778072695413)
      ·
        refine ⟨7630766608864854194315195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81394843827891778072695413 7630766608864854194315195)
        ·
          refine ⟨11446149913297281291472793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7630766608864854194315195 11446149913297281291472793)
          ·
            refine ⟨8584612434972960968604595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11446149913297281291472793 8584612434972960968604595)
            ·
              refine ⟨12876918652459441452906893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584612434972960968604595 12876918652459441452906893)
              ·
                refine ⟨4828844494672290544840085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12876918652459441452906893 4828844494672290544840085)
                ·
                  refine ⟨226352085687763619289379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4828844494672290544840085 226352085687763619289379)
                  ·
                    rfl

theorem cell21_991843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_991843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991843 prefixEnd_991843 := by exact prefixLift 991843
  have htrace : WordTrace (prefixWord ++ tailWord_991843) baseStart_991843 baseEnd_991843 := by
    simpa [prefixWord, tailWord_991843, baseEnd_991843] using wordTrace_append hprefix tailTrace_991843
  have hstable : (prefixWord ++ tailWord_991843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991843).length < 2 ^ (prefixWord ++ tailWord_991843).sum := by decide
  have hdescent : baseEnd_991843 < baseStart_991843 := by decide
  rcases family_descends (prefixWord ++ tailWord_991843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991950 : List Nat := [4, 1, 1, 1, 3, 3, 8]
def baseStart_991950 : Nat := 118140960795 + 991950 * 2 ^ 59
def prefixEnd_991950 : Nat := 4983230072969 + 3 ^ 40 * 991950 * 2
def baseEnd_991950 : Nat := 25152944949506134556203

theorem tailTrace_991950 : CollatzResearch.WordTrace tailWord_991950 prefixEnd_991950 25152944949506134556203 := by
  unfold tailWord_991950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522423594542754552195663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24119592504228024278376869 4522423594542754552195663)
  ·
    refine ⟨6783635391814131828293495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4522423594542754552195663 6783635391814131828293495)
    ·
      refine ⟨10175453087721197742440243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783635391814131828293495 10175453087721197742440243)
      ·
        refine ⟨15263179631581796613660365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10175453087721197742440243 15263179631581796613660365)
        ·
          refine ⟨5723692361843173730122637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15263179631581796613660365 5723692361843173730122637)
          ·
            refine ⟨2146384635691190148795989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5723692361843173730122637 2146384635691190148795989)
            ·
              refine ⟨25152944949506134556203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2146384635691190148795989 25152944949506134556203)
              ·
                rfl

theorem cell21_991950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 8].length) (baseStart_991950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991950 prefixEnd_991950 := by exact prefixLift 991950
  have htrace : WordTrace (prefixWord ++ tailWord_991950) baseStart_991950 baseEnd_991950 := by
    simpa [prefixWord, tailWord_991950, baseEnd_991950] using wordTrace_append hprefix tailTrace_991950
  have hstable : (prefixWord ++ tailWord_991950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991950).length < 2 ^ (prefixWord ++ tailWord_991950).sum := by decide
  have hdescent : baseEnd_991950 < baseStart_991950 := by decide
  rcases family_descends (prefixWord ++ tailWord_991950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991981 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 5]
def baseStart_991981 : Nat := 118140960795 + 991981 * 2 ^ 59
def prefixEnd_991981 : Nat := 4983230072969 + 3 ^ 40 * 991981 * 2
def baseEnd_991981 : Nat := 226383579167906045989097

theorem tailTrace_991981 : CollatzResearch.WordTrace tailWord_991981 prefixEnd_991981 226383579167906045989097 := by
  unfold tailWord_991981
  simp only [CollatzResearch.WordTrace]
  refine ⟨36180519419229728711943797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24120346279486485807962531 36180519419229728711943797)
  ·
    refine ⟨3391923695552787066744731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36180519419229728711943797 3391923695552787066744731)
    ·
      refine ⟨5087885543329180600117097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391923695552787066744731 5087885543329180600117097)
      ·
        refine ⟨3815914157496885450087823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5087885543329180600117097 3815914157496885450087823)
        ·
          refine ⟨5723871236245328175131735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815914157496885450087823 5723871236245328175131735)
          ·
            refine ⟨8585806854367992262697603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723871236245328175131735 8585806854367992262697603)
            ·
              refine ⟨12878710281551988394046405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585806854367992262697603 12878710281551988394046405)
              ·
                refine ⟨2414758177790997823883701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12878710281551988394046405 2414758177790997823883701)
                ·
                  refine ⟨226383579167906045989097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2414758177790997823883701 226383579167906045989097)
                  ·
                    rfl

theorem cell21_991981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_991981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_991981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_991981 prefixEnd_991981 := by exact prefixLift 991981
  have htrace : WordTrace (prefixWord ++ tailWord_991981) baseStart_991981 baseEnd_991981 := by
    simpa [prefixWord, tailWord_991981, baseEnd_991981] using wordTrace_append hprefix tailTrace_991981
  have hstable : (prefixWord ++ tailWord_991981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991981).length < 2 ^ (prefixWord ++ tailWord_991981).sum := by decide
  have hdescent : baseEnd_991981 < baseStart_991981 := by decide
  rcases family_descends (prefixWord ++ tailWord_991981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992009 : List Nat := [1, 2, 1, 1, 3, 2, 11]
def baseStart_992009 : Nat := 118140960795 + 992009 * 2 ^ 59
def prefixEnd_992009 : Nat := 4983230072969 + 3 ^ 40 * 992009 * 2
def baseEnd_992009 : Nat := 25154441016598246613597

theorem tailTrace_992009 : CollatzResearch.WordTrace tailWord_992009 prefixEnd_992009 25154441016598246613597 := by
  unfold tailWord_992009
  simp only [CollatzResearch.WordTrace]
  refine ⟨36181540663128289493963081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24121027108752192995975387 36181540663128289493963081)
  ·
    refine ⟨27136155497346217120472311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36181540663128289493963081 27136155497346217120472311)
    ·
      refine ⟨40704233246019325680708467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27136155497346217120472311 40704233246019325680708467)
      ·
        refine ⟨61056349869028988521062701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40704233246019325680708467 61056349869028988521062701)
        ·
          refine ⟨22896131200885870695398513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61056349869028988521062701 22896131200885870695398513)
          ·
            refine ⟨17172098400664403021548885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22896131200885870695398513 17172098400664403021548885)
            ·
              refine ⟨25154441016598246613597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17172098400664403021548885 25154441016598246613597)
              ·
                rfl

theorem cell21_992009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 11].length) (baseStart_992009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992009 prefixEnd_992009 := by exact prefixLift 992009
  have htrace : WordTrace (prefixWord ++ tailWord_992009) baseStart_992009 baseEnd_992009 := by
    simpa [prefixWord, tailWord_992009, baseEnd_992009] using wordTrace_append hprefix tailTrace_992009
  have hstable : (prefixWord ++ tailWord_992009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992009).length < 2 ^ (prefixWord ++ tailWord_992009).sum := by decide
  have hdescent : baseEnd_992009 < baseStart_992009 := by decide
  rcases family_descends (prefixWord ++ tailWord_992009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992026 : List Nat := [3, 1, 1, 3, 2, 1, 4, 6]
def baseStart_992026 : Nat := 118140960795 + 992026 * 2 ^ 59
def prefixEnd_992026 : Nat := 4983230072969 + 3 ^ 40 * 992026 * 2
def baseEnd_992026 : Nat := 75464616260331989246335

theorem tailTrace_992026 : CollatzResearch.WordTrace tailWord_992026 prefixEnd_992026 75464616260331989246335 := by
  unfold tailWord_992026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9045540176016675349332983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24121440469377800931554621 9045540176016675349332983)
  ·
    refine ⟨13568310264025013023999475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9045540176016675349332983 13568310264025013023999475)
    ·
      refine ⟨20352465396037519535999213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13568310264025013023999475 20352465396037519535999213)
      ·
        refine ⟨7632174523514069825999705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20352465396037519535999213 7632174523514069825999705)
        ·
          refine ⟨5724130892635552369499779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7632174523514069825999705 5724130892635552369499779)
          ·
            refine ⟨8586196338953328554249669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724130892635552369499779 8586196338953328554249669)
            ·
              refine ⟨1609911813553749103921813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8586196338953328554249669 1609911813553749103921813)
              ·
                refine ⟨75464616260331989246335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1609911813553749103921813 75464616260331989246335)
                ·
                  rfl

theorem cell21_992026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_992026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992026 prefixEnd_992026 := by exact prefixLift 992026
  have htrace : WordTrace (prefixWord ++ tailWord_992026) baseStart_992026 baseEnd_992026 := by
    simpa [prefixWord, tailWord_992026, baseEnd_992026] using wordTrace_append hprefix tailTrace_992026
  have hstable : (prefixWord ++ tailWord_992026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992026).length < 2 ^ (prefixWord ++ tailWord_992026).sum := by decide
  have hdescent : baseEnd_992026 < baseStart_992026 := by decide
  rcases family_descends (prefixWord ++ tailWord_992026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992077 : List Nat := [1, 6, 1, 2, 3, 1, 1, 6]
def baseStart_992077 : Nat := 118140960795 + 992077 * 2 ^ 59
def prefixEnd_992077 : Nat := 4983230072969 + 3 ^ 40 * 992077 * 2
def baseEnd_992077 : Nat := 75468495891943737462967

theorem tailTrace_992077 : CollatzResearch.WordTrace tailWord_992077 prefixEnd_992077 75468495891943737462967 := by
  unfold tailWord_992077
  simp only [CollatzResearch.WordTrace]
  refine ⟨36184020826881937107438485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24122680551254624738292323 36184020826881937107438485)
  ·
    refine ⟨1696125976260090801911179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36184020826881937107438485 1696125976260090801911179)
    ·
      refine ⟨2544188964390136202866769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696125976260090801911179 2544188964390136202866769)
      ·
        refine ⟨1908141723292602152150077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2544188964390136202866769 1908141723292602152150077)
        ·
          refine ⟨715553146234725807056279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1908141723292602152150077 715553146234725807056279)
          ·
            refine ⟨1073329719352088710584419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715553146234725807056279 1073329719352088710584419)
            ·
              refine ⟨1609994579028133065876629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073329719352088710584419 1609994579028133065876629)
              ·
                refine ⟨75468495891943737462967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1609994579028133065876629 75468495891943737462967)
                ·
                  rfl

theorem cell21_992077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 6].length) (baseStart_992077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992077 prefixEnd_992077 := by exact prefixLift 992077
  have htrace : WordTrace (prefixWord ++ tailWord_992077) baseStart_992077 baseEnd_992077 := by
    simpa [prefixWord, tailWord_992077, baseEnd_992077] using wordTrace_append hprefix tailTrace_992077
  have hstable : (prefixWord ++ tailWord_992077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992077).length < 2 ^ (prefixWord ++ tailWord_992077).sum := by decide
  have hdescent : baseEnd_992077 < baseStart_992077 := by decide
  rcases family_descends (prefixWord ++ tailWord_992077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992133 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 5]
def baseStart_992133 : Nat := 118140960795 + 992133 * 2 ^ 59
def prefixEnd_992133 : Nat := 4983230072969 + 3 ^ 40 * 992133 * 2
def baseEnd_992133 : Nat := 226418267638787559455453

theorem tailTrace_992133 : CollatzResearch.WordTrace tailWord_992133 prefixEnd_992133 226418267638787559455453 := by
  unfold tailWord_992133
  simp only [CollatzResearch.WordTrace]
  refine ⟨36186063314679058671477053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24124042209786039114318035 36186063314679058671477053)
  ·
    refine ⟨13569773743004647001803895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36186063314679058671477053 13569773743004647001803895)
    ·
      refine ⟨20354660614506970502705843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569773743004647001803895 20354660614506970502705843)
      ·
        refine ⟨30531990921760455754058765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20354660614506970502705843 30531990921760455754058765)
        ·
          refine ⟨11449496595660170907772037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30531990921760455754058765 11449496595660170907772037)
          ·
            refine ⟨2146780611686282045207257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11449496595660170907772037 2146780611686282045207257)
            ·
              refine ⟨1610085458764711533905443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146780611686282045207257 1610085458764711533905443)
              ·
                refine ⟨2415128188147067300858165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610085458764711533905443 2415128188147067300858165)
                ·
                  refine ⟨226418267638787559455453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2415128188147067300858165 226418267638787559455453)
                  ·
                    rfl

theorem cell21_992133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_992133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992133 prefixEnd_992133 := by exact prefixLift 992133
  have htrace : WordTrace (prefixWord ++ tailWord_992133) baseStart_992133 baseEnd_992133 := by
    simpa [prefixWord, tailWord_992133, baseEnd_992133] using wordTrace_append hprefix tailTrace_992133
  have hstable : (prefixWord ++ tailWord_992133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992133).length < 2 ^ (prefixWord ++ tailWord_992133).sum := by decide
  have hdescent : baseEnd_992133 < baseStart_992133 := by decide
  rcases family_descends (prefixWord ++ tailWord_992133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992237 : List Nat := [1, 5, 1, 14]
def baseStart_992237 : Nat := 118140960795 + 992237 * 2 ^ 59
def prefixEnd_992237 : Nat := 4983230072969 + 3 ^ 40 * 992237 * 2
def baseEnd_992237 : Nat := 931860089941178970049

theorem tailTrace_992237 : CollatzResearch.WordTrace tailWord_992237 prefixEnd_992237 931860089941178970049 := by
  unfold tailWord_992237
  simp only [CollatzResearch.WordTrace]
  refine ⟨36189856506302284433262965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24126571004201522955508643 36189856506302284433262965)
  ·
    refine ⟨3392799047465839165618403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36189856506302284433262965 3392799047465839165618403)
    ·
      refine ⟨5089198571198758748427605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392799047465839165618403 5089198571198758748427605)
      ·
        refine ⟨931860089941178970049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 5089198571198758748427605 931860089941178970049)
        ·
          rfl

theorem cell21_992237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 14].length) (baseStart_992237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992237 prefixEnd_992237 := by exact prefixLift 992237
  have htrace : WordTrace (prefixWord ++ tailWord_992237) baseStart_992237 baseEnd_992237 := by
    simpa [prefixWord, tailWord_992237, baseEnd_992237] using wordTrace_append hprefix tailTrace_992237
  have hstable : (prefixWord ++ tailWord_992237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992237).length < 2 ^ (prefixWord ++ tailWord_992237).sum := by decide
  have hdescent : baseEnd_992237 < baseStart_992237 := by decide
  rcases family_descends (prefixWord ++ tailWord_992237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992268 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_992268 : Nat := 118140960795 + 992268 * 2 ^ 59
def prefixEnd_992268 : Nat := 4983230072969 + 3 ^ 40 * 992268 * 2
def baseEnd_992268 : Nat := 226449076478057324705177

theorem tailTrace_992268 : CollatzResearch.WordTrace tailWord_992268 prefixEnd_992268 226449076478057324705177 := by
  unfold tailWord_992268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18095493584594988363820729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24127324779459984485094305 18095493584594988363820729)
  ·
    refine ⟨13571620188446241272865547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18095493584594988363820729 13571620188446241272865547)
    ·
      refine ⟨20357430282669361909298321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13571620188446241272865547 20357430282669361909298321)
      ·
        refine ⟨15268072712002021431973741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20357430282669361909298321 15268072712002021431973741)
        ·
          refine ⟨5725527267000758036990153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15268072712002021431973741 5725527267000758036990153)
          ·
            refine ⟨4294145450250568527742615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5725527267000758036990153 4294145450250568527742615)
            ·
              refine ⟨6441218175375852791613923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294145450250568527742615 6441218175375852791613923)
              ·
                refine ⟨9661827263063779187420885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441218175375852791613923 9661827263063779187420885)
                ·
                  refine ⟨226449076478057324705177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9661827263063779187420885 226449076478057324705177)
                  ·
                    rfl

theorem cell21_992268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_992268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992268 prefixEnd_992268 := by exact prefixLift 992268
  have htrace : WordTrace (prefixWord ++ tailWord_992268) baseStart_992268 baseEnd_992268 := by
    simpa [prefixWord, tailWord_992268, baseEnd_992268] using wordTrace_append hprefix tailTrace_992268
  have hstable : (prefixWord ++ tailWord_992268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992268).length < 2 ^ (prefixWord ++ tailWord_992268).sum := by decide
  have hdescent : baseEnd_992268 < baseStart_992268 := by decide
  rcases family_descends (prefixWord ++ tailWord_992268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992302 : List Nat := [4, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_992302 : Nat := 118140960795 + 992302 * 2 ^ 59
def prefixEnd_992302 : Nat := 4983230072969 + 3 ^ 40 * 992302 * 2
def baseEnd_992302 : Nat := 226456835741280821138441

theorem tailTrace_992302 : CollatzResearch.WordTrace tailWord_992302 prefixEnd_992302 226456835741280821138441 := by
  unfold tailWord_992302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524028406383350066797395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24128151500711200356252773 4524028406383350066797395)
  ·
    refine ⟨6786042609575025100196093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4524028406383350066797395 6786042609575025100196093)
    ·
      refine ⟨2544765978590634412573535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6786042609575025100196093 2544765978590634412573535)
      ·
        refine ⟨3817148967885951618860303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544765978590634412573535 3817148967885951618860303)
        ·
          refine ⟨5725723451828927428290455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3817148967885951618860303 5725723451828927428290455)
          ·
            refine ⟨8588585177743391142435683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5725723451828927428290455 8588585177743391142435683)
            ·
              refine ⟨12882877766615086713653525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588585177743391142435683 12882877766615086713653525)
              ·
                refine ⟨603884895310082189702509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12882877766615086713653525 603884895310082189702509)
                ·
                  refine ⟨226456835741280821138441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603884895310082189702509 226456835741280821138441)
                  ·
                    rfl

theorem cell21_992302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_992302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992302 prefixEnd_992302 := by exact prefixLift 992302
  have htrace : WordTrace (prefixWord ++ tailWord_992302) baseStart_992302 baseEnd_992302 := by
    simpa [prefixWord, tailWord_992302, baseEnd_992302] using wordTrace_append hprefix tailTrace_992302
  have hstable : (prefixWord ++ tailWord_992302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992302).length < 2 ^ (prefixWord ++ tailWord_992302).sum := by decide
  have hdescent : baseEnd_992302 < baseStart_992302 := by decide
  rcases family_descends (prefixWord ++ tailWord_992302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992330 : List Nat := [3, 1, 2, 1, 1, 2, 6, 5]
def baseStart_992330 : Nat := 118140960795 + 992330 * 2 ^ 59
def prefixEnd_992330 : Nat := 4983230072969 + 3 ^ 40 * 992330 * 2
def baseEnd_992330 : Nat := 75487741907586331557239

theorem tailTrace_992330 : CollatzResearch.WordTrace tailWord_992330 prefixEnd_992330 75487741907586331557239 := by
  unfold tailWord_992330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048312123741340329099611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24128832329976907544265629 9048312123741340329099611)
  ·
    refine ⟨13572468185612010493649417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9048312123741340329099611 13572468185612010493649417)
    ·
      refine ⟨10179351139209007870237063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13572468185612010493649417 10179351139209007870237063)
      ·
        refine ⟨15269026708813511805355595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179351139209007870237063 15269026708813511805355595)
        ·
          refine ⟨22903540063220267708033393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15269026708813511805355595 22903540063220267708033393)
          ·
            refine ⟨17177655047415200781025045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22903540063220267708033393 17177655047415200781025045)
            ·
              refine ⟨805202580347587536610549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17177655047415200781025045 805202580347587536610549)
              ·
                refine ⟨75487741907586331557239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805202580347587536610549 75487741907586331557239)
                ·
                  rfl

theorem cell21_992330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_992330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992330 prefixEnd_992330 := by exact prefixLift 992330
  have htrace : WordTrace (prefixWord ++ tailWord_992330) baseStart_992330 baseEnd_992330 := by
    simpa [prefixWord, tailWord_992330, baseEnd_992330] using wordTrace_append hprefix tailTrace_992330
  have hstable : (prefixWord ++ tailWord_992330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992330).length < 2 ^ (prefixWord ++ tailWord_992330).sum := by decide
  have hdescent : baseEnd_992330 < baseStart_992330 := by decide
  rcases family_descends (prefixWord ++ tailWord_992330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992361 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 5]
def baseStart_992361 : Nat := 118140960795 + 992361 * 2 ^ 59
def prefixEnd_992361 : Nat := 4983230072969 + 3 ^ 40 * 992361 * 2
def baseEnd_992361 : Nat := 226470300345109829654987

theorem tailTrace_992361 : CollatzResearch.WordTrace tailWord_992361 prefixEnd_992361 226470300345109829654987 := by
  unfold tailWord_992361
  simp only [CollatzResearch.WordTrace]
  refine ⟨36194379157853053610776937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24129586105235369073851291 36194379157853053610776937)
  ·
    refine ⟨27145784368389790208082703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36194379157853053610776937 27145784368389790208082703)
    ·
      refine ⟨40718676552584685312124055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27145784368389790208082703 40718676552584685312124055)
      ·
        refine ⟨61078014828877027968186083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40718676552584685312124055 61078014828877027968186083)
        ·
          refine ⟨91617022243315541952279125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61078014828877027968186083 91617022243315541952279125)
          ·
            refine ⟨1073636979413854007253271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 91617022243315541952279125 1073636979413854007253271)
            ·
              refine ⟨1610455469120781010879907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073636979413854007253271 1610455469120781010879907)
              ·
                refine ⟨2415683203681171516319861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610455469120781010879907 2415683203681171516319861)
                ·
                  refine ⟨226470300345109829654987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2415683203681171516319861 226470300345109829654987)
                  ·
                    rfl

theorem cell21_992361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_992361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992361 prefixEnd_992361 := by exact prefixLift 992361
  have htrace : WordTrace (prefixWord ++ tailWord_992361) baseStart_992361 baseEnd_992361 := by
    simpa [prefixWord, tailWord_992361, baseEnd_992361] using wordTrace_append hprefix tailTrace_992361
  have hstable : (prefixWord ++ tailWord_992361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992361).length < 2 ^ (prefixWord ++ tailWord_992361).sum := by decide
  have hdescent : baseEnd_992361 < baseStart_992361 := by decide
  rcases family_descends (prefixWord ++ tailWord_992361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992375 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 4]
def baseStart_992375 : Nat := 118140960795 + 992375 * 2 ^ 59
def prefixEnd_992375 : Nat := 4983230072969 + 3 ^ 40 * 992375 * 2
def baseEnd_992375 : Nat := 226473495335848916421625

theorem tailTrace_992375 : CollatzResearch.WordTrace tailWord_992375 prefixEnd_992375 226473495335848916421625 := by
  unfold tailWord_992375
  simp only [CollatzResearch.WordTrace]
  refine ⟨36194889779802334001786579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24129926519868222667857719 36194889779802334001786579)
  ·
    refine ⟨54292334669703501002679869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36194889779802334001786579 54292334669703501002679869)
    ·
      refine ⟨20359625501138812876004951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54292334669703501002679869 20359625501138812876004951)
      ·
        refine ⟨30539438251708219314007427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20359625501138812876004951 30539438251708219314007427)
        ·
          refine ⟨45809157377562328971011141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30539438251708219314007427 45809157377562328971011141)
          ·
            refine ⟨8589217008292936682064589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45809157377562328971011141 8589217008292936682064589)
            ·
              refine ⟨3220956378109851255774221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8589217008292936682064589 3220956378109851255774221)
              ·
                refine ⟨1207858641791194220915333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3220956378109851255774221 1207858641791194220915333)
                ·
                  refine ⟨226473495335848916421625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207858641791194220915333 226473495335848916421625)
                  ·
                    rfl

theorem cell21_992375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_992375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992375 prefixEnd_992375 := by exact prefixLift 992375
  have htrace : WordTrace (prefixWord ++ tailWord_992375) baseStart_992375 baseEnd_992375 := by
    simpa [prefixWord, tailWord_992375, baseEnd_992375] using wordTrace_append hprefix tailTrace_992375
  have hstable : (prefixWord ++ tailWord_992375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992375).length < 2 ^ (prefixWord ++ tailWord_992375).sum := by decide
  have hdescent : baseEnd_992375 < baseStart_992375 := by decide
  rcases family_descends (prefixWord ++ tailWord_992375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992423 : List Nat := [1, 1, 6, 2, 1, 3, 1, 6]
def baseStart_992423 : Nat := 118140960795 + 992423 * 2 ^ 59
def prefixEnd_992423 : Nat := 4983230072969 + 3 ^ 40 * 992423 * 2
def baseEnd_992423 : Nat := 75494816529937166540509

theorem tailTrace_992423 : CollatzResearch.WordTrace tailWord_992423 prefixEnd_992423 75494816529937166540509 := by
  unfold tailWord_992423
  simp only [CollatzResearch.WordTrace]
  refine ⟨36196640483628438199533923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24131093655752292133022615 36196640483628438199533923)
  ·
    refine ⟨54294960725442657299300885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36196640483628438199533923 54294960725442657299300885)
    ·
      refine ⟨2545076284005124560904729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54294960725442657299300885 2545076284005124560904729)
      ·
        refine ⟨1908807213003843420678547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2545076284005124560904729 1908807213003843420678547)
        ·
          refine ⟨2863210819505765131017821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908807213003843420678547 2863210819505765131017821)
          ·
            refine ⟨1073704057314661924131683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2863210819505765131017821 1073704057314661924131683)
            ·
              refine ⟨1610556085971992886197525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073704057314661924131683 1610556085971992886197525)
              ·
                refine ⟨75494816529937166540509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1610556085971992886197525 75494816529937166540509)
                ·
                  rfl

theorem cell21_992423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 6].length) (baseStart_992423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992423 prefixEnd_992423 := by exact prefixLift 992423
  have htrace : WordTrace (prefixWord ++ tailWord_992423) baseStart_992423 baseEnd_992423 := by
    simpa [prefixWord, tailWord_992423, baseEnd_992423] using wordTrace_append hprefix tailTrace_992423
  have hstable : (prefixWord ++ tailWord_992423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992423).length < 2 ^ (prefixWord ++ tailWord_992423).sum := by decide
  have hdescent : baseEnd_992423 < baseStart_992423 := by decide
  rcases family_descends (prefixWord ++ tailWord_992423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992485 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 4]
def baseStart_992485 : Nat := 118140960795 + 992485 * 2 ^ 59
def prefixEnd_992485 : Nat := 4983230072969 + 3 ^ 40 * 992485 * 2
def baseEnd_992485 : Nat := 226498598834513169588067

theorem tailTrace_992485 : CollatzResearch.WordTrace tailWord_992485 prefixEnd_992485 226498598834513169588067 := by
  unfold tailWord_992485
  simp only [CollatzResearch.WordTrace]
  refine ⟨36198901809403822788290909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24132601206269215192193939 36198901809403822788290909)
  ·
    refine ⟨13574588178526433545609091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36198901809403822788290909 13574588178526433545609091)
    ·
      refine ⟨20361882267789650318413637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13574588178526433545609091 20361882267789650318413637)
      ·
        refine ⟨3817852925210559434702557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20361882267789650318413637 3817852925210559434702557)
        ·
          refine ⟨1431694846953959788013459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3817852925210559434702557 1431694846953959788013459)
          ·
            refine ⟨2147542270430939682020189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431694846953959788013459 2147542270430939682020189)
            ·
              refine ⟨805328351411602380757571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2147542270430939682020189 805328351411602380757571)
              ·
                refine ⟨1207992527117403571136357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805328351411602380757571 1207992527117403571136357)
                ·
                  refine ⟨226498598834513169588067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207992527117403571136357 226498598834513169588067)
                  ·
                    rfl

theorem cell21_992485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_992485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992485 prefixEnd_992485 := by exact prefixLift 992485
  have htrace : WordTrace (prefixWord ++ tailWord_992485) baseStart_992485 baseEnd_992485 := by
    simpa [prefixWord, tailWord_992485, baseEnd_992485] using wordTrace_append hprefix tailTrace_992485
  have hstable : (prefixWord ++ tailWord_992485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992485).length < 2 ^ (prefixWord ++ tailWord_992485).sum := by decide
  have hdescent : baseEnd_992485 < baseStart_992485 := by decide
  rcases family_descends (prefixWord ++ tailWord_992485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992544 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_992544 : Nat := 118140960795 + 992544 * 2 ^ 59
def prefixEnd_992544 : Nat := 4983230072969 + 3 ^ 40 * 992544 * 2
def baseEnd_992544 : Nat := 226512063438342178104613

theorem tailTrace_992544 : CollatzResearch.WordTrace tailWord_992544 prefixEnd_992544 226512063438342178104613 := by
  unfold tailWord_992544
  simp only [CollatzResearch.WordTrace]
  refine ⟨18100526858095037932344343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24134035810793383909792457 18100526858095037932344343)
  ·
    refine ⟨27150790287142556898516515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18100526858095037932344343 27150790287142556898516515)
    ·
      refine ⟨40726185430713835347774773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27150790287142556898516515 40726185430713835347774773)
      ·
        refine ⟨3818079884129422063853885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40726185430713835347774773 3818079884129422063853885)
        ·
          refine ⟨1431779956548533273945207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3818079884129422063853885 1431779956548533273945207)
          ·
            refine ⟨2147669934822799910917811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431779956548533273945207 2147669934822799910917811)
            ·
              refine ⟨3221504902234199866376717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147669934822799910917811 3221504902234199866376717)
              ·
                refine ⟨1208064338337824949891269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3221504902234199866376717 1208064338337824949891269)
                ·
                  refine ⟨226512063438342178104613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208064338337824949891269 226512063438342178104613)
                  ·
                    rfl

theorem cell21_992544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_992544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992544 prefixEnd_992544 := by exact prefixLift 992544
  have htrace : WordTrace (prefixWord ++ tailWord_992544) baseStart_992544 baseEnd_992544 := by
    simpa [prefixWord, tailWord_992544, baseEnd_992544] using wordTrace_append hprefix tailTrace_992544
  have hstable : (prefixWord ++ tailWord_992544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992544).length < 2 ^ (prefixWord ++ tailWord_992544).sum := by decide
  have hdescent : baseEnd_992544 < baseStart_992544 := by decide
  rcases family_descends (prefixWord ++ tailWord_992544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992586 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_992586 : Nat := 118140960795 + 992586 * 2 ^ 59
def prefixEnd_992586 : Nat := 4983230072969 + 3 ^ 40 * 992586 * 2
def baseEnd_992586 : Nat := 226521648410559438404527

theorem tailTrace_992586 : CollatzResearch.WordTrace tailWord_992586 prefixEnd_992586 226521648410559438404527 := by
  unfold tailWord_992586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9050646395509479259429403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24135057054691944691811741 9050646395509479259429403)
  ·
    refine ⟨13575969593264218889144105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9050646395509479259429403 13575969593264218889144105)
    ·
      refine ⟨10181977194948164166858079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13575969593264218889144105 10181977194948164166858079)
      ·
        refine ⟨15272965792422246250287119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10181977194948164166858079 15272965792422246250287119)
        ·
          refine ⟨22909448688633369375430679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15272965792422246250287119 22909448688633369375430679)
          ·
            refine ⟨34364173032950054063146019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22909448688633369375430679 34364173032950054063146019)
            ·
              refine ⟨51546259549425081094719029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34364173032950054063146019 51546259549425081094719029)
              ·
                refine ⟨4832461832758601352629909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51546259549425081094719029 4832461832758601352629909)
                ·
                  refine ⟨226521648410559438404527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4832461832758601352629909 226521648410559438404527)
                  ·
                    rfl

theorem cell21_992586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_992586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992586 prefixEnd_992586 := by exact prefixLift 992586
  have htrace : WordTrace (prefixWord ++ tailWord_992586) baseStart_992586 baseEnd_992586 := by
    simpa [prefixWord, tailWord_992586, baseEnd_992586] using wordTrace_append hprefix tailTrace_992586
  have hstable : (prefixWord ++ tailWord_992586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992586).length < 2 ^ (prefixWord ++ tailWord_992586).sum := by decide
  have hdescent : baseEnd_992586 < baseStart_992586 := by decide
  rcases family_descends (prefixWord ++ tailWord_992586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992631 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 7]
def baseStart_992631 : Nat := 118140960795 + 992631 * 2 ^ 59
def prefixEnd_992631 : Nat := 4983230072969 + 3 ^ 40 * 992631 * 2
def baseEnd_992631 : Nat := 226531918023649360154435

theorem tailTrace_992631 : CollatzResearch.WordTrace tailWord_992631 prefixEnd_992631 226531918023649360154435 := by
  unfold tailWord_992631
  simp only [CollatzResearch.WordTrace]
  refine ⟨36204226866874889723105747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24136151244583259815403831 36204226866874889723105747)
  ·
    refine ⟨54306340300312334584658621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36204226866874889723105747 54306340300312334584658621)
    ·
      refine ⟨20364877612617125469246983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54306340300312334584658621 20364877612617125469246983)
      ·
        refine ⟨30547316418925688203870475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20364877612617125469246983 30547316418925688203870475)
        ·
          refine ⟨45820974628388532305805713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30547316418925688203870475 45820974628388532305805713)
          ·
            refine ⟨34365730971291399229354285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45820974628388532305805713 34365730971291399229354285)
            ·
              refine ⟨12887149114234274711007857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34365730971291399229354285 12887149114234274711007857)
              ·
                refine ⟨9665361835675706033255893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12887149114234274711007857 9665361835675706033255893)
                ·
                  refine ⟨226531918023649360154435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9665361835675706033255893 226531918023649360154435)
                  ·
                    rfl

theorem cell21_992631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_992631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992631 prefixEnd_992631 := by exact prefixLift 992631
  have htrace : WordTrace (prefixWord ++ tailWord_992631) baseStart_992631 baseEnd_992631 := by
    simpa [prefixWord, tailWord_992631, baseEnd_992631] using wordTrace_append hprefix tailTrace_992631
  have hstable : (prefixWord ++ tailWord_992631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992631).length < 2 ^ (prefixWord ++ tailWord_992631).sum := by decide
  have hdescent : baseEnd_992631 < baseStart_992631 := by decide
  rcases family_descends (prefixWord ++ tailWord_992631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992648 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_992648 : Nat := 118140960795 + 992648 * 2 ^ 59
def prefixEnd_992648 : Nat := 4983230072969 + 3 ^ 40 * 992648 * 2
def baseEnd_992648 : Nat := 226535797655261108371067

theorem tailTrace_992648 : CollatzResearch.WordTrace tailWord_992648 prefixEnd_992648 226535797655261108371067 := by
  unfold tailWord_992648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102423453906650813237299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24136564605208867750983065 18102423453906650813237299)
  ·
    refine ⟨27153635180859976219855949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18102423453906650813237299 27153635180859976219855949)
    ·
      refine ⟨10182613192822491082445981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27153635180859976219855949 10182613192822491082445981)
      ·
        refine ⟨3818479947308434155917243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10182613192822491082445981 3818479947308434155917243)
        ·
          refine ⟨5727719920962651233875865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818479947308434155917243 5727719920962651233875865)
          ·
            refine ⟨4295789940721988425406899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727719920962651233875865 4295789940721988425406899)
            ·
              refine ⟨6443684911082982638110349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295789940721988425406899 6443684911082982638110349)
              ·
                refine ⟨2416381841656118489291381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6443684911082982638110349 2416381841656118489291381)
                ·
                  refine ⟨226535797655261108371067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2416381841656118489291381 226535797655261108371067)
                  ·
                    rfl

theorem cell21_992648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_992648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992648 prefixEnd_992648 := by exact prefixLift 992648
  have htrace : WordTrace (prefixWord ++ tailWord_992648) baseStart_992648 baseEnd_992648 := by
    simpa [prefixWord, tailWord_992648, baseEnd_992648] using wordTrace_append hprefix tailTrace_992648
  have hstable : (prefixWord ++ tailWord_992648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992648).length < 2 ^ (prefixWord ++ tailWord_992648).sum := by decide
  have hdescent : baseEnd_992648 < baseStart_992648 := by decide
  rcases family_descends (prefixWord ++ tailWord_992648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992668 : List Nat := [2, 2, 3, 4, 1, 2, 2, 5]
def baseStart_992668 : Nat := 118140960795 + 992668 * 2 ^ 59
def prefixEnd_992668 : Nat := 4983230072969 + 3 ^ 40 * 992668 * 2
def baseEnd_992668 : Nat := 75513453975915172679231

theorem tailTrace_992668 : CollatzResearch.WordTrace tailWord_992668 prefixEnd_992668 75513453975915172679231 := by
  unfold tailWord_992668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102788183870422521101329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24137050911827230028135105 18102788183870422521101329)
  ·
    refine ⟨13577091137902816890825997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18102788183870422521101329 13577091137902816890825997)
    ·
      refine ⟨5091409176713556334059749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13577091137902816890825997 5091409176713556334059749)
      ·
        refine ⟨954639220633791812636203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5091409176713556334059749 954639220633791812636203)
        ·
          refine ⟨1431958830950687718954305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954639220633791812636203 1431958830950687718954305)
          ·
            refine ⟨1073969123213015789215729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431958830950687718954305 1073969123213015789215729)
            ·
              refine ⟨805476842409761841911797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073969123213015789215729 805476842409761841911797)
              ·
                refine ⟨75513453975915172679231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805476842409761841911797 75513453975915172679231)
                ·
                  rfl

theorem cell21_992668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_992668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992668 prefixEnd_992668 := by exact prefixLift 992668
  have htrace : WordTrace (prefixWord ++ tailWord_992668) baseStart_992668 baseEnd_992668 := by
    simpa [prefixWord, tailWord_992668, baseEnd_992668] using wordTrace_append hprefix tailTrace_992668
  have hstable : (prefixWord ++ tailWord_992668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992668).length < 2 ^ (prefixWord ++ tailWord_992668).sum := by decide
  have hdescent : baseEnd_992668 < baseStart_992668 := by decide
  rcases family_descends (prefixWord ++ tailWord_992668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992693 : List Nat := [1, 3, 3, 2, 2, 1, 9]
def baseStart_992693 : Nat := 118140960795 + 992693 * 2 ^ 59
def prefixEnd_992693 : Nat := 4983230072969 + 3 ^ 40 * 992693 * 2
def baseEnd_992693 : Nat := 25171785252039003346775

theorem tailTrace_992693 : CollatzResearch.WordTrace tailWord_992693 prefixEnd_992693 25171785252039003346775 := by
  unfold tailWord_992693
  simp only [CollatzResearch.WordTrace]
  refine ⟨36206488192650274311862733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24137658795100182874575155 36206488192650274311862733)
  ·
    refine ⟨13577433072243852866948525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36206488192650274311862733 13577433072243852866948525)
    ·
      refine ⟨5091537402091444825105697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13577433072243852866948525 5091537402091444825105697)
      ·
        refine ⟨3818653051568583618829273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5091537402091444825105697 3818653051568583618829273)
        ·
          refine ⟨2863989788676437714121955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3818653051568583618829273 2863989788676437714121955)
          ·
            refine ⟨4295984683014656571182933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863989788676437714121955 4295984683014656571182933)
            ·
              refine ⟨25171785252039003346775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4295984683014656571182933 25171785252039003346775)
              ·
                rfl

theorem cell21_992693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 9].length) (baseStart_992693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992693 prefixEnd_992693 := by exact prefixLift 992693
  have htrace : WordTrace (prefixWord ++ tailWord_992693) baseStart_992693 baseEnd_992693 := by
    simpa [prefixWord, tailWord_992693, baseEnd_992693] using wordTrace_append hprefix tailTrace_992693
  have hstable : (prefixWord ++ tailWord_992693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992693).length < 2 ^ (prefixWord ++ tailWord_992693).sum := by decide
  have hdescent : baseEnd_992693 < baseStart_992693 := by decide
  rcases family_descends (prefixWord ++ tailWord_992693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992752 : List Nat := [2, 1, 1, 1, 3, 13]
def baseStart_992752 : Nat := 118140960795 + 992752 * 2 ^ 59
def prefixEnd_992752 : Nat := 4983230072969 + 3 ^ 40 * 992752 * 2
def baseEnd_992752 : Nat := 8391093773043705134723

theorem tailTrace_992752 : CollatzResearch.WordTrace tailWord_992752 prefixEnd_992752 8391093773043705134723 := by
  unfold tailWord_992752
  simp only [CollatzResearch.WordTrace]
  refine ⟨18104320049718263694130255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24139093399624351592173673 18104320049718263694130255)
  ·
    refine ⟨27156480074577395541195383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18104320049718263694130255 27156480074577395541195383)
    ·
      refine ⟨40734720111866093311793075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27156480074577395541195383 40734720111866093311793075)
      ·
        refine ⟨61102080167799139967689613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40734720111866093311793075 61102080167799139967689613)
        ·
          refine ⟨22913280062924677487883605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61102080167799139967689613 22913280062924677487883605)
          ·
            refine ⟨8391093773043705134723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 22913280062924677487883605 8391093773043705134723)
            ·
              rfl

theorem cell21_992752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 13].length) (baseStart_992752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992752 prefixEnd_992752 := by exact prefixLift 992752
  have htrace : WordTrace (prefixWord ++ tailWord_992752) baseStart_992752 baseEnd_992752 := by
    simpa [prefixWord, tailWord_992752, baseEnd_992752] using wordTrace_append hprefix tailTrace_992752
  have hstable : (prefixWord ++ tailWord_992752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992752).length < 2 ^ (prefixWord ++ tailWord_992752).sum := by decide
  have hdescent : baseEnd_992752 < baseStart_992752 := by decide
  rcases family_descends (prefixWord ++ tailWord_992752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992758 : List Nat := [5, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_992758 : Nat := 118140960795 + 992758 * 2 ^ 59
def prefixEnd_992758 : Nat := 4983230072969 + 3 ^ 40 * 992758 * 2
def baseEnd_992758 : Nat := 226560901153925361537509

theorem tailTrace_992758 : CollatzResearch.WordTrace tailWord_992758 prefixEnd_992758 226560901153925361537509 := by
  unfold tailWord_992758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263053683588424400811183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24139239291609860275319285 2263053683588424400811183)
  ·
    refine ⟨3394580525382636601216775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263053683588424400811183 3394580525382636601216775)
    ·
      refine ⟨5091870788073954901825163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3394580525382636601216775 5091870788073954901825163)
      ·
        refine ⟨7637806182110932352737745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091870788073954901825163 7637806182110932352737745)
        ·
          refine ⟨5728354636583199264553309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7637806182110932352737745 5728354636583199264553309)
          ·
            refine ⟨2148132988718699724207491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5728354636583199264553309 2148132988718699724207491)
            ·
              refine ⟨3222199483078049586311237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148132988718699724207491 3222199483078049586311237)
              ·
                refine ⟨604162403077134297433357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3222199483078049586311237 604162403077134297433357)
                ·
                  refine ⟨226560901153925361537509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604162403077134297433357 226560901153925361537509)
                  ·
                    rfl

theorem cell21_992758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_992758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992758 prefixEnd_992758 := by exact prefixLift 992758
  have htrace : WordTrace (prefixWord ++ tailWord_992758) baseStart_992758 baseEnd_992758 := by
    simpa [prefixWord, tailWord_992758, baseEnd_992758] using wordTrace_append hprefix tailTrace_992758
  have hstable : (prefixWord ++ tailWord_992758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992758).length < 2 ^ (prefixWord ++ tailWord_992758).sum := by decide
  have hdescent : baseEnd_992758 < baseStart_992758 := by decide
  rcases family_descends (prefixWord ++ tailWord_992758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992924 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_992924 : Nat := 118140960795 + 992924 * 2 ^ 59
def prefixEnd_992924 : Nat := 4983230072969 + 3 ^ 40 * 992924 * 2
def baseEnd_992924 : Nat := 226598784615545961770503

theorem tailTrace_992924 : CollatzResearch.WordTrace tailWord_992924 prefixEnd_992924 226598784615545961770503 := by
  unfold tailWord_992924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18107456727406700381760913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24143275636542267175681217 18107456727406700381760913)
  ·
    refine ⟨13580592545555025286320685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18107456727406700381760913 13580592545555025286320685)
    ·
      refine ⟨5092722204583134482370257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13580592545555025286320685 5092722204583134482370257)
      ·
        refine ⟨3819541653437350861777693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5092722204583134482370257 3819541653437350861777693)
        ·
          refine ⟨1432328120039006573166635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3819541653437350861777693 1432328120039006573166635)
          ·
            refine ⟨2148492180058509859749953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432328120039006573166635 2148492180058509859749953)
            ·
              refine ⟨1611369135043882394812465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148492180058509859749953 1611369135043882394812465)
              ·
                refine ⟨1208526851282911796109349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611369135043882394812465 1208526851282911796109349)
                ·
                  refine ⟨226598784615545961770503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208526851282911796109349 226598784615545961770503)
                  ·
                    rfl

theorem cell21_992924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_992924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_992924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_992924 prefixEnd_992924 := by exact prefixLift 992924
  have htrace : WordTrace (prefixWord ++ tailWord_992924) baseStart_992924 baseEnd_992924 := by
    simpa [prefixWord, tailWord_992924, baseEnd_992924] using wordTrace_append hprefix tailTrace_992924
  have hstable : (prefixWord ++ tailWord_992924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992924).length < 2 ^ (prefixWord ++ tailWord_992924).sum := by decide
  have hdescent : baseEnd_992924 < baseStart_992924 := by decide
  rcases family_descends (prefixWord ++ tailWord_992924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993000 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_993000 : Nat := 118140960795 + 993000 * 2 ^ 59
def prefixEnd_993000 : Nat := 4983230072969 + 3 ^ 40 * 993000 * 2
def baseEnd_993000 : Nat := 226616128850986718503681

theorem tailTrace_993000 : CollatzResearch.WordTrace tailWord_993000 prefixEnd_993000 226616128850986718503681 := by
  unfold tailWord_993000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18108842701269032871644227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24145123601692043828858969 18108842701269032871644227)
  ·
    refine ⟨27163264051903549307466341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18108842701269032871644227 27163264051903549307466341)
    ·
      refine ⟨5093112009731915495149939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27163264051903549307466341 5093112009731915495149939)
      ·
        refine ⟨7639668014597873242724909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093112009731915495149939 7639668014597873242724909)
        ·
          refine ⟨2864875505474202466021841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7639668014597873242724909 2864875505474202466021841)
          ·
            refine ⟨2148656629105651849516381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864875505474202466021841 2148656629105651849516381)
            ·
              refine ⟨805746235914619443568643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2148656629105651849516381 805746235914619443568643)
              ·
                refine ⟨1208619353871929165352965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805746235914619443568643 1208619353871929165352965)
                ·
                  refine ⟨226616128850986718503681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208619353871929165352965 226616128850986718503681)
                  ·
                    rfl

theorem cell21_993000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_993000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993000 prefixEnd_993000 := by exact prefixLift 993000
  have htrace : WordTrace (prefixWord ++ tailWord_993000) baseStart_993000 baseEnd_993000 := by
    simpa [prefixWord, tailWord_993000, baseEnd_993000] using wordTrace_append hprefix tailTrace_993000
  have hstable : (prefixWord ++ tailWord_993000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993000).length < 2 ^ (prefixWord ++ tailWord_993000).sum := by decide
  have hdescent : baseEnd_993000 < baseStart_993000 := by decide
  rcases family_descends (prefixWord ++ tailWord_993000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993011 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 5]
def baseStart_993011 : Nat := 118140960795 + 993011 * 2 ^ 59
def prefixEnd_993011 : Nat := 4983230072969 + 3 ^ 40 * 993011 * 2
def baseEnd_993011 : Nat := 226618639200853143820325

theorem tailTrace_993011 : CollatzResearch.WordTrace tailWord_993011 prefixEnd_993011 226618639200853143820325 := by
  unfold tailWord_993011
  simp only [CollatzResearch.WordTrace]
  refine ⟨36218086605498214621938887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24145391070332143081292591 36218086605498214621938887)
  ·
    refine ⟨54327129908247321932908331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36218086605498214621938887 54327129908247321932908331)
    ·
      refine ⟨81490694862370982899362497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54327129908247321932908331 81490694862370982899362497)
      ·
        refine ⟨61118021146778237174521873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81490694862370982899362497 61118021146778237174521873)
        ·
          refine ⟨45838515860083677880891405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61118021146778237174521873 45838515860083677880891405)
          ·
            refine ⟨17189443447531379205334277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45838515860083677880891405 17189443447531379205334277)
            ·
              refine ⟨3223020646412133601000177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17189443447531379205334277 3223020646412133601000177)
              ·
                refine ⟨2417265484809100200750133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223020646412133601000177 2417265484809100200750133)
                ·
                  refine ⟨226618639200853143820325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2417265484809100200750133 226618639200853143820325)
                  ·
                    rfl

theorem cell21_993011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_993011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993011 prefixEnd_993011 := by exact prefixLift 993011
  have htrace : WordTrace (prefixWord ++ tailWord_993011) baseStart_993011 baseEnd_993011 := by
    simpa [prefixWord, tailWord_993011, baseEnd_993011] using wordTrace_append hprefix tailTrace_993011
  have hstable : (prefixWord ++ tailWord_993011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993011).length < 2 ^ (prefixWord ++ tailWord_993011).sum := by decide
  have hdescent : baseEnd_993011 < baseStart_993011 := by decide
  rcases family_descends (prefixWord ++ tailWord_993011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993014 : List Nat := [5, 1, 1, 1, 1, 3, 4, 5]
def baseStart_993014 : Nat := 118140960795 + 993014 * 2 ^ 59
def prefixEnd_993014 : Nat := 4983230072969 + 3 ^ 40 * 993014 * 2
def baseEnd_993014 : Nat := 75539774613908601756773

theorem tailTrace_993014 : CollatzResearch.WordTrace tailWord_993014 prefixEnd_993014 75539774613908601756773 := by
  unfold tailWord_993014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263637251530459133393631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24145464016324897422865397 2263637251530459133393631)
  ·
    refine ⟨3395455877295688700090447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263637251530459133393631 3395455877295688700090447)
    ·
      refine ⟨5093183815943533050135671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395455877295688700090447 5093183815943533050135671)
      ·
        refine ⟨7639775723915299575203507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093183815943533050135671 7639775723915299575203507)
        ·
          refine ⟨11459663585872949362805261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639775723915299575203507 11459663585872949362805261)
          ·
            refine ⟨4297373844702356011051973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11459663585872949362805261 4297373844702356011051973)
            ·
              refine ⟨805757595881691752072245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4297373844702356011051973 805757595881691752072245)
              ·
                refine ⟨75539774613908601756773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805757595881691752072245 75539774613908601756773)
                ·
                  rfl

theorem cell21_993014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_993014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993014 prefixEnd_993014 := by exact prefixLift 993014
  have htrace : WordTrace (prefixWord ++ tailWord_993014) baseStart_993014 baseEnd_993014 := by
    simpa [prefixWord, tailWord_993014, baseEnd_993014] using wordTrace_append hprefix tailTrace_993014
  have hstable : (prefixWord ++ tailWord_993014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993014).length < 2 ^ (prefixWord ++ tailWord_993014).sum := by decide
  have hdescent : baseEnd_993014 < baseStart_993014 := by decide
  rcases family_descends (prefixWord ++ tailWord_993014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993037 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 5]
def baseStart_993037 : Nat := 118140960795 + 993037 * 2 ^ 59
def prefixEnd_993037 : Nat := 4983230072969 + 3 ^ 40 * 993037 * 2
def baseEnd_993037 : Nat := 226624572755082876386939

theorem tailTrace_993037 : CollatzResearch.WordTrace tailWord_993037 prefixEnd_993037 226624572755082876386939 := by
  unfold tailWord_993037
  simp only [CollatzResearch.WordTrace]
  refine ⟨36219034903404021062385365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24146023268936014041590243 36219034903404021062385365)
  ·
    refine ⟨848883630548531743649657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36219034903404021062385365 848883630548531743649657)
    ·
      refine ⟨636662722911398807737243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 848883630548531743649657 636662722911398807737243)
      ·
        refine ⟨954994084367098211605865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636662722911398807737243 954994084367098211605865)
        ·
          refine ⟨716245563275323658704399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954994084367098211605865 716245563275323658704399)
          ·
            refine ⟨1074368344912985488056599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716245563275323658704399 1074368344912985488056599)
            ·
              refine ⟨1611552517369478232084899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074368344912985488056599 1611552517369478232084899)
              ·
                refine ⟨2417328776054217348127349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611552517369478232084899 2417328776054217348127349)
                ·
                  refine ⟨226624572755082876386939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2417328776054217348127349 226624572755082876386939)
                  ·
                    rfl

theorem cell21_993037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_993037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993037 prefixEnd_993037 := by exact prefixLift 993037
  have htrace : WordTrace (prefixWord ++ tailWord_993037) baseStart_993037 baseEnd_993037 := by
    simpa [prefixWord, tailWord_993037, baseEnd_993037] using wordTrace_append hprefix tailTrace_993037
  have hstable : (prefixWord ++ tailWord_993037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993037).length < 2 ^ (prefixWord ++ tailWord_993037).sum := by decide
  have hdescent : baseEnd_993037 < baseStart_993037 := by decide
  rcases family_descends (prefixWord ++ tailWord_993037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993059 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 4]
def baseStart_993059 : Nat := 118140960795 + 993059 * 2 ^ 59
def prefixEnd_993059 : Nat := 4983230072969 + 3 ^ 40 * 993059 * 2
def baseEnd_993059 : Nat := 226629593454815727020227

theorem tailTrace_993059 : CollatzResearch.WordTrace tailWord_993059 prefixEnd_993059 226629593454815727020227 := by
  unfold tailWord_993059
  simp only [CollatzResearch.WordTrace]
  refine ⟨36219837309324318819686231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24146558206216212546457487 36219837309324318819686231)
  ·
    refine ⟨54329755963986478229529347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36219837309324318819686231 54329755963986478229529347)
    ·
      refine ⟨81494633945979717344294021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54329755963986478229529347 81494633945979717344294021)
      ·
        refine ⟨15280243864871197002055129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81494633945979717344294021 15280243864871197002055129)
        ·
          refine ⟨11460182898653397751541347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15280243864871197002055129 11460182898653397751541347)
          ·
            refine ⟨17190274347980096627312021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460182898653397751541347 17190274347980096627312021)
            ·
              refine ⟨805794110061567029405251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17190274347980096627312021 805794110061567029405251)
              ·
                refine ⟨1208691165092350544107877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805794110061567029405251 1208691165092350544107877)
                ·
                  refine ⟨226629593454815727020227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208691165092350544107877 226629593454815727020227)
                  ·
                    rfl

theorem cell21_993059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 4].length) (baseStart_993059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993059 prefixEnd_993059 := by exact prefixLift 993059
  have htrace : WordTrace (prefixWord ++ tailWord_993059) baseStart_993059 baseEnd_993059 := by
    simpa [prefixWord, tailWord_993059, baseEnd_993059] using wordTrace_append hprefix tailTrace_993059
  have hstable : (prefixWord ++ tailWord_993059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993059).length < 2 ^ (prefixWord ++ tailWord_993059).sum := by decide
  have hdescent : baseEnd_993059 < baseStart_993059 := by decide
  rcases family_descends (prefixWord ++ tailWord_993059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993180 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_993180 : Nat := 118140960795 + 993180 * 2 ^ 59
def prefixEnd_993180 : Nat := 4983230072969 + 3 ^ 40 * 993180 * 2
def baseEnd_993180 : Nat := 226657207303346405503313

theorem tailTrace_993180 : CollatzResearch.WordTrace tailWord_993180 prefixEnd_993180 226657207303346405503313 := by
  unfold tailWord_993180
  simp only [CollatzResearch.WordTrace]
  refine ⟨18112125270942978242420497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24149500361257304323227329 18112125270942978242420497)
  ·
    refine ⟨13584093953207233681815373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18112125270942978242420497 13584093953207233681815373)
    ·
      refine ⟨5094035232452712630680765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13584093953207233681815373 5094035232452712630680765)
      ·
        refine ⟨1910263212169767236505287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5094035232452712630680765 1910263212169767236505287)
        ·
          refine ⟨2865394818254650854757931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910263212169767236505287 2865394818254650854757931)
          ·
            refine ⟨4298092227381976282136897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865394818254650854757931 4298092227381976282136897)
            ·
              refine ⟨3223569170536482211602673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298092227381976282136897 3223569170536482211602673)
              ·
                refine ⟨2417676877902361658702005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223569170536482211602673 2417676877902361658702005)
                ·
                  refine ⟨226657207303346405503313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2417676877902361658702005 226657207303346405503313)
                  ·
                    rfl

theorem cell21_993180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_993180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993180 prefixEnd_993180 := by exact prefixLift 993180
  have htrace : WordTrace (prefixWord ++ tailWord_993180) baseStart_993180 baseEnd_993180 := by
    simpa [prefixWord, tailWord_993180, baseEnd_993180] using wordTrace_append hprefix tailTrace_993180
  have hstable : (prefixWord ++ tailWord_993180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993180).length < 2 ^ (prefixWord ++ tailWord_993180).sum := by decide
  have hdescent : baseEnd_993180 < baseStart_993180 := by decide
  rcases family_descends (prefixWord ++ tailWord_993180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993183 : List Nat := [1, 1, 2, 5, 4, 1, 2, 5]
def baseStart_993183 : Nat := 118140960795 + 993183 * 2 ^ 59
def prefixEnd_993183 : Nat := 4983230072969 + 3 ^ 40 * 993183 * 2
def baseEnd_993183 : Nat := 75552630648073022317769

theorem tailTrace_993183 : CollatzResearch.WordTrace tailWord_993183 prefixEnd_993183 75552630648073022317769 := by
  unfold tailWord_993183
  simp only [CollatzResearch.WordTrace]
  refine ⟨36224359960875087997200203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24149573307250058664800135 36224359960875087997200203)
  ·
    refine ⟨54336539941312631995800305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36224359960875087997200203 54336539941312631995800305)
    ·
      refine ⟨40752404955984473996850229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54336539941312631995800305 40752404955984473996850229)
      ·
        refine ⟨3820537964623544437204709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40752404955984473996850229 3820537964623544437204709)
        ·
          refine ⟨716350868366914581975883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3820537964623544437204709 716350868366914581975883)
          ·
            refine ⟨1074526302550371872963825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716350868366914581975883 1074526302550371872963825)
            ·
              refine ⟨805894726912778904722869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074526302550371872963825 805894726912778904722869)
              ·
                refine ⟨75552630648073022317769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805894726912778904722869 75552630648073022317769)
                ·
                  rfl

theorem cell21_993183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 5].length) (baseStart_993183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993183 prefixEnd_993183 := by exact prefixLift 993183
  have htrace : WordTrace (prefixWord ++ tailWord_993183) baseStart_993183 baseEnd_993183 := by
    simpa [prefixWord, tailWord_993183, baseEnd_993183] using wordTrace_append hprefix tailTrace_993183
  have hstable : (prefixWord ++ tailWord_993183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993183).length < 2 ^ (prefixWord ++ tailWord_993183).sum := by decide
  have hdescent : baseEnd_993183 < baseStart_993183 := by decide
  rcases family_descends (prefixWord ++ tailWord_993183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993214 : List Nat := [4, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_993214 : Nat := 118140960795 + 993214 * 2 ^ 59
def prefixEnd_993214 : Nat := 4983230072969 + 3 ^ 40 * 993214 * 2
def baseEnd_993214 : Nat := 226664966566569901936577

theorem tailTrace_993214 : CollatzResearch.WordTrace tailWord_993214 prefixEnd_993214 226664966566569901936577 := by
  unfold tailWord_993214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528186327970347536447337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24150327082508520194385797 4528186327970347536447337)
  ·
    refine ⟨3396139745977760652335503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4528186327970347536447337 3396139745977760652335503)
    ·
      refine ⟨5094209618966640978503255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396139745977760652335503 5094209618966640978503255)
      ·
        refine ⟨7641314428449961467754883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5094209618966640978503255 7641314428449961467754883)
        ·
          refine ⟨11461971642674942201632325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7641314428449961467754883 11461971642674942201632325)
          ·
            refine ⟨2149119683001551662806061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11461971642674942201632325 2149119683001551662806061)
            ·
              refine ⟨805919881125581873552273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149119683001551662806061 805919881125581873552273)
              ·
                refine ⟨604439910844186405164205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805919881125581873552273 604439910844186405164205)
                ·
                  refine ⟨226664966566569901936577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604439910844186405164205 226664966566569901936577)
                  ·
                    rfl

theorem cell21_993214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_993214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993214 prefixEnd_993214 := by exact prefixLift 993214
  have htrace : WordTrace (prefixWord ++ tailWord_993214) baseStart_993214 baseEnd_993214 := by
    simpa [prefixWord, tailWord_993214, baseEnd_993214] using wordTrace_append hprefix tailTrace_993214
  have hstable : (prefixWord ++ tailWord_993214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993214).length < 2 ^ (prefixWord ++ tailWord_993214).sum := by decide
  have hdescent : baseEnd_993214 < baseStart_993214 := by decide
  rcases family_descends (prefixWord ++ tailWord_993214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993228 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_993228 : Nat := 118140960795 + 993228 * 2 ^ 59
def prefixEnd_993228 : Nat := 4983230072969 + 3 ^ 40 * 993228 * 2
def baseEnd_993228 : Nat := 226668161557308988703215

theorem tailTrace_993228 : CollatzResearch.WordTrace tailWord_993228 prefixEnd_993228 226668161557308988703215 := by
  unfold tailWord_993228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18113000622856030341294169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24150667497141373788392225 18113000622856030341294169)
  ·
    refine ⟨13584750467142022755970627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18113000622856030341294169 13584750467142022755970627)
    ·
      refine ⟨20377125700713034133955941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13584750467142022755970627 20377125700713034133955941)
      ·
        refine ⟨3820711068883693900116739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20377125700713034133955941 3820711068883693900116739)
        ·
          refine ⟨5731066603325540850175109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820711068883693900116739 5731066603325540850175109)
          ·
            refine ⟨1074574988123538909407833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5731066603325540850175109 1074574988123538909407833)
            ·
              refine ⟨805931241092654182055875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074574988123538909407833 805931241092654182055875)
              ·
                refine ⟨1208896861638981273083813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805931241092654182055875 1208896861638981273083813)
                ·
                  refine ⟨226668161557308988703215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208896861638981273083813 226668161557308988703215)
                  ·
                    rfl

theorem cell21_993228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_993228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993228 prefixEnd_993228 := by exact prefixLift 993228
  have htrace : WordTrace (prefixWord ++ tailWord_993228) baseStart_993228 baseEnd_993228 := by
    simpa [prefixWord, tailWord_993228, baseEnd_993228] using wordTrace_append hprefix tailTrace_993228
  have hstable : (prefixWord ++ tailWord_993228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993228).length < 2 ^ (prefixWord ++ tailWord_993228).sum := by decide
  have hdescent : baseEnd_993228 < baseStart_993228 := by decide
  rcases family_descends (prefixWord ++ tailWord_993228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993256 : List Nat := [2, 1, 4, 1, 1, 1, 1, 7, 3]
def baseStart_993256 : Nat := 118140960795 + 993256 * 2 ^ 59
def prefixEnd_993256 : Nat := 4983230072969 + 3 ^ 40 * 993256 * 2
def baseEnd_993256 : Nat := 226674551538787162236491

theorem tailTrace_993256 : CollatzResearch.WordTrace tailWord_993256 prefixEnd_993256 226674551538787162236491 := by
  unfold tailWord_993256
  simp only [CollatzResearch.WordTrace]
  refine ⟨18113511244805310732303811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24151348326407080976405081 18113511244805310732303811)
  ·
    refine ⟨27170266867207966098455717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18113511244805310732303811 27170266867207966098455717)
    ·
      refine ⟨5094425037601493643460447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27170266867207966098455717 5094425037601493643460447)
      ·
        refine ⟨7641637556402240465190671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5094425037601493643460447 7641637556402240465190671)
        ·
          refine ⟨11462456334603360697786007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7641637556402240465190671 11462456334603360697786007)
          ·
            refine ⟨17193684501905041046679011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11462456334603360697786007 17193684501905041046679011)
            ·
              refine ⟨25790526752857561570018517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17193684501905041046679011 25790526752857561570018517)
              ·
                refine ⟨604465470770099099297309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25790526752857561570018517 604465470770099099297309)
                ·
                  refine ⟨226674551538787162236491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604465470770099099297309 226674551538787162236491)
                  ·
                    rfl

theorem cell21_993256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_993256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993256 prefixEnd_993256 := by exact prefixLift 993256
  have htrace : WordTrace (prefixWord ++ tailWord_993256) baseStart_993256 baseEnd_993256 := by
    simpa [prefixWord, tailWord_993256, baseEnd_993256] using wordTrace_append hprefix tailTrace_993256
  have hstable : (prefixWord ++ tailWord_993256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993256).length < 2 ^ (prefixWord ++ tailWord_993256).sum := by decide
  have hdescent : baseEnd_993256 < baseStart_993256 := by decide
  rcases family_descends (prefixWord ++ tailWord_993256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993273 : List Nat := [1, 2, 1, 3, 1, 4, 4, 2, 3]
def baseStart_993273 : Nat := 118140960795 + 993273 * 2 ^ 59
def prefixEnd_993273 : Nat := 4983230072969 + 3 ^ 40 * 993273 * 2
def baseEnd_993273 : Nat := 226678431170398910453123

theorem tailTrace_993273 : CollatzResearch.WordTrace tailWord_993273 prefixEnd_993273 226678431170398910453123 := by
  unfold tailWord_993273
  simp only [CollatzResearch.WordTrace]
  refine ⟨36227642530549033367976473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24151761687032688911984315 36227642530549033367976473)
  ·
    refine ⟨27170731897911775025982355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36227642530549033367976473 27170731897911775025982355)
    ·
      refine ⟨40756097846867662538973533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27170731897911775025982355 40756097846867662538973533)
      ·
        refine ⟨15283536692575373452115075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40756097846867662538973533 15283536692575373452115075)
        ·
          refine ⟨22925305038863060178172613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15283536692575373452115075 22925305038863060178172613)
          ·
            refine ⟨4298494694786823783407365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22925305038863060178172613 4298494694786823783407365)
            ·
              refine ⟨805967755272529459388881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4298494694786823783407365 805967755272529459388881)
              ·
                refine ⟨604475816454397094541661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805967755272529459388881 604475816454397094541661)
                ·
                  refine ⟨226678431170398910453123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604475816454397094541661 226678431170398910453123)
                  ·
                    rfl

theorem cell21_993273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_993273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993273 prefixEnd_993273 := by exact prefixLift 993273
  have htrace : WordTrace (prefixWord ++ tailWord_993273) baseStart_993273 baseEnd_993273 := by
    simpa [prefixWord, tailWord_993273, baseEnd_993273] using wordTrace_append hprefix tailTrace_993273
  have hstable : (prefixWord ++ tailWord_993273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993273).length < 2 ^ (prefixWord ++ tailWord_993273).sum := by decide
  have hdescent : baseEnd_993273 < baseStart_993273 := by decide
  rcases family_descends (prefixWord ++ tailWord_993273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993391 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 5]
def baseStart_993391 : Nat := 118140960795 + 993391 * 2 ^ 59
def prefixEnd_993391 : Nat := 4983230072969 + 3 ^ 40 * 993391 * 2
def baseEnd_993391 : Nat := 226705360378056927486215

theorem tailTrace_993391 : CollatzResearch.WordTrace tailWord_993391 prefixEnd_993391 226705360378056927486215 := by
  unfold tailWord_993391
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231946344121539520772027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24154630896081026347181351 36231946344121539520772027)
  ·
    refine ⟨54347919516182309281158041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36231946344121539520772027 54347919516182309281158041)
    ·
      refine ⟨40760939637136731960868531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54347919516182309281158041 40760939637136731960868531)
      ·
        refine ⟨61141409455705097941302797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40760939637136731960868531 61141409455705097941302797)
        ·
          refine ⟨22928028545889411727988549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61141409455705097941302797 22928028545889411727988549)
          ·
            refine ⟨4299005352354264698997853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22928028545889411727988549 4299005352354264698997853)
            ·
              refine ⟨1612127007132849262124195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4299005352354264698997853 1612127007132849262124195)
              ·
                refine ⟨2418190510699273893186293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612127007132849262124195 2418190510699273893186293)
                ·
                  refine ⟨226705360378056927486215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2418190510699273893186293 226705360378056927486215)
                  ·
                    rfl

theorem cell21_993391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_993391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993391 prefixEnd_993391 := by exact prefixLift 993391
  have htrace : WordTrace (prefixWord ++ tailWord_993391) baseStart_993391 baseEnd_993391 := by
    simpa [prefixWord, tailWord_993391, baseEnd_993391] using wordTrace_append hprefix tailTrace_993391
  have hstable : (prefixWord ++ tailWord_993391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993391).length < 2 ^ (prefixWord ++ tailWord_993391).sum := by decide
  have hdescent : baseEnd_993391 < baseStart_993391 := by decide
  rcases family_descends (prefixWord ++ tailWord_993391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993439 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 4]
def baseStart_993439 : Nat := 118140960795 + 993439 * 2 ^ 59
def prefixEnd_993439 : Nat := 4983230072969 + 3 ^ 40 * 993439 * 2
def baseEnd_993439 : Nat := 226716314632019510686117

theorem tailTrace_993439 : CollatzResearch.WordTrace tailWord_993439 prefixEnd_993439 226716314632019510686117 := by
  unfold tailWord_993439
  simp only [CollatzResearch.WordTrace]
  refine ⟨36233697047947643718519371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24155798031965095812346247 36233697047947643718519371)
  ·
    refine ⟨54350545571921465577779057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36233697047947643718519371 54350545571921465577779057)
    ·
      refine ⟨40762909178941099183334293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54350545571921465577779057 40762909178941099183334293)
      ·
        refine ⟨1910761367762864024218795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40762909178941099183334293 1910761367762864024218795)
        ·
          refine ⟨2866142051644296036328193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910761367762864024218795 2866142051644296036328193)
          ·
            refine ⟨2149606538733222027246145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866142051644296036328193 2149606538733222027246145)
            ·
              refine ⟨1612204904049916520434609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2149606538733222027246145 1612204904049916520434609)
              ·
                refine ⟨1209153678037437390325957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612204904049916520434609 1209153678037437390325957)
                ·
                  refine ⟨226716314632019510686117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209153678037437390325957 226716314632019510686117)
                  ·
                    rfl

theorem cell21_993439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_993439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993439 prefixEnd_993439 := by exact prefixLift 993439
  have htrace : WordTrace (prefixWord ++ tailWord_993439) baseStart_993439 baseEnd_993439 := by
    simpa [prefixWord, tailWord_993439, baseEnd_993439] using wordTrace_append hprefix tailTrace_993439
  have hstable : (prefixWord ++ tailWord_993439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993439).length < 2 ^ (prefixWord ++ tailWord_993439).sum := by decide
  have hdescent : baseEnd_993439 < baseStart_993439 := by decide
  rcases family_descends (prefixWord ++ tailWord_993439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993442 : List Nat := [3, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_993442 : Nat := 118140960795 + 993442 * 2 ^ 59
def prefixEnd_993442 : Nat := 4983230072969 + 3 ^ 40 * 993442 * 2
def baseEnd_993442 : Nat := 226716999272892172136111

theorem tailTrace_993442 : CollatzResearch.WordTrace tailWord_993442 prefixEnd_993442 226716999272892172136111 := by
  unfold tailWord_993442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058451616734193807719645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24155870977957850153919053 9058451616734193807719645)
  ·
    refine ⟨3396919356275322677894867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9058451616734193807719645 3396919356275322677894867)
    ·
      refine ⟨5095379034412984016842301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396919356275322677894867 5095379034412984016842301)
      ·
        refine ⟨1910767137904869006315863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5095379034412984016842301 1910767137904869006315863)
        ·
          refine ⟨2866150706857303509473795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910767137904869006315863 2866150706857303509473795)
          ·
            refine ⟨4299226060285955264210693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866150706857303509473795 4299226060285955264210693)
            ·
              refine ⟨806104886303616612039505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4299226060285955264210693 806104886303616612039505)
              ·
                refine ⟨604578664727712459029629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806104886303616612039505 604578664727712459029629)
                ·
                  refine ⟨226716999272892172136111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604578664727712459029629 226716999272892172136111)
                  ·
                    rfl

theorem cell21_993442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_993442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993442 prefixEnd_993442 := by exact prefixLift 993442
  have htrace : WordTrace (prefixWord ++ tailWord_993442) baseStart_993442 baseEnd_993442 := by
    simpa [prefixWord, tailWord_993442, baseEnd_993442] using wordTrace_append hprefix tailTrace_993442
  have hstable : (prefixWord ++ tailWord_993442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993442).length < 2 ^ (prefixWord ++ tailWord_993442).sum := by decide
  have hdescent : baseEnd_993442 < baseStart_993442 := by decide
  rcases family_descends (prefixWord ++ tailWord_993442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993453 : List Nat := [1, 5, 2, 1, 2, 1, 3, 6]
def baseStart_993453 : Nat := 118140960795 + 993453 * 2 ^ 59
def prefixEnd_993453 : Nat := 4983230072969 + 3 ^ 40 * 993453 * 2
def baseEnd_993453 : Nat := 75573169874252865817585

theorem tailTrace_993453 : CollatzResearch.WordTrace tailWord_993453 prefixEnd_993453 75573169874252865817585 := by
  unfold tailWord_993453
  simp only [CollatzResearch.WordTrace]
  refine ⟨36234207669896924109529013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24156138446597949406352675 36234207669896924109529013)
  ·
    refine ⟨3396956969052836635268345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36234207669896924109529013 3396956969052836635268345)
    ·
      refine ⟨2547717726789627476451259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3396956969052836635268345 2547717726789627476451259)
      ·
        refine ⟨3821576590184441214676889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547717726789627476451259 3821576590184441214676889)
        ·
          refine ⟨2866182442638330911007667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3821576590184441214676889 2866182442638330911007667)
          ·
            refine ⟨4299273663957496366511501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866182442638330911007667 4299273663957496366511501)
            ·
              refine ⟨1612227623984061137441813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4299273663957496366511501 1612227623984061137441813)
              ·
                refine ⟨75573169874252865817585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1612227623984061137441813 75573169874252865817585)
                ·
                  rfl

theorem cell21_993453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 6].length) (baseStart_993453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993453 prefixEnd_993453 := by exact prefixLift 993453
  have htrace : WordTrace (prefixWord ++ tailWord_993453) baseStart_993453 baseEnd_993453 := by
    simpa [prefixWord, tailWord_993453, baseEnd_993453] using wordTrace_append hprefix tailTrace_993453
  have hstable : (prefixWord ++ tailWord_993453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993453).length < 2 ^ (prefixWord ++ tailWord_993453).sum := by decide
  have hdescent : baseEnd_993453 < baseStart_993453 := by decide
  rcases family_descends (prefixWord ++ tailWord_993453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993470 : List Nat := [4, 2, 1, 1, 4, 1, 3, 5]
def baseStart_993470 : Nat := 118140960795 + 993470 * 2 ^ 59
def prefixEnd_993470 : Nat := 4983230072969 + 3 ^ 40 * 993470 * 2
def baseEnd_993470 : Nat := 75574463084790115223129

theorem tailTrace_993470 : CollatzResearch.WordTrace tailWord_993470 prefixEnd_993470 75574463084790115223129 := by
  unfold tailWord_993470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529353463854417001612233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24156551807223557341931909 4529353463854417001612233)
  ·
    refine ⟨3397015097890812751209175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4529353463854417001612233 3397015097890812751209175)
    ·
      refine ⟨5095522646836219126813763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3397015097890812751209175 5095522646836219126813763)
      ·
        refine ⟨7643283970254328690220645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5095522646836219126813763 7643283970254328690220645)
        ·
          refine ⟨1433115744422686629416371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7643283970254328690220645 1433115744422686629416371)
          ·
            refine ⟨2149673616634029944124557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433115744422686629416371 2149673616634029944124557)
            ·
              refine ⟨806127606237761229046709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149673616634029944124557 806127606237761229046709)
              ·
                refine ⟨75574463084790115223129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806127606237761229046709 75574463084790115223129)
                ·
                  rfl

theorem cell21_993470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_993470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993470 prefixEnd_993470 := by exact prefixLift 993470
  have htrace : WordTrace (prefixWord ++ tailWord_993470) baseStart_993470 baseEnd_993470 := by
    simpa [prefixWord, tailWord_993470, baseEnd_993470] using wordTrace_append hprefix tailTrace_993470
  have hstable : (prefixWord ++ tailWord_993470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993470).length < 2 ^ (prefixWord ++ tailWord_993470).sum := by decide
  have hdescent : baseEnd_993470 < baseStart_993470 := by decide
  rcases family_descends (prefixWord ++ tailWord_993470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993498 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_993498 : Nat := 118140960795 + 993498 * 2 ^ 59
def prefixEnd_993498 : Nat := 4983230072969 + 3 ^ 40 * 993498 * 2
def baseEnd_993498 : Nat := 226729779235848519202663

theorem tailTrace_993498 : CollatzResearch.WordTrace tailWord_993498 prefixEnd_993498 226729779235848519202663 := by
  unfold tailWord_993498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058962238683474198729287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24157232636489264529944765 9058962238683474198729287)
  ·
    refine ⟨13588443358025211298093931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9058962238683474198729287 13588443358025211298093931)
    ·
      refine ⟨20382665037037816947140897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13588443358025211298093931 20382665037037816947140897)
      ·
        refine ⟨15286998777778362710355673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20382665037037816947140897 15286998777778362710355673)
        ·
          refine ⟨11465249083333772032766755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15286998777778362710355673 11465249083333772032766755)
          ·
            refine ⟨17197873625000658049150133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11465249083333772032766755 17197873625000658049150133)
            ·
              refine ⟨1612300652343811692107825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17197873625000658049150133 1612300652343811692107825)
              ·
                refine ⟨1209225489257858769080869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612300652343811692107825 1209225489257858769080869)
                ·
                  refine ⟨226729779235848519202663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209225489257858769080869 226729779235848519202663)
                  ·
                    rfl

theorem cell21_993498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_993498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993498 prefixEnd_993498 := by exact prefixLift 993498
  have htrace : WordTrace (prefixWord ++ tailWord_993498) baseStart_993498 baseEnd_993498 := by
    simpa [prefixWord, tailWord_993498, baseEnd_993498] using wordTrace_append hprefix tailTrace_993498
  have hstable : (prefixWord ++ tailWord_993498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993498).length < 2 ^ (prefixWord ++ tailWord_993498).sum := by decide
  have hdescent : baseEnd_993498 < baseStart_993498 := by decide
  rcases family_descends (prefixWord ++ tailWord_993498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993501 : List Nat := [1, 4, 3, 2, 1, 1, 2, 4, 3]
def baseStart_993501 : Nat := 118140960795 + 993501 * 2 ^ 59
def prefixEnd_993501 : Nat := 4983230072969 + 3 ^ 40 * 993501 * 2
def baseEnd_993501 : Nat := 226730463876721180652657

theorem tailTrace_993501 : CollatzResearch.WordTrace tailWord_993501 prefixEnd_993501 226730463876721180652657 := by
  unfold tailWord_993501
  simp only [CollatzResearch.WordTrace]
  refine ⟨36235958373723028307276357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24157305582482018871517571 36235958373723028307276357)
  ·
    refine ⟨6794242195073067807614317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36235958373723028307276357 6794242195073067807614317)
    ·
      refine ⟨2547840823152400427855369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6794242195073067807614317 2547840823152400427855369)
      ·
        refine ⟨1910880617364300320891527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547840823152400427855369 1910880617364300320891527)
        ·
          refine ⟨2866320926046450481337291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910880617364300320891527 2866320926046450481337291)
          ·
            refine ⟨4299481389069675722005937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866320926046450481337291 4299481389069675722005937)
            ·
              refine ⟨3224611041802256791504453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4299481389069675722005937 3224611041802256791504453)
              ·
                refine ⟨604614570337923148407085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3224611041802256791504453 604614570337923148407085)
                ·
                  refine ⟨226730463876721180652657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604614570337923148407085 226730463876721180652657)
                  ·
                    rfl

theorem cell21_993501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_993501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993501 prefixEnd_993501 := by exact prefixLift 993501
  have htrace : WordTrace (prefixWord ++ tailWord_993501) baseStart_993501 baseEnd_993501 := by
    simpa [prefixWord, tailWord_993501, baseEnd_993501] using wordTrace_append hprefix tailTrace_993501
  have hstable : (prefixWord ++ tailWord_993501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993501).length < 2 ^ (prefixWord ++ tailWord_993501).sum := by decide
  have hdescent : baseEnd_993501 < baseStart_993501 := by decide
  rcases family_descends (prefixWord ++ tailWord_993501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993557 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 6]
def baseStart_993557 : Nat := 118140960795 + 993557 * 2 ^ 59
def prefixEnd_993557 : Nat := 4983230072969 + 3 ^ 40 * 993557 * 2
def baseEnd_993557 : Nat := 226743243839677527719209

theorem tailTrace_993557 : CollatzResearch.WordTrace tailWord_993557 prefixEnd_993557 226743243839677527719209 := by
  unfold tailWord_993557
  simp only [CollatzResearch.WordTrace]
  refine ⟨36238000861520149871314925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24158667241013433247543283 36238000861520149871314925)
  ·
    refine ⟨13589250323070056201743097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36238000861520149871314925 13589250323070056201743097)
    ·
      refine ⟨10191937742302542151307323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13589250323070056201743097 10191937742302542151307323)
      ·
        refine ⟨15287906613453813226960985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10191937742302542151307323 15287906613453813226960985)
        ·
          refine ⟨11465929960090359920220739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15287906613453813226960985 11465929960090359920220739)
          ·
            refine ⟨17198894940135539880331109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11465929960090359920220739 17198894940135539880331109)
            ·
              refine ⟨3224792801275413727562083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17198894940135539880331109 3224792801275413727562083)
              ·
                refine ⟨4837189201913120591343125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224792801275413727562083 4837189201913120591343125)
                ·
                  refine ⟨226743243839677527719209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4837189201913120591343125 226743243839677527719209)
                  ·
                    rfl

theorem cell21_993557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_993557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993557 prefixEnd_993557 := by exact prefixLift 993557
  have htrace : WordTrace (prefixWord ++ tailWord_993557) baseStart_993557 baseEnd_993557 := by
    simpa [prefixWord, tailWord_993557, baseEnd_993557] using wordTrace_append hprefix tailTrace_993557
  have hstable : (prefixWord ++ tailWord_993557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993557).length < 2 ^ (prefixWord ++ tailWord_993557).sum := by decide
  have hdescent : baseEnd_993557 < baseStart_993557 := by decide
  rcases family_descends (prefixWord ++ tailWord_993557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993653 : List Nat := [1, 3, 4, 1, 2, 2, 2, 3, 3]
def baseStart_993653 : Nat := 118140960795 + 993653 * 2 ^ 59
def prefixEnd_993653 : Nat := 4983230072969 + 3 ^ 40 * 993653 * 2
def baseEnd_993653 : Nat := 226765152347602694119013

theorem tailTrace_993653 : CollatzResearch.WordTrace tailWord_993653 prefixEnd_993653 226765152347602694119013 := by
  unfold tailWord_993653
  simp only [CollatzResearch.WordTrace]
  refine ⟨36241502269172358266809613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24161001512781572177873075 36241502269172358266809613)
  ·
    refine ⟨13590563350939634350053605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36241502269172358266809613 13590563350939634350053605)
    ·
      refine ⟨2548230628301181440635051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13590563350939634350053605 2548230628301181440635051)
      ·
        refine ⟨3822345942451772160952577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548230628301181440635051 3822345942451772160952577)
        ·
          refine ⟨2866759456838829120714433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3822345942451772160952577 2866759456838829120714433)
          ·
            refine ⟨2150069592629121840535825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866759456838829120714433 2150069592629121840535825)
            ·
              refine ⟨1612552194471841380401869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150069592629121840535825 1612552194471841380401869)
              ·
                refine ⟨604707072926940517650701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1612552194471841380401869 604707072926940517650701)
                ·
                  refine ⟨226765152347602694119013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604707072926940517650701 226765152347602694119013)
                  ·
                    rfl

theorem cell21_993653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_993653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993653 prefixEnd_993653 := by exact prefixLift 993653
  have htrace : WordTrace (prefixWord ++ tailWord_993653) baseStart_993653 baseEnd_993653 := by
    simpa [prefixWord, tailWord_993653, baseEnd_993653] using wordTrace_append hprefix tailTrace_993653
  have hstable : (prefixWord ++ tailWord_993653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993653).length < 2 ^ (prefixWord ++ tailWord_993653).sum := by decide
  have hdescent : baseEnd_993653 < baseStart_993653 := by decide
  rcases family_descends (prefixWord ++ tailWord_993653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993667 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 4]
def baseStart_993667 : Nat := 118140960795 + 993667 * 2 ^ 59
def prefixEnd_993667 : Nat := 4983230072969 + 3 ^ 40 * 993667 * 2
def baseEnd_993667 : Nat := 226768347338341780885651

theorem tailTrace_993667 : CollatzResearch.WordTrace tailWord_993667 prefixEnd_993667 226768347338341780885651 := by
  unfold tailWord_993667
  simp only [CollatzResearch.WordTrace]
  refine ⟨36242012891121638657819255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24161341927414425771879503 36242012891121638657819255)
  ·
    refine ⟨54363019336682457986728883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36242012891121638657819255 54363019336682457986728883)
    ·
      refine ⟨81544529005023686980093325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54363019336682457986728883 81544529005023686980093325)
      ·
        refine ⟨30579198376883882617534997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81544529005023686980093325 30579198376883882617534997)
        ·
          refine ⟨1433399923916431997696953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30579198376883882617534997 1433399923916431997696953)
          ·
            refine ⟨1075049942937323998272715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1433399923916431997696953 1075049942937323998272715)
            ·
              refine ⟨1612574914405985997409073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075049942937323998272715 1612574914405985997409073)
              ·
                refine ⟨1209431185804489498056805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1612574914405985997409073 1209431185804489498056805)
                ·
                  refine ⟨226768347338341780885651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209431185804489498056805 226768347338341780885651)
                  ·
                    rfl

theorem cell21_993667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4].length) (baseStart_993667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993667 prefixEnd_993667 := by exact prefixLift 993667
  have htrace : WordTrace (prefixWord ++ tailWord_993667) baseStart_993667 baseEnd_993667 := by
    simpa [prefixWord, tailWord_993667, baseEnd_993667] using wordTrace_append hprefix tailTrace_993667
  have hstable : (prefixWord ++ tailWord_993667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993667).length < 2 ^ (prefixWord ++ tailWord_993667).sum := by decide
  have hdescent : baseEnd_993667 < baseStart_993667 := by decide
  rcases family_descends (prefixWord ++ tailWord_993667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993684 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_993684 : Nat := 118140960795 + 993684 * 2 ^ 59
def prefixEnd_993684 : Nat := 4983230072969 + 3 ^ 40 * 993684 * 2
def baseEnd_993684 : Nat := 226772226969953529102283

theorem tailTrace_993684 : CollatzResearch.WordTrace tailWord_993684 prefixEnd_993684 226772226969953529102283 := by
  unfold tailWord_993684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18121316466030025280594053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24161755288040033707458737 18121316466030025280594053)
  ·
    refine ⟨3397746837380629740111385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18121316466030025280594053 3397746837380629740111385)
    ·
      refine ⟨2548310128035472305083539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3397746837380629740111385 2548310128035472305083539)
      ·
        refine ⟨3822465192053208457625309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548310128035472305083539 3822465192053208457625309)
        ·
          refine ⟨1433424447019953171609491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3822465192053208457625309 1433424447019953171609491)
          ·
            refine ⟨2150136670529929757414237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433424447019953171609491 2150136670529929757414237)
            ·
              refine ⟨806301251448723659030339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2150136670529929757414237 806301251448723659030339)
              ·
                refine ⟨1209451877173085488545509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806301251448723659030339 1209451877173085488545509)
                ·
                  refine ⟨226772226969953529102283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209451877173085488545509 226772226969953529102283)
                  ·
                    rfl

theorem cell21_993684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_993684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993684 prefixEnd_993684 := by exact prefixLift 993684
  have htrace : WordTrace (prefixWord ++ tailWord_993684) baseStart_993684 baseEnd_993684 := by
    simpa [prefixWord, tailWord_993684, baseEnd_993684] using wordTrace_append hprefix tailTrace_993684
  have hstable : (prefixWord ++ tailWord_993684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993684).length < 2 ^ (prefixWord ++ tailWord_993684).sum := by decide
  have hdescent : baseEnd_993684 < baseStart_993684 := by decide
  rcases family_descends (prefixWord ++ tailWord_993684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993754 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_993754 : Nat := 118140960795 + 993754 * 2 ^ 59
def prefixEnd_993754 : Nat := 4983230072969 + 3 ^ 40 * 993754 * 2
def baseEnd_993754 : Nat := 226788201923648962935473

theorem tailTrace_993754 : CollatzResearch.WordTrace tailWord_993754 prefixEnd_993754 226788201923648962935473 := by
  unfold tailWord_993754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9061296510451613129059079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24163457361204301677490877 9061296510451613129059079)
  ·
    refine ⟨13591944765677419693588619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9061296510451613129059079 13591944765677419693588619)
    ·
      refine ⟨20387917148516129540382929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13591944765677419693588619 20387917148516129540382929)
      ·
        refine ⟨15290937861387097155287197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20387917148516129540382929 15290937861387097155287197)
        ·
          refine ⟨5734101698020161433232699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15290937861387097155287197 5734101698020161433232699)
          ·
            refine ⟨8601152547030242149849049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734101698020161433232699 8601152547030242149849049)
            ·
              refine ⟨6450864410272681612386787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8601152547030242149849049 6450864410272681612386787)
              ·
                refine ⟨9676296615409022418580181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450864410272681612386787 9676296615409022418580181)
                ·
                  refine ⟨226788201923648962935473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9676296615409022418580181 226788201923648962935473)
                  ·
                    rfl

theorem cell21_993754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_993754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993754 prefixEnd_993754 := by exact prefixLift 993754
  have htrace : WordTrace (prefixWord ++ tailWord_993754) baseStart_993754 baseEnd_993754 := by
    simpa [prefixWord, tailWord_993754, baseEnd_993754] using wordTrace_append hprefix tailTrace_993754
  have hstable : (prefixWord ++ tailWord_993754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993754).length < 2 ^ (prefixWord ++ tailWord_993754).sum := by decide
  have hdescent : baseEnd_993754 < baseStart_993754 := by decide
  rcases family_descends (prefixWord ++ tailWord_993754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993771 : List Nat := [1, 1, 1, 1, 2, 3, 4, 5, 3]
def baseStart_993771 : Nat := 118140960795 + 993771 * 2 ^ 59
def prefixEnd_993771 : Nat := 4983230072969 + 3 ^ 40 * 993771 * 2
def baseEnd_993771 : Nat := 226792081555260711152105

theorem tailTrace_993771 : CollatzResearch.WordTrace tailWord_993771 prefixEnd_993771 226792081555260711152105 := by
  unfold tailWord_993771
  simp only [CollatzResearch.WordTrace]
  refine ⟨36245806082744864419605167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24163870721829909613070111 36245806082744864419605167)
  ·
    refine ⟨54368709124117296629407751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36245806082744864419605167 54368709124117296629407751)
    ·
      refine ⟨81553063686175944944111627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54368709124117296629407751 81553063686175944944111627)
      ·
        refine ⟨122329595529263917416167441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81553063686175944944111627 122329595529263917416167441)
        ·
          refine ⟨91747196646947938062125581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122329595529263917416167441 91747196646947938062125581)
          ·
            refine ⟨34405198742605476773297093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91747196646947938062125581 34405198742605476773297093)
            ·
              refine ⟨6450974764238526894993205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34405198742605476773297093 6450974764238526894993205)
              ·
                refine ⟨604778884147361896405613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6450974764238526894993205 604778884147361896405613)
                ·
                  refine ⟨226792081555260711152105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604778884147361896405613 226792081555260711152105)
                  ·
                    rfl

theorem cell21_993771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 3].length) (baseStart_993771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993771 prefixEnd_993771 := by exact prefixLift 993771
  have htrace : WordTrace (prefixWord ++ tailWord_993771) baseStart_993771 baseEnd_993771 := by
    simpa [prefixWord, tailWord_993771, baseEnd_993771] using wordTrace_append hprefix tailTrace_993771
  have hstable : (prefixWord ++ tailWord_993771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993771).length < 2 ^ (prefixWord ++ tailWord_993771).sum := by decide
  have hdescent : baseEnd_993771 < baseStart_993771 := by decide
  rcases family_descends (prefixWord ++ tailWord_993771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993785 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 4]
def baseStart_993785 : Nat := 118140960795 + 993785 * 2 ^ 59
def prefixEnd_993785 : Nat := 4983230072969 + 3 ^ 40 * 993785 * 2
def baseEnd_993785 : Nat := 226795276545999797918743

theorem tailTrace_993785 : CollatzResearch.WordTrace tailWord_993785 prefixEnd_993785 226795276545999797918743 := by
  unfold tailWord_993785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36246316704694144810614809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24164211136462763207076539 36246316704694144810614809)
  ·
    refine ⟨27184737528520608607961107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36246316704694144810614809 27184737528520608607961107)
    ·
      refine ⟨40777106292780912911941661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27184737528520608607961107 40777106292780912911941661)
      ·
        refine ⟨15291414859792842341978123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40777106292780912911941661 15291414859792842341978123)
        ·
          refine ⟨22937122289689263512967185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15291414859792842341978123 22937122289689263512967185)
          ·
            refine ⟨17202841717266947634725389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22937122289689263512967185 17202841717266947634725389)
            ·
              refine ⟨6451065643975105363022021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17202841717266947634725389 6451065643975105363022021)
              ·
                refine ⟨1209574808245332255566629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6451065643975105363022021 1209574808245332255566629)
                ·
                  refine ⟨226795276545999797918743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209574808245332255566629 226795276545999797918743)
                  ·
                    rfl

theorem cell21_993785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_993785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993785 prefixEnd_993785 := by exact prefixLift 993785
  have htrace : WordTrace (prefixWord ++ tailWord_993785) baseStart_993785 baseEnd_993785 := by
    simpa [prefixWord, tailWord_993785, baseEnd_993785] using wordTrace_append hprefix tailTrace_993785
  have hstable : (prefixWord ++ tailWord_993785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993785).length < 2 ^ (prefixWord ++ tailWord_993785).sum := by decide
  have hdescent : baseEnd_993785 < baseStart_993785 := by decide
  rcases family_descends (prefixWord ++ tailWord_993785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993805 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 5]
def baseStart_993805 : Nat := 118140960795 + 993805 * 2 ^ 59
def prefixEnd_993805 : Nat := 4983230072969 + 3 ^ 40 * 993805 * 2
def baseEnd_993805 : Nat := 226799840818484207585369

theorem tailTrace_993805 : CollatzResearch.WordTrace tailWord_993805 prefixEnd_993805 226799840818484207585369 := by
  unfold tailWord_993805
  simp only [CollatzResearch.WordTrace]
  refine ⟨36247046164621688226342869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24164697443081125484228579 36247046164621688226342869)
  ·
    refine ⟨849540144483320817804911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36247046164621688226342869 849540144483320817804911)
    ·
      refine ⟨1274310216724981226707367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849540144483320817804911 1274310216724981226707367)
      ·
        refine ⟨1911465325087471840061051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274310216724981226707367 1911465325087471840061051)
        ·
          refine ⟨2867197987631207760091577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911465325087471840061051 2867197987631207760091577)
          ·
            refine ⟨2150398490723405820068683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2867197987631207760091577 2150398490723405820068683)
            ·
              refine ⟨3225597736085108730103025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150398490723405820068683 3225597736085108730103025)
              ·
                refine ⟨2419198302063831547577269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225597736085108730103025 2419198302063831547577269)
                ·
                  refine ⟨226799840818484207585369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2419198302063831547577269 226799840818484207585369)
                  ·
                    rfl

theorem cell21_993805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_993805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993805 prefixEnd_993805 := by exact prefixLift 993805
  have htrace : WordTrace (prefixWord ++ tailWord_993805) baseStart_993805 baseEnd_993805 := by
    simpa [prefixWord, tailWord_993805, baseEnd_993805] using wordTrace_append hprefix tailTrace_993805
  have hstable : (prefixWord ++ tailWord_993805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993805).length < 2 ^ (prefixWord ++ tailWord_993805).sum := by decide
  have hdescent : baseEnd_993805 < baseStart_993805 := by decide
  rcases family_descends (prefixWord ++ tailWord_993805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993847 : List Nat := [1, 1, 3, 1, 2, 3, 1, 6, 3]
def baseStart_993847 : Nat := 118140960795 + 993847 * 2 ^ 59
def prefixEnd_993847 : Nat := 4983230072969 + 3 ^ 40 * 993847 * 2
def baseEnd_993847 : Nat := 226809425790701467885283

theorem tailTrace_993847 : CollatzResearch.WordTrace tailWord_993847 prefixEnd_993847 226809425790701467885283 := by
  unfold tailWord_993847
  simp only [CollatzResearch.WordTrace]
  refine ⟨36248578030469529399371795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24165718686979686266247863 36248578030469529399371795)
  ·
    refine ⟨54372867045704294099057693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36248578030469529399371795 54372867045704294099057693)
    ·
      refine ⟨20389825142139110287146635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54372867045704294099057693 20389825142139110287146635)
      ·
        refine ⟨30584737713208665430719953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20389825142139110287146635 30584737713208665430719953)
        ·
          refine ⟨22938553284906499073039965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30584737713208665430719953 22938553284906499073039965)
          ·
            refine ⟨8601957481839937152389987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22938553284906499073039965 8601957481839937152389987)
            ·
              refine ⟨12902936222759905728584981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601957481839937152389987 12902936222759905728584981)
              ·
                refine ⟨604825135441870581027421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12902936222759905728584981 604825135441870581027421)
                ·
                  refine ⟨226809425790701467885283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604825135441870581027421 226809425790701467885283)
                  ·
                    rfl

theorem cell21_993847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 3].length) (baseStart_993847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993847 prefixEnd_993847 := by exact prefixLift 993847
  have htrace : WordTrace (prefixWord ++ tailWord_993847) baseStart_993847 baseEnd_993847 := by
    simpa [prefixWord, tailWord_993847, baseEnd_993847] using wordTrace_append hprefix tailTrace_993847
  have hstable : (prefixWord ++ tailWord_993847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993847).length < 2 ^ (prefixWord ++ tailWord_993847).sum := by decide
  have hdescent : baseEnd_993847 < baseStart_993847 := by decide
  rcases family_descends (prefixWord ++ tailWord_993847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993909 : List Nat := [1, 3, 4, 2, 2, 1, 2, 6]
def baseStart_993909 : Nat := 118140960795 + 993909 * 2 ^ 59
def prefixEnd_993909 : Nat := 4983230072969 + 3 ^ 40 * 993909 * 2
def baseEnd_993909 : Nat := 75607858345134379283941

theorem tailTrace_993909 : CollatzResearch.WordTrace tailWord_993909 prefixEnd_993909 75607858345134379283941 := by
  unfold tailWord_993909
  simp only [CollatzResearch.WordTrace]
  refine ⟨36250839356244913988128781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24167226237496609325419187 36250839356244913988128781)
  ·
    refine ⟨13594064758591842745548293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36250839356244913988128781 13594064758591842745548293)
    ·
      refine ⟨2548887142235970514790305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13594064758591842745548293 2548887142235970514790305)
      ·
        refine ⟨1911665356676977886092729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2548887142235970514790305 1911665356676977886092729)
        ·
          refine ⟨1433749017507733414569547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1911665356676977886092729 1433749017507733414569547)
          ·
            refine ⟨2150623526261600121854321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433749017507733414569547 2150623526261600121854321)
            ·
              refine ⟨1612967644696200091390741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150623526261600121854321 1612967644696200091390741)
              ·
                refine ⟨75607858345134379283941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1612967644696200091390741 75607858345134379283941)
                ·
                  rfl

theorem cell21_993909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 6].length) (baseStart_993909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_993909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_993909 prefixEnd_993909 := by exact prefixLift 993909
  have htrace : WordTrace (prefixWord ++ tailWord_993909) baseStart_993909 baseEnd_993909 := by
    simpa [prefixWord, tailWord_993909, baseEnd_993909] using wordTrace_append hprefix tailTrace_993909
  have hstable : (prefixWord ++ tailWord_993909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993909).length < 2 ^ (prefixWord ++ tailWord_993909).sum := by decide
  have hdescent : baseEnd_993909 < baseStart_993909 := by decide
  rcases family_descends (prefixWord ++ tailWord_993909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994036 : List Nat := [2, 6, 1, 1, 3, 1, 2, 5]
def baseStart_994036 : Nat := 118140960795 + 994036 * 2 ^ 59
def prefixEnd_994036 : Nat := 4983230072969 + 3 ^ 40 * 994036 * 2
def baseEnd_994036 : Nat := 75617519388559713078299

theorem tailTrace_994036 : CollatzResearch.WordTrace tailWord_994036 prefixEnd_994036 75617519388559713078299 := by
  unfold tailWord_994036
  simp only [CollatzResearch.WordTrace]
  refine ⟨18127735713392407339000981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24170314284523209785334641 18127735713392407339000981)
  ·
    refine ⟨849737611565269094015671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18127735713392407339000981 849737611565269094015671)
    ·
      refine ⟨1274606417347903641023507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849737611565269094015671 1274606417347903641023507)
      ·
        refine ⟨1911909626021855461535261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274606417347903641023507 1911909626021855461535261)
        ·
          refine ⟨716966109758195798075723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1911909626021855461535261 716966109758195798075723)
          ·
            refine ⟨1075449164637293697113585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716966109758195798075723 1075449164637293697113585)
            ·
              refine ⟨806586873477970272835189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075449164637293697113585 806586873477970272835189)
              ·
                refine ⟨75617519388559713078299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806586873477970272835189 75617519388559713078299)
                ·
                  rfl

theorem cell21_994036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_994036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994036 prefixEnd_994036 := by exact prefixLift 994036
  have htrace : WordTrace (prefixWord ++ tailWord_994036) baseStart_994036 baseEnd_994036 := by
    simpa [prefixWord, tailWord_994036, baseEnd_994036] using wordTrace_append hprefix tailTrace_994036
  have hstable : (prefixWord ++ tailWord_994036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994036).length < 2 ^ (prefixWord ++ tailWord_994036).sum := by decide
  have hdescent : baseEnd_994036 < baseStart_994036 := by decide
  rcases family_descends (prefixWord ++ tailWord_994036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994044 : List Nat := [2, 2, 2, 1, 3, 2, 4, 5]
def baseStart_994044 : Nat := 118140960795 + 994044 * 2 ^ 59
def prefixEnd_994044 : Nat := 4983230072969 + 3 ^ 40 * 994044 * 2
def baseEnd_994044 : Nat := 75618127958224301033849

theorem tailTrace_994044 : CollatzResearch.WordTrace tailWord_994044 prefixEnd_994044 75618127958224301033849 := by
  unfold tailWord_994044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18127881605377916022146593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24170508807170554696195457 18127881605377916022146593)
  ·
    refine ⟨13595911204033437016609945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18127881605377916022146593 13595911204033437016609945)
    ·
      refine ⟨10196933403025077762457459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13595911204033437016609945 10196933403025077762457459)
      ·
        refine ⟨15295400104537616643686189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10196933403025077762457459 15295400104537616643686189)
        ·
          refine ⟨5735775039201606241382321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15295400104537616643686189 5735775039201606241382321)
          ·
            refine ⟨4301831279401204681036741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5735775039201606241382321 4301831279401204681036741)
            ·
              refine ⟨806593364887725877694389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4301831279401204681036741 806593364887725877694389)
              ·
                refine ⟨75618127958224301033849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806593364887725877694389 75618127958224301033849)
                ·
                  rfl

theorem cell21_994044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_994044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994044 prefixEnd_994044 := by exact prefixLift 994044
  have htrace : WordTrace (prefixWord ++ tailWord_994044) baseStart_994044 baseEnd_994044 := by
    simpa [prefixWord, tailWord_994044, baseEnd_994044] using wordTrace_append hprefix tailTrace_994044
  have hstable : (prefixWord ++ tailWord_994044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994044).length < 2 ^ (prefixWord ++ tailWord_994044).sum := by decide
  have hdescent : baseEnd_994044 < baseStart_994044 := by decide
  rcases family_descends (prefixWord ++ tailWord_994044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994117 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 9]
def baseStart_994117 : Nat := 118140960795 + 994117 * 2 ^ 59
def prefixEnd_994117 : Nat := 4983230072969 + 3 ^ 40 * 994117 * 2
def baseEnd_994117 : Nat := 226871043469240998384731

theorem tailTrace_994117 : CollatzResearch.WordTrace tailWord_994117 prefixEnd_994117 226871043469240998384731 := by
  unfold tailWord_994117
  simp only [CollatzResearch.WordTrace]
  refine ⟨36258425739491365511700605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24172283826327577007800403 36258425739491365511700605)
  ·
    refine ⟨13596909652309262066887727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36258425739491365511700605 13596909652309262066887727)
    ·
      refine ⟨20395364478463893100331591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13596909652309262066887727 20395364478463893100331591)
      ·
        refine ⟨30593046717695839650497387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20395364478463893100331591 30593046717695839650497387)
        ·
          refine ⟨45889570076543759475746081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30593046717695839650497387 45889570076543759475746081)
          ·
            refine ⟨34417177557407819606809561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45889570076543759475746081 34417177557407819606809561)
            ·
              refine ⟨25812883168055864705107171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34417177557407819606809561 25812883168055864705107171)
              ·
                refine ⟨38719324752083797057660757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25812883168055864705107171 38719324752083797057660757)
                ·
                  refine ⟨226871043469240998384731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38719324752083797057660757 226871043469240998384731)
                  ·
                    rfl

theorem cell21_994117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_994117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994117 prefixEnd_994117 := by exact prefixLift 994117
  have htrace : WordTrace (prefixWord ++ tailWord_994117) baseStart_994117 baseEnd_994117 := by
    simpa [prefixWord, tailWord_994117, baseEnd_994117] using wordTrace_append hprefix tailTrace_994117
  have hstable : (prefixWord ++ tailWord_994117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994117).length < 2 ^ (prefixWord ++ tailWord_994117).sum := by decide
  have hdescent : baseEnd_994117 < baseStart_994117 := by decide
  rcases family_descends (prefixWord ++ tailWord_994117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994255 : List Nat := [1, 1, 2, 1, 1, 7, 2, 6]
def baseStart_994255 : Nat := 118140960795 + 994255 * 2 ^ 59
def prefixEnd_994255 : Nat := 4983230072969 + 3 ^ 40 * 994255 * 2
def baseEnd_994255 : Nat := 75634178983127808361483

theorem tailTrace_994255 : CollatzResearch.WordTrace tailWord_994255 prefixEnd_994255 75634178983127808361483 := by
  unfold tailWord_994255
  simp only [CollatzResearch.WordTrace]
  refine ⟨36263459012991415080224219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24175639341994276720149479 36263459012991415080224219)
  ·
    refine ⟨54395188519487122620336329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36263459012991415080224219 54395188519487122620336329)
    ·
      refine ⟨40796391389615341965252247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54395188519487122620336329 40796391389615341965252247)
      ·
        refine ⟨61194587084423012947878371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40796391389615341965252247 61194587084423012947878371)
        ·
          refine ⟨91791880626634519421817557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61194587084423012947878371 91791880626634519421817557)
          ·
            refine ⟨2151372202186746548948849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 91791880626634519421817557 2151372202186746548948849)
            ·
              refine ⟨1613529151640059911711637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151372202186746548948849 1613529151640059911711637)
              ·
                refine ⟨75634178983127808361483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1613529151640059911711637 75634178983127808361483)
                ·
                  rfl

theorem cell21_994255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 6].length) (baseStart_994255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994255 prefixEnd_994255 := by exact prefixLift 994255
  have htrace : WordTrace (prefixWord ++ tailWord_994255) baseStart_994255 baseEnd_994255 := by
    simpa [prefixWord, tailWord_994255, baseEnd_994255] using wordTrace_append hprefix tailTrace_994255
  have hstable : (prefixWord ++ tailWord_994255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994255).length < 2 ^ (prefixWord ++ tailWord_994255).sum := by decide
  have hdescent : baseEnd_994255 < baseStart_994255 := by decide
  rcases family_descends (prefixWord ++ tailWord_994255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994258 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_994258 : Nat := 118140960795 + 994258 * 2 ^ 59
def prefixEnd_994258 : Nat := 4983230072969 + 3 ^ 40 * 994258 * 2
def baseEnd_994258 : Nat := 226903221590256086534443

theorem tailTrace_994258 : CollatzResearch.WordTrace tailWord_994258 prefixEnd_994258 226903221590256086534443 := by
  unfold tailWord_994258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065892107995136648145857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24175712287987031061722285 9065892107995136648145857)
  ·
    refine ⟨6799419080996352486109393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9065892107995136648145857 6799419080996352486109393)
    ·
      refine ⟨5099564310747264364582045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6799419080996352486109393 5099564310747264364582045)
      ·
        refine ⟨1912336616530224136718267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5099564310747264364582045 1912336616530224136718267)
        ·
          refine ⟨2868504924795336205077401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912336616530224136718267 2868504924795336205077401)
          ·
            refine ⟨2151378693596502153808051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868504924795336205077401 2151378693596502153808051)
            ·
              refine ⟨3227068040394753230712077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151378693596502153808051 3227068040394753230712077)
              ·
                refine ⟨1210150515148032461517029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3227068040394753230712077 1210150515148032461517029)
                ·
                  refine ⟨226903221590256086534443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1210150515148032461517029 226903221590256086534443)
                  ·
                    rfl

theorem cell21_994258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_994258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994258 prefixEnd_994258 := by exact prefixLift 994258
  have htrace : WordTrace (prefixWord ++ tailWord_994258) baseStart_994258 baseEnd_994258 := by
    simpa [prefixWord, tailWord_994258, baseEnd_994258] using wordTrace_append hprefix tailTrace_994258
  have hstable : (prefixWord ++ tailWord_994258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994258).length < 2 ^ (prefixWord ++ tailWord_994258).sum := by decide
  have hdescent : baseEnd_994258 < baseStart_994258 := by decide
  rcases family_descends (prefixWord ++ tailWord_994258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994306 : List Nat := [3, 4, 1, 3, 1, 2, 1, 6]
def baseStart_994306 : Nat := 118140960795 + 994306 * 2 ^ 59
def prefixEnd_994306 : Nat := 4983230072969 + 3 ^ 40 * 994306 * 2
def baseEnd_994306 : Nat := 75638058614739556578115

theorem tailTrace_994306 : CollatzResearch.WordTrace tailWord_994306 prefixEnd_994306 75638058614739556578115 := by
  unfold tailWord_994306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066329783951662697582693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24176879423871100526887181 9066329783951662697582693)
  ·
    refine ⟨1699936834490936755796755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9066329783951662697582693 1699936834490936755796755)
    ·
      refine ⟨2549905251736405133695133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699936834490936755796755 2549905251736405133695133)
      ·
        refine ⟨956214469401151925135675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2549905251736405133695133 956214469401151925135675)
        ·
          refine ⟨1434321704101727887703513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956214469401151925135675 1434321704101727887703513)
          ·
            refine ⟨1075741278076295915777635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434321704101727887703513 1075741278076295915777635)
            ·
              refine ⟨1613611917114443873666453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075741278076295915777635 1613611917114443873666453)
              ·
                refine ⟨75638058614739556578115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1613611917114443873666453 75638058614739556578115)
                ·
                  rfl

theorem cell21_994306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_994306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994306 prefixEnd_994306 := by exact prefixLift 994306
  have htrace : WordTrace (prefixWord ++ tailWord_994306) baseStart_994306 baseEnd_994306 := by
    simpa [prefixWord, tailWord_994306, baseEnd_994306] using wordTrace_append hprefix tailTrace_994306
  have hstable : (prefixWord ++ tailWord_994306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994306).length < 2 ^ (prefixWord ++ tailWord_994306).sum := by decide
  have hdescent : baseEnd_994306 < baseStart_994306 := by decide
  rcases family_descends (prefixWord ++ tailWord_994306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994407 : List Nat := [1, 1, 5, 1, 1, 5, 7]
def baseStart_994407 : Nat := 118140960795 + 994407 * 2 ^ 59
def prefixEnd_994407 : Nat := 4983230072969 + 3 ^ 40 * 994407 * 2
def baseEnd_994407 : Nat := 25215247268918326505645

theorem tailTrace_994407 : CollatzResearch.WordTrace tailWord_994407 prefixEnd_994407 25215247268918326505645 := by
  unfold tailWord_994407
  simp only [CollatzResearch.WordTrace]
  refine ⟨36269002908440745039757475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24179335272293830026504983 36269002908440745039757475)
  ·
    refine ⟨54403504362661117559636213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36269002908440745039757475 54403504362661117559636213)
    ·
      refine ⟨5100328533999479771215895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54403504362661117559636213 5100328533999479771215895)
      ·
        refine ⟨7650492800999219656823843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100328533999479771215895 7650492800999219656823843)
        ·
          refine ⟨11475739201498829485235765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650492800999219656823843 11475739201498829485235765)
          ·
            refine ⟨1075850550140515264240853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11475739201498829485235765 1075850550140515264240853)
            ·
              refine ⟨25215247268918326505645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1075850550140515264240853 25215247268918326505645)
              ·
                rfl

theorem cell21_994407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 7].length) (baseStart_994407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994407 prefixEnd_994407 := by exact prefixLift 994407
  have htrace : WordTrace (prefixWord ++ tailWord_994407) baseStart_994407 baseEnd_994407 := by
    simpa [prefixWord, tailWord_994407, baseEnd_994407] using wordTrace_append hprefix tailTrace_994407
  have hstable : (prefixWord ++ tailWord_994407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994407).length < 2 ^ (prefixWord ++ tailWord_994407).sum := by decide
  have hdescent : baseEnd_994407 < baseStart_994407 := by decide
  rcases family_descends (prefixWord ++ tailWord_994407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994469 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 4]
def baseStart_994469 : Nat := 118140960795 + 994469 * 2 ^ 59
def prefixEnd_994469 : Nat := 4983230072969 + 3 ^ 40 * 994469 * 2
def baseEnd_994469 : Nat := 226951374664966608517345

theorem tailTrace_994469 : CollatzResearch.WordTrace tailWord_994469 prefixEnd_994469 226951374664966608517345 := by
  unfold tailWord_994469
  simp only [CollatzResearch.WordTrace]
  refine ⟨36271264234216129628514461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24180842822810753085676307 36271264234216129628514461)
  ·
    refine ⟨13601724087831048610692923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36271264234216129628514461 13601724087831048610692923)
    ·
      refine ⟨20402586131746572916039385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13601724087831048610692923 20402586131746572916039385)
      ·
        refine ⟨15301939598809929687029539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20402586131746572916039385 15301939598809929687029539)
        ·
          refine ⟨22952909398214894530544309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15301939598809929687029539 22952909398214894530544309)
          ·
            refine ⟨2151835256082646362238529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22952909398214894530544309 2151835256082646362238529)
            ·
              refine ⟨1613876442061984771678897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151835256082646362238529 1613876442061984771678897)
              ·
                refine ⟨1210407331546488578759173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613876442061984771678897 1210407331546488578759173)
                ·
                  refine ⟨226951374664966608517345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1210407331546488578759173 226951374664966608517345)
                  ·
                    rfl

theorem cell21_994469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_994469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994469 prefixEnd_994469 := by exact prefixLift 994469
  have htrace : WordTrace (prefixWord ++ tailWord_994469) baseStart_994469 baseEnd_994469 := by
    simpa [prefixWord, tailWord_994469, baseEnd_994469] using wordTrace_append hprefix tailTrace_994469
  have hstable : (prefixWord ++ tailWord_994469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994469).length < 2 ^ (prefixWord ++ tailWord_994469).sum := by decide
  have hdescent : baseEnd_994469 < baseStart_994469 := by decide
  rcases family_descends (prefixWord ++ tailWord_994469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994528 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_994528 : Nat := 118140960795 + 994528 * 2 ^ 59
def prefixEnd_994528 : Nat := 4983230072969 + 3 ^ 40 * 994528 * 2
def baseEnd_994528 : Nat := 226964839268795617033891

theorem tailTrace_994528 : CollatzResearch.WordTrace tailWord_994528 prefixEnd_994528 226964839268795617033891 := by
  unfold tailWord_994528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18136708070501191352456119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24182277427334921803274825 18136708070501191352456119)
  ·
    refine ⟨27205062105751787028684179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18136708070501191352456119 27205062105751787028684179)
    ·
      refine ⟨40807593158627680543026269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27205062105751787028684179 40807593158627680543026269)
      ·
        refine ⟨15302847434485380203634851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40807593158627680543026269 15302847434485380203634851)
        ·
          refine ⟨22954271151728070305452277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15302847434485380203634851 22954271151728070305452277)
          ·
            refine ⟨2151962920474506591136151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22954271151728070305452277 2151962920474506591136151)
            ·
              refine ⟨3227944380711759886704227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151962920474506591136151 3227944380711759886704227)
              ·
                refine ⟨4841916571067639830056341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227944380711759886704227 4841916571067639830056341)
                ·
                  refine ⟨226964839268795617033891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4841916571067639830056341 226964839268795617033891)
                  ·
                    rfl

theorem cell21_994528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_994528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994528 prefixEnd_994528 := by exact prefixLift 994528
  have htrace : WordTrace (prefixWord ++ tailWord_994528) baseStart_994528 baseEnd_994528 := by
    simpa [prefixWord, tailWord_994528, baseEnd_994528] using wordTrace_append hprefix tailTrace_994528
  have hstable : (prefixWord ++ tailWord_994528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994528).length < 2 ^ (prefixWord ++ tailWord_994528).sum := by decide
  have hdescent : baseEnd_994528 < baseStart_994528 := by decide
  rcases family_descends (prefixWord ++ tailWord_994528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994559 : List Nat := [1, 1, 2, 2, 1, 5, 4, 5]
def baseStart_994559 : Nat := 118140960795 + 994559 * 2 ^ 59
def prefixEnd_994559 : Nat := 4983230072969 + 3 ^ 40 * 994559 * 2
def baseEnd_994559 : Nat := 75657304630382150672387

theorem tailTrace_994559 : CollatzResearch.WordTrace tailWord_994559 prefixEnd_994559 75657304630382150672387 := by
  unfold tailWord_994559
  simp only [CollatzResearch.WordTrace]
  refine ⟨36274546803890074999290731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24183031202593383332860487 36274546803890074999290731)
  ·
    refine ⟨54411820205835112498936097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36274546803890074999290731 54411820205835112498936097)
    ·
      refine ⟨40808865154376334374202073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54411820205835112498936097 40808865154376334374202073)
      ·
        refine ⟨30606648865782250780651555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40808865154376334374202073 30606648865782250780651555)
        ·
          refine ⟨45909973298673376170977333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30606648865782250780651555 45909973298673376170977333)
          ·
            refine ⟨4304059996750629016029125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45909973298673376170977333 4304059996750629016029125)
            ·
              refine ⟨807011249390742940505461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4304059996750629016029125 807011249390742940505461)
              ·
                refine ⟨75657304630382150672387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 807011249390742940505461 75657304630382150672387)
                ·
                  rfl

theorem cell21_994559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 5].length) (baseStart_994559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994559 prefixEnd_994559 := by exact prefixLift 994559
  have htrace : WordTrace (prefixWord ++ tailWord_994559) baseStart_994559 baseEnd_994559 := by
    simpa [prefixWord, tailWord_994559, baseEnd_994559] using wordTrace_append hprefix tailTrace_994559
  have hstable : (prefixWord ++ tailWord_994559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994559).length < 2 ^ (prefixWord ++ tailWord_994559).sum := by decide
  have hdescent : baseEnd_994559 < baseStart_994559 := by decide
  rcases family_descends (prefixWord ++ tailWord_994559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994618 : List Nat := [3, 1, 1, 1, 4, 1, 1, 9]
def baseStart_994618 : Nat := 118140960795 + 994618 * 2 ^ 59
def prefixEnd_994618 : Nat := 4983230072969 + 3 ^ 40 * 994618 * 2
def baseEnd_994618 : Nat := 75661792831658486844569

theorem tailTrace_994618 : CollatzResearch.WordTrace tailWord_994618 prefixEnd_994618 75661792831658486844569 := by
  unfold tailWord_994618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069174677669082018922127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24184465807117552050459005 9069174677669082018922127)
  ·
    refine ⟨13603762016503623028383191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9069174677669082018922127 13603762016503623028383191)
    ·
      refine ⟨20405643024755434542574787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13603762016503623028383191 20405643024755434542574787)
      ·
        refine ⟨30608464537133151813862181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20405643024755434542574787 30608464537133151813862181)
        ·
          refine ⟨5739087100712465965099159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30608464537133151813862181 5739087100712465965099159)
          ·
            refine ⟨8608630651068698947648739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739087100712465965099159 8608630651068698947648739)
            ·
              refine ⟨12912945976603048421473109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8608630651068698947648739 12912945976603048421473109)
              ·
                refine ⟨75661792831658486844569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12912945976603048421473109 75661792831658486844569)
                ·
                  rfl

theorem cell21_994618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_994618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994618 prefixEnd_994618 := by exact prefixLift 994618
  have htrace : WordTrace (prefixWord ++ tailWord_994618) baseStart_994618 baseEnd_994618 := by
    simpa [prefixWord, tailWord_994618, baseEnd_994618] using wordTrace_append hprefix tailTrace_994618
  have hstable : (prefixWord ++ tailWord_994618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994618).length < 2 ^ (prefixWord ++ tailWord_994618).sum := by decide
  have hdescent : baseEnd_994618 < baseStart_994618 := by decide
  rcases family_descends (prefixWord ++ tailWord_994618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994728 : List Nat := [2, 1, 6, 1, 2, 1, 1, 7]
def baseStart_994728 : Nat := 118140960795 + 994728 * 2 ^ 59
def prefixEnd_994728 : Nat := 4983230072969 + 3 ^ 40 * 994728 * 2
def baseEnd_994728 : Nat := 75670160664546571233383

theorem tailTrace_994728 : CollatzResearch.WordTrace tailWord_994728 prefixEnd_994728 75670160664546571233383 := by
  unfold tailWord_994728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140355370138908431096419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24187140493518544574795225 18140355370138908431096419)
  ·
    refine ⟨27210533055208362646644629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18140355370138908431096419 27210533055208362646644629)
    ·
      refine ⟨1275493736962891999061467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27210533055208362646644629 1275493736962891999061467)
      ·
        refine ⟨1913240605444337998592201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275493736962891999061467 1913240605444337998592201)
        ·
          refine ⟨1434930454083253498944151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1913240605444337998592201 1434930454083253498944151)
          ·
            refine ⟨2152395681124880248416227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434930454083253498944151 2152395681124880248416227)
            ·
              refine ⟨3228593521687320372624341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152395681124880248416227 3228593521687320372624341)
              ·
                refine ⟨75670160664546571233383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3228593521687320372624341 75670160664546571233383)
                ·
                  rfl

theorem cell21_994728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_994728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994728 prefixEnd_994728 := by exact prefixLift 994728
  have htrace : WordTrace (prefixWord ++ tailWord_994728) baseStart_994728 baseEnd_994728 := by
    simpa [prefixWord, tailWord_994728, baseEnd_994728] using wordTrace_append hprefix tailTrace_994728
  have hstable : (prefixWord ++ tailWord_994728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994728).length < 2 ^ (prefixWord ++ tailWord_994728).sum := by decide
  have hdescent : baseEnd_994728 < baseStart_994728 := by decide
  rcases family_descends (prefixWord ++ tailWord_994728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994759 : List Nat := [1, 1, 4, 1, 1, 3, 5, 2, 3]
def baseStart_994759 : Nat := 118140960795 + 994759 * 2 ^ 59
def prefixEnd_994759 : Nat := 4983230072969 + 3 ^ 40 * 994759 * 2
def baseEnd_994759 : Nat := 227017556615990548683419

theorem tailTrace_994759 : CollatzResearch.WordTrace tailWord_994759 prefixEnd_994759 227017556615990548683419 := by
  unfold tailWord_994759
  simp only [CollatzResearch.WordTrace]
  refine ⟨36281841403165509156571331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24187894268777006104380887 36281841403165509156571331)
  ·
    refine ⟨54422762104748263734856997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36281841403165509156571331 54422762104748263734856997)
    ·
      refine ⟨10204267894640299450285687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54422762104748263734856997 10204267894640299450285687)
      ·
        refine ⟨15306401841960449175428531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204267894640299450285687 15306401841960449175428531)
        ·
          refine ⟨22959602762940673763142797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15306401841960449175428531 22959602762940673763142797)
          ·
            refine ⟨8609851036102752661178549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22959602762940673763142797 8609851036102752661178549)
            ·
              refine ⟨807173534634633061985489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8609851036102752661178549 807173534634633061985489)
              ·
                refine ⟨605380150975974796489117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807173534634633061985489 605380150975974796489117)
                ·
                  refine ⟨227017556615990548683419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605380150975974796489117 227017556615990548683419)
                  ·
                    rfl

theorem cell21_994759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 3].length) (baseStart_994759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994759 prefixEnd_994759 := by exact prefixLift 994759
  have htrace : WordTrace (prefixWord ++ tailWord_994759) baseStart_994759 baseEnd_994759 := by
    simpa [prefixWord, tailWord_994759, baseEnd_994759] using wordTrace_append hprefix tailTrace_994759
  have hstable : (prefixWord ++ tailWord_994759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994759).length < 2 ^ (prefixWord ++ tailWord_994759).sum := by decide
  have hdescent : baseEnd_994759 < baseStart_994759 := by decide
  rcases family_descends (prefixWord ++ tailWord_994759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994908 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_994908 : Nat := 118140960795 + 994908 * 2 ^ 59
def prefixEnd_994908 : Nat := 4983230072969 + 3 ^ 40 * 994908 * 2
def baseEnd_994908 : Nat := 227051560445999400699781

theorem tailTrace_994908 : CollatzResearch.WordTrace tailWord_994908 prefixEnd_994908 227051560445999400699781 := by
  unfold tailWord_994908
  simp only [CollatzResearch.WordTrace]
  refine ⟨18143637939812853801872689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24191517253083805069163585 18143637939812853801872689)
  ·
    refine ⟨13607728454859640351404517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18143637939812853801872689 13607728454859640351404517)
    ·
      refine ⟨2551449085286182565888347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13607728454859640351404517 2551449085286182565888347)
      ·
        refine ⟨3827173627929273848832521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551449085286182565888347 3827173627929273848832521)
        ·
          refine ⟨2870380220946955386624391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3827173627929273848832521 2870380220946955386624391)
          ·
            refine ⟨4305570331420433079936587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870380220946955386624391 4305570331420433079936587)
            ·
              refine ⟨6458355497130649619904881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305570331420433079936587 6458355497130649619904881)
              ·
                refine ⟨4843766622847987214928661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6458355497130649619904881 4843766622847987214928661)
                ·
                  refine ⟨227051560445999400699781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4843766622847987214928661 227051560445999400699781)
                  ·
                    rfl

theorem cell21_994908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_994908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994908 prefixEnd_994908 := by exact prefixLift 994908
  have htrace : WordTrace (prefixWord ++ tailWord_994908) baseStart_994908 baseEnd_994908 := by
    simpa [prefixWord, tailWord_994908, baseEnd_994908] using wordTrace_append hprefix tailTrace_994908
  have hstable : (prefixWord ++ tailWord_994908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994908).length < 2 ^ (prefixWord ++ tailWord_994908).sum := by decide
  have hdescent : baseEnd_994908 < baseStart_994908 := by decide
  rcases family_descends (prefixWord ++ tailWord_994908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_994922 : List Nat := [3, 1, 3, 2, 1, 2, 9]
def baseStart_994922 : Nat := 118140960795 + 994922 * 2 ^ 59
def prefixEnd_994922 : Nat := 4983230072969 + 3 ^ 40 * 994922 * 2
def baseEnd_994922 : Nat := 25228306159637609718491

theorem tailTrace_994922 : CollatzResearch.WordTrace tailWord_994922 prefixEnd_994922 25228306159637609718491 := by
  unfold tailWord_994922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9071946625393746998688755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24191857667716658663170013 9071946625393746998688755)
  ·
    refine ⟨13607919938090620498033133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9071946625393746998688755 13607919938090620498033133)
    ·
      refine ⟨5102969976783982686762425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13607919938090620498033133 5102969976783982686762425)
      ·
        refine ⟨3827227482587987015071819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5102969976783982686762425 3827227482587987015071819)
        ·
          refine ⟨5740841223881980522607729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827227482587987015071819 5740841223881980522607729)
          ·
            refine ⟨4305630917911485391955797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5740841223881980522607729 4305630917911485391955797)
            ·
              refine ⟨25228306159637609718491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4305630917911485391955797 25228306159637609718491)
              ·
                rfl

theorem cell21_994922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 9].length) (baseStart_994922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_994922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_994922 prefixEnd_994922 := by exact prefixLift 994922
  have htrace : WordTrace (prefixWord ++ tailWord_994922) baseStart_994922 baseEnd_994922 := by
    simpa [prefixWord, tailWord_994922, baseEnd_994922] using wordTrace_append hprefix tailTrace_994922
  have hstable : (prefixWord ++ tailWord_994922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_994922).length < 2 ^ (prefixWord ++ tailWord_994922).sum := by decide
  have hdescent : baseEnd_994922 < baseStart_994922 := by decide
  rcases family_descends (prefixWord ++ tailWord_994922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995105 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 5]
def baseStart_995105 : Nat := 118140960795 + 995105 * 2 ^ 59
def prefixEnd_995105 : Nat := 4983230072969 + 3 ^ 40 * 995105 * 2
def baseEnd_995105 : Nat := 227096518529970835916045

theorem tailTrace_995105 : CollatzResearch.WordTrace tailWord_995105 prefixEnd_995105 227096518529970835916045 := by
  unfold tailWord_995105
  simp only [CollatzResearch.WordTrace]
  refine ⟨36294461059912010248666769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24196307373274673499111179 36294461059912010248666769)
  ·
    refine ⟨27220845794934007686500077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36294461059912010248666769 27220845794934007686500077)
    ·
      refine ⟨10207817173100252882437529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27220845794934007686500077 10207817173100252882437529)
      ·
        refine ⟨7655862879825189661828147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10207817173100252882437529 7655862879825189661828147)
        ·
          refine ⟨11483794319737784492742221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655862879825189661828147 11483794319737784492742221)
          ·
            refine ⟨4306422869901669184778333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11483794319737784492742221 4306422869901669184778333)
            ·
              refine ⟨1614908576213125944291875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4306422869901669184778333 1614908576213125944291875)
              ·
                refine ⟨2422362864319688916437813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614908576213125944291875 2422362864319688916437813)
                ·
                  refine ⟨227096518529970835916045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422362864319688916437813 227096518529970835916045)
                  ·
                    rfl

theorem cell21_995105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_995105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995105 prefixEnd_995105 := by exact prefixLift 995105
  have htrace : WordTrace (prefixWord ++ tailWord_995105) baseStart_995105 baseEnd_995105 := by
    simpa [prefixWord, tailWord_995105, baseEnd_995105] using wordTrace_append hprefix tailTrace_995105
  have hstable : (prefixWord ++ tailWord_995105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995105).length < 2 ^ (prefixWord ++ tailWord_995105).sum := by decide
  have hdescent : baseEnd_995105 < baseStart_995105 := by decide
  rcases family_descends (prefixWord ++ tailWord_995105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995119 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 4]
def baseStart_995119 : Nat := 118140960795 + 995119 * 2 ^ 59
def prefixEnd_995119 : Nat := 4983230072969 + 3 ^ 40 * 995119 * 2
def baseEnd_995119 : Nat := 227099713520709922682683

theorem tailTrace_995119 : CollatzResearch.WordTrace tailWord_995119 prefixEnd_995119 227099713520709922682683 := by
  unfold tailWord_995119
  simp only [CollatzResearch.WordTrace]
  refine ⟨36294971681861290639676411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24196647787907527093117607 36294971681861290639676411)
  ·
    refine ⟨54442457522791935959514617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36294971681861290639676411 54442457522791935959514617)
    ·
      refine ⟨40831843142093951969635963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54442457522791935959514617 40831843142093951969635963)
      ·
        refine ⟨61247764713140927954453945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40831843142093951969635963 61247764713140927954453945)
        ·
          refine ⟨45935823534855695965840459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61247764713140927954453945 45935823534855695965840459)
          ·
            refine ⟨68903735302283543948760689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45935823534855695965840459 68903735302283543948760689)
            ·
              refine ⟨51677801476712657961570517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68903735302283543948760689 51677801476712657961570517)
              ·
                refine ⟨1211198472110452920974309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51677801476712657961570517 1211198472110452920974309)
                ·
                  refine ⟨227099713520709922682683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211198472110452920974309 227099713520709922682683)
                  ·
                    rfl

theorem cell21_995119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_995119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995119 prefixEnd_995119 := by exact prefixLift 995119
  have htrace : WordTrace (prefixWord ++ tailWord_995119) baseStart_995119 baseEnd_995119 := by
    simpa [prefixWord, tailWord_995119, baseEnd_995119] using wordTrace_append hprefix tailTrace_995119
  have hstable : (prefixWord ++ tailWord_995119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995119).length < 2 ^ (prefixWord ++ tailWord_995119).sum := by decide
  have hdescent : baseEnd_995119 < baseStart_995119 := by decide
  rcases family_descends (prefixWord ++ tailWord_995119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995156 : List Nat := [2, 4, 1, 1, 3, 3, 2, 2, 3]
def baseStart_995156 : Nat := 118140960795 + 995156 * 2 ^ 59
def prefixEnd_995156 : Nat := 4983230072969 + 3 ^ 40 * 995156 * 2
def baseEnd_995156 : Nat := 227108157424806080565941

theorem tailTrace_995156 : CollatzResearch.WordTrace tailWord_995156 prefixEnd_995156 227108157424806080565941 := by
  unfold tailWord_995156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18148160591363622979386661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24197547455151497305848881 18148160591363622979386661)
  ·
    refine ⟨3402780110880679308634999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18148160591363622979386661 3402780110880679308634999)
    ·
      refine ⟨5104170166321018962952499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3402780110880679308634999 5104170166321018962952499)
      ·
        refine ⟨7656255249481528444428749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104170166321018962952499 7656255249481528444428749)
        ·
          refine ⟨2871095718555573166660781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7656255249481528444428749 2871095718555573166660781)
          ·
            refine ⟨1076660894458339937497793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2871095718555573166660781 1076660894458339937497793)
            ·
              refine ⟨807495670843754953123345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076660894458339937497793 807495670843754953123345)
              ·
                refine ⟨605621753132816214842509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807495670843754953123345 605621753132816214842509)
                ·
                  refine ⟨227108157424806080565941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605621753132816214842509 227108157424806080565941)
                  ·
                    rfl

theorem cell21_995156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_995156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995156 prefixEnd_995156 := by exact prefixLift 995156
  have htrace : WordTrace (prefixWord ++ tailWord_995156) baseStart_995156 baseEnd_995156 := by
    simpa [prefixWord, tailWord_995156, baseEnd_995156] using wordTrace_append hprefix tailTrace_995156
  have hstable : (prefixWord ++ tailWord_995156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995156).length < 2 ^ (prefixWord ++ tailWord_995156).sum := by decide
  have hdescent : baseEnd_995156 < baseStart_995156 := by decide
  rcases family_descends (prefixWord ++ tailWord_995156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995209 : List Nat := [1, 2, 1, 1, 5, 1, 10]
def baseStart_995209 : Nat := 118140960795 + 995209 * 2 ^ 59
def prefixEnd_995209 : Nat := 4983230072969 + 3 ^ 40 * 995209 * 2
def baseEnd_995209 : Nat := 25235583638543307353611

theorem tailTrace_995209 : CollatzResearch.WordTrace tailWord_995209 prefixEnd_995209 25235583638543307353611 := by
  unfold tailWord_995209
  simp only [CollatzResearch.WordTrace]
  refine ⟨36298254251535236010452681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24198836167690157340301787 36298254251535236010452681)
  ·
    refine ⟨27223690688651427007839511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36298254251535236010452681 27223690688651427007839511)
    ·
      refine ⟨40835536032977140511759267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27223690688651427007839511 40835536032977140511759267)
      ·
        refine ⟨61253304049465710767638901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40835536032977140511759267 61253304049465710767638901)
        ·
          refine ⟨5742497254637410384466147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61253304049465710767638901 5742497254637410384466147)
          ·
            refine ⟨8613745881956115576699221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742497254637410384466147 8613745881956115576699221)
            ·
              refine ⟨25235583638543307353611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8613745881956115576699221 25235583638543307353611)
              ·
                rfl

theorem cell21_995209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 10].length) (baseStart_995209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995209 prefixEnd_995209 := by exact prefixLift 995209
  have htrace : WordTrace (prefixWord ++ tailWord_995209) baseStart_995209 baseEnd_995209 := by
    simpa [prefixWord, tailWord_995209, baseEnd_995209] using wordTrace_append hprefix tailTrace_995209
  have hstable : (prefixWord ++ tailWord_995209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995209).length < 2 ^ (prefixWord ++ tailWord_995209).sum := by decide
  have hdescent : baseEnd_995209 < baseStart_995209 := by decide
  rcases family_descends (prefixWord ++ tailWord_995209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_995229 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 4]
def baseStart_995229 : Nat := 118140960795 + 995229 * 2 ^ 59
def prefixEnd_995229 : Nat := 4983230072969 + 3 ^ 40 * 995229 * 2
def baseEnd_995229 : Nat := 227124817019374175849125

theorem tailTrace_995229 : CollatzResearch.WordTrace tailWord_995229 prefixEnd_995229 227124817019374175849125 := by
  unfold tailWord_995229
  simp only [CollatzResearch.WordTrace]
  refine ⟨36298983711462779426180741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24199322474308519617453827 36298983711462779426180741)
  ·
    refine ⟨6806059445899271142408889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36298983711462779426180741 6806059445899271142408889)
    ·
      refine ⟨5104544584424453356806667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6806059445899271142408889 5104544584424453356806667)
      ·
        refine ⟨7656816876636680035210001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104544584424453356806667 7656816876636680035210001)
        ·
          refine ⟨5742612657477510026407501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7656816876636680035210001 5742612657477510026407501)
          ·
            refine ⟨2153479746554066259902813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5742612657477510026407501 2153479746554066259902813)
            ·
              refine ⟨807554904957774847463555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2153479746554066259902813 807554904957774847463555)
              ·
                refine ⟨1211332357436662271195333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807554904957774847463555 1211332357436662271195333)
                ·
                  refine ⟨227124817019374175849125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211332357436662271195333 227124817019374175849125)
                  ·
                    rfl

theorem cell21_995229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_995229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_995229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_995229 prefixEnd_995229 := by exact prefixLift 995229
  have htrace : WordTrace (prefixWord ++ tailWord_995229) baseStart_995229 baseEnd_995229 := by
    simpa [prefixWord, tailWord_995229, baseEnd_995229] using wordTrace_append hprefix tailTrace_995229
  have hstable : (prefixWord ++ tailWord_995229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_995229).length < 2 ^ (prefixWord ++ tailWord_995229).sum := by decide
  have hdescent : baseEnd_995229 < baseStart_995229 := by decide
  rcases family_descends (prefixWord ++ tailWord_995229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
