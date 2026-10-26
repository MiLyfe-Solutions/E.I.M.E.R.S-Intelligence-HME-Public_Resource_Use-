import V185TrunkScan22Chunk140

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1261778 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1261778 : Nat := 118140960795 + 1261778 * 2 ^ 59
def prefixEnd_1261778 : Nat := 4983230072969 + 3 ^ 40 * 1261778 * 2
def baseEnd_1261778 : Nat := 431932395512579680981463

theorem tailTrace_1261778 : CollatzResearch.WordTrace tailWord_1261778 prefixEnd_1261778 431932395512579680981463 := by
  unfold tailWord_1261778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11505206105700318842778497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30680549615200850247409325 11505206105700318842778497)
  ·
    refine ⟨8628904579275239132083873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11505206105700318842778497 8628904579275239132083873)
    ·
      refine ⟨6471678434456429349062905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8628904579275239132083873 6471678434456429349062905)
      ·
        refine ⟨4853758825842322011797179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6471678434456429349062905 4853758825842322011797179)
        ·
          refine ⟨7280638238763483017695769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853758825842322011797179 7280638238763483017695769)
          ·
            refine ⟨5460478679072612263271827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7280638238763483017695769 5460478679072612263271827)
            ·
              refine ⟨8190718018608918394907741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5460478679072612263271827 8190718018608918394907741)
              ·
                refine ⟨3071519256978344398090403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8190718018608918394907741 3071519256978344398090403)
                ·
                  refine ⟨4607278885467516597135605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071519256978344398090403 4607278885467516597135605)
                  ·
                    refine ⟨431932395512579680981463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4607278885467516597135605 431932395512579680981463)
                    ·
                      rfl

theorem cell22_1261778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1261778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261778 prefixEnd_1261778 := by exact prefixLift 1261778
  have htrace : WordTrace (prefixWord ++ tailWord_1261778) baseStart_1261778 baseEnd_1261778 := by
    simpa [prefixWord, tailWord_1261778, baseEnd_1261778] using wordTrace_append hprefix tailTrace_1261778
  have hstable : (prefixWord ++ tailWord_1261778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261778).length < 2 ^ (prefixWord ++ tailWord_1261778).sum := by decide
  have hdescent : baseEnd_1261778 < baseStart_1261778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261821 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1261821 : Nat := 118140960795 + 1261821 * 2 ^ 59
def prefixEnd_1261821 : Nat := 4983230072969 + 3 ^ 40 * 1261821 * 2
def baseEnd_1261821 : Nat := 431947115291341902156331

theorem tailTrace_1261821 : CollatzResearch.WordTrace tailWord_1261821 prefixEnd_1261821 431947115291341902156331 := by
  unfold tailWord_1261821
  simp only [CollatzResearch.WordTrace]
  refine ⟨46022392761645493714929317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30681595174430329143286211 46022392761645493714929317)
  ·
    refine ⟨8629198642808530071549247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46022392761645493714929317 8629198642808530071549247)
    ·
      refine ⟨12943797964212795107323871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8629198642808530071549247 12943797964212795107323871)
      ·
        refine ⟨19415696946319192660985807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12943797964212795107323871 19415696946319192660985807)
        ·
          refine ⟨29123545419478788991478711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19415696946319192660985807 29123545419478788991478711)
          ·
            refine ⟨43685318129218183487218067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29123545419478788991478711 43685318129218183487218067)
            ·
              refine ⟨65527977193827275230827101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43685318129218183487218067 65527977193827275230827101)
              ·
                refine ⟨24572991447685228211560163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65527977193827275230827101 24572991447685228211560163)
                ·
                  refine ⟨36859487171527842317340245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24572991447685228211560163 36859487171527842317340245)
                  ·
                    refine ⟨431947115291341902156331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36859487171527842317340245 431947115291341902156331)
                    ·
                      rfl

theorem cell22_1261821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1261821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261821 prefixEnd_1261821 := by exact prefixLift 1261821
  have htrace : WordTrace (prefixWord ++ tailWord_1261821) baseStart_1261821 baseEnd_1261821 := by
    simpa [prefixWord, tailWord_1261821, baseEnd_1261821] using wordTrace_append hprefix tailTrace_1261821
  have hstable : (prefixWord ++ tailWord_1261821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261821).length < 2 ^ (prefixWord ++ tailWord_1261821).sum := by decide
  have hdescent : baseEnd_1261821 < baseStart_1261821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261851 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 1, 7]
def baseStart_1261851 : Nat := 118140960795 + 1261851 * 2 ^ 59
def prefixEnd_1261851 : Nat := 4983230072969 + 3 ^ 40 * 1261851 * 2
def baseEnd_1261851 : Nat := 431957384904431823906239

theorem tailTrace_1261851 : CollatzResearch.WordTrace tailWord_1261851 prefixEnd_1261851 431957384904431823906239 := by
  unfold tailWord_1261851
  simp only [CollatzResearch.WordTrace]
  refine ⟨46023486951536808838521407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30682324634357872559014271 46023486951536808838521407)
  ·
    refine ⟨69035230427305213257782111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46023486951536808838521407 69035230427305213257782111)
    ·
      refine ⟨103552845640957819886673167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69035230427305213257782111 103552845640957819886673167)
      ·
        refine ⟨155329268461436729830009751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103552845640957819886673167 155329268461436729830009751)
        ·
          refine ⟨232993902692155094745014627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155329268461436729830009751 232993902692155094745014627)
          ·
            refine ⟨349490854038232642117521941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232993902692155094745014627 349490854038232642117521941)
            ·
              refine ⟨16382383783042155099258841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 349490854038232642117521941 16382383783042155099258841)
              ·
                refine ⟨12286787837281616324444131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16382383783042155099258841 12286787837281616324444131)
                ·
                  refine ⟨18430181755922424486666197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12286787837281616324444131 18430181755922424486666197)
                  ·
                    refine ⟨431957384904431823906239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18430181755922424486666197 431957384904431823906239)
                    ·
                      rfl

theorem cell22_1261851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_1261851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261851 prefixEnd_1261851 := by exact prefixLift 1261851
  have htrace : WordTrace (prefixWord ++ tailWord_1261851) baseStart_1261851 baseEnd_1261851 := by
    simpa [prefixWord, tailWord_1261851, baseEnd_1261851] using wordTrace_append hprefix tailTrace_1261851
  have hstable : (prefixWord ++ tailWord_1261851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261851).length < 2 ^ (prefixWord ++ tailWord_1261851).sum := by decide
  have hdescent : baseEnd_1261851 < baseStart_1261851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261857 : List Nat := [1, 2, 3, 2, 1, 1, 5, 3, 1, 3]
def baseStart_1261857 : Nat := 118140960795 + 1261857 * 2 ^ 59
def prefixEnd_1261857 : Nat := 4983230072969 + 3 ^ 40 * 1261857 * 2
def baseEnd_1261857 : Nat := 431959438827049808256221

theorem tailTrace_1261857 : CollatzResearch.WordTrace tailWord_1261857 prefixEnd_1261857 431959438827049808256221 := by
  unfold tailWord_1261857
  simp only [CollatzResearch.WordTrace]
  refine ⟨46023705789515071863239825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30682470526343381242159883 46023705789515071863239825)
  ·
    refine ⟨34517779342136303897429869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46023705789515071863239825 34517779342136303897429869)
    ·
      refine ⟨12944167253301113961536201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34517779342136303897429869 12944167253301113961536201)
      ·
        refine ⟨9708125439975835471152151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12944167253301113961536201 9708125439975835471152151)
        ·
          refine ⟨14562188159963753206728227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9708125439975835471152151 14562188159963753206728227)
          ·
            refine ⟨21843282239945629810092341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14562188159963753206728227 21843282239945629810092341)
            ·
              refine ⟨2047807709994902794696157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21843282239945629810092341 2047807709994902794696157)
              ·
                refine ⟨767927891248088548011059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2047807709994902794696157 767927891248088548011059)
                ·
                  refine ⟨1151891836872132822016589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767927891248088548011059 1151891836872132822016589)
                  ·
                    refine ⟨431959438827049808256221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151891836872132822016589 431959438827049808256221)
                    ·
                      rfl

theorem cell22_1261857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_1261857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261857 prefixEnd_1261857 := by exact prefixLift 1261857
  have htrace : WordTrace (prefixWord ++ tailWord_1261857) baseStart_1261857 baseEnd_1261857 := by
    simpa [prefixWord, tailWord_1261857, baseEnd_1261857] using wordTrace_append hprefix tailTrace_1261857
  have hstable : (prefixWord ++ tailWord_1261857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261857).length < 2 ^ (prefixWord ++ tailWord_1261857).sum := by decide
  have hdescent : baseEnd_1261857 < baseStart_1261857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261874 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_1261874 : Nat := 118140960795 + 1261874 * 2 ^ 59
def prefixEnd_1261874 : Nat := 4983230072969 + 3 ^ 40 * 1261874 * 2
def baseEnd_1261874 : Nat := 431965258274467430581169

theorem tailTrace_1261874 : CollatzResearch.WordTrace tailWord_1261874 prefixEnd_1261874 431965258274467430581169 := by
  unfold tailWord_1261874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11506081457613370941652169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30682883886968989177739117 11506081457613370941652169)
  ·
    refine ⟨8629561093210028206239127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11506081457613370941652169 8629561093210028206239127)
    ·
      refine ⟨12944341639815042309358691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8629561093210028206239127 12944341639815042309358691)
      ·
        refine ⟨19416512459722563464038037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12944341639815042309358691 19416512459722563464038037)
        ·
          refine ⟨910149021549495162376783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19416512459722563464038037 910149021549495162376783)
          ·
            refine ⟨1365223532324242743565175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910149021549495162376783 1365223532324242743565175)
            ·
              refine ⟨2047835298486364115347763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365223532324242743565175 2047835298486364115347763)
              ·
                refine ⟨3071752947729546173021645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047835298486364115347763 3071752947729546173021645)
                ·
                  refine ⟨1151907355398579814883117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3071752947729546173021645 1151907355398579814883117)
                  ·
                    refine ⟨431965258274467430581169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151907355398579814883117 431965258274467430581169)
                    ·
                      rfl

theorem cell22_1261874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_1261874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261874 prefixEnd_1261874 := by exact prefixLift 1261874
  have htrace : WordTrace (prefixWord ++ tailWord_1261874) baseStart_1261874 baseEnd_1261874 := by
    simpa [prefixWord, tailWord_1261874, baseEnd_1261874] using wordTrace_append hprefix tailTrace_1261874
  have hstable : (prefixWord ++ tailWord_1261874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261874).length < 2 ^ (prefixWord ++ tailWord_1261874).sum := by decide
  have hdescent : baseEnd_1261874 < baseStart_1261874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261932 : List Nat := [2, 2, 1, 1, 6, 1, 1, 4, 4]
def baseStart_1261932 : Nat := 118140960795 + 1261932 * 2 ^ 59
def prefixEnd_1261932 : Nat := 4983230072969 + 3 ^ 40 * 1261932 * 2
def baseEnd_1261932 : Nat := 143995037619924870876997

theorem tailTrace_1261932 : CollatzResearch.WordTrace tailWord_1261932 prefixEnd_1261932 143995037619924870876997 := by
  unfold tailWord_1261932
  simp only [CollatzResearch.WordTrace]
  refine ⟨23013220632121679836110025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30684294176162239781480033 23013220632121679836110025)
  ·
    refine ⟨17259915474091259877082519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23013220632121679836110025 17259915474091259877082519)
    ·
      refine ⟨25889873211136889815623779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17259915474091259877082519 25889873211136889815623779)
      ·
        refine ⟨38834809816705334723435669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25889873211136889815623779 38834809816705334723435669)
        ·
          refine ⟨1820381710158062565161047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38834809816705334723435669 1820381710158062565161047)
          ·
            refine ⟨2730572565237093847741571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820381710158062565161047 2730572565237093847741571)
            ·
              refine ⟨4095858847855640771612357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730572565237093847741571 4095858847855640771612357)
              ·
                refine ⟨767973533972932644677317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4095858847855640771612357 767973533972932644677317)
                ·
                  refine ⟨143995037619924870876997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 767973533972932644677317 143995037619924870876997)
                  ·
                    rfl

theorem cell22_1261932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_1261932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261932 prefixEnd_1261932 := by exact prefixLift 1261932
  have htrace : WordTrace (prefixWord ++ tailWord_1261932) baseStart_1261932 baseEnd_1261932 := by
    simpa [prefixWord, tailWord_1261932, baseEnd_1261932] using wordTrace_append hprefix tailTrace_1261932
  have hstable : (prefixWord ++ tailWord_1261932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261932).length < 2 ^ (prefixWord ++ tailWord_1261932).sum := by decide
  have hdescent : baseEnd_1261932 < baseStart_1261932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261960 : List Nat := [2, 1, 3, 3, 1, 1, 5, 6]
def baseStart_1261960 : Nat := 118140960795 + 1261960 * 2 ^ 59
def prefixEnd_1261960 : Nat := 4983230072969 + 3 ^ 40 * 1261960 * 2
def baseEnd_1261960 : Nat := 47999410870221319214545

theorem tailTrace_1261960 : CollatzResearch.WordTrace tailWord_1261960 prefixEnd_1261960 47999410870221319214545 := by
  unfold tailWord_1261960
  simp only [CollatzResearch.WordTrace]
  refine ⟨23013731254070960227119667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30684975005427946969492889 23013731254070960227119667)
  ·
    refine ⟨34520596881106440340679501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23013731254070960227119667 34520596881106440340679501)
    ·
      refine ⟨12945223830414915127754813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34520596881106440340679501 12945223830414915127754813)
      ·
        refine ⟨4854458936405593172908055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12945223830414915127754813 4854458936405593172908055)
        ·
          refine ⟨7281688404608389759362083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854458936405593172908055 7281688404608389759362083)
          ·
            refine ⟨10922532606912584639043125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281688404608389759362083 10922532606912584639043125)
            ·
              refine ⟨1023987431898054809910293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10922532606912584639043125 1023987431898054809910293)
              ·
                refine ⟨47999410870221319214545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1023987431898054809910293 47999410870221319214545)
                ·
                  rfl

theorem cell22_1261960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 6].length) (baseStart_1261960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261960 prefixEnd_1261960 := by exact prefixLift 1261960
  have htrace : WordTrace (prefixWord ++ tailWord_1261960) baseStart_1261960 baseEnd_1261960 := by
    simpa [prefixWord, tailWord_1261960, baseEnd_1261960] using wordTrace_append hprefix tailTrace_1261960
  have hstable : (prefixWord ++ tailWord_1261960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261960).length < 2 ^ (prefixWord ++ tailWord_1261960).sum := by decide
  have hdescent : baseEnd_1261960 < baseStart_1261960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261962 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_1261962 : Nat := 118140960795 + 1261962 * 2 ^ 59
def prefixEnd_1261962 : Nat := 4983230072969 + 3 ^ 40 * 1261962 * 2
def baseEnd_1261962 : Nat := 431995382472864534380899

theorem tailTrace_1261962 : CollatzResearch.WordTrace tailWord_1261962 prefixEnd_1261962 431995382472864534380899 := by
  unfold tailWord_1261962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11506883863533668698953035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30685023636089783197208093 11506883863533668698953035)
  ·
    refine ⟨17260325795300503048429553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11506883863533668698953035 17260325795300503048429553)
    ·
      refine ⟨12945244346475377286322165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17260325795300503048429553 12945244346475377286322165)
      ·
        refine ⟨1213616657482066620592703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12945244346475377286322165 1213616657482066620592703)
        ·
          refine ⟨1820424986223099930889055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213616657482066620592703 1820424986223099930889055)
          ·
            refine ⟨2730637479334649896333583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820424986223099930889055 2730637479334649896333583)
            ·
              refine ⟨4095956219001974844500375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730637479334649896333583 4095956219001974844500375)
              ·
                refine ⟨6143934328502962266750563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095956219001974844500375 6143934328502962266750563)
                ·
                  refine ⟨9215901492754443400125845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6143934328502962266750563 9215901492754443400125845)
                  ·
                    refine ⟨431995382472864534380899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9215901492754443400125845 431995382472864534380899)
                    ·
                      rfl

theorem cell22_1261962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_1261962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261962 prefixEnd_1261962 := by exact prefixLift 1261962
  have htrace : WordTrace (prefixWord ++ tailWord_1261962) baseStart_1261962 baseEnd_1261962 := by
    simpa [prefixWord, tailWord_1261962, baseEnd_1261962] using wordTrace_append hprefix tailTrace_1261962
  have hstable : (prefixWord ++ tailWord_1261962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261962).length < 2 ^ (prefixWord ++ tailWord_1261962).sum := by decide
  have hdescent : baseEnd_1261962 < baseStart_1261962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261981 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_1261981 : Nat := 118140960795 + 1261981 * 2 ^ 59
def prefixEnd_1261981 : Nat := 4983230072969 + 3 ^ 40 * 1261981 * 2
def baseEnd_1261981 : Nat := 432001886561154818155841

theorem tailTrace_1261981 : CollatzResearch.WordTrace tailWord_1261981 prefixEnd_1261981 432001886561154818155841 := by
  unfold tailWord_1261981
  simp only [CollatzResearch.WordTrace]
  refine ⟨46028228441065841040753797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30685485627377227360502531 46028228441065841040753797)
  ·
    refine ⟨8630292832699845195141337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46028228441065841040753797 8630292832699845195141337)
    ·
      refine ⟨6472719624524883896356003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8630292832699845195141337 6472719624524883896356003)
      ·
        refine ⟨9709079436787325844534005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6472719624524883896356003 9709079436787325844534005)
        ·
          refine ⟨910226197198811797925063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9709079436787325844534005 910226197198811797925063)
          ·
            refine ⟨1365339295798217696887595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910226197198811797925063 1365339295798217696887595)
            ·
              refine ⟨2048008943697326545331393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365339295798217696887595 2048008943697326545331393)
              ·
                refine ⟨1536006707772994908998545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2048008943697326545331393 1536006707772994908998545)
                ·
                  refine ⟨1152005030829746181748909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1536006707772994908998545 1152005030829746181748909)
                  ·
                    refine ⟨432001886561154818155841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1152005030829746181748909 432001886561154818155841)
                    ·
                      rfl

theorem cell22_1261981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_1261981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1261981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1261981 prefixEnd_1261981 := by exact prefixLift 1261981
  have htrace : WordTrace (prefixWord ++ tailWord_1261981) baseStart_1261981 baseEnd_1261981 := by
    simpa [prefixWord, tailWord_1261981, baseEnd_1261981] using wordTrace_append hprefix tailTrace_1261981
  have hstable : (prefixWord ++ tailWord_1261981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261981).length < 2 ^ (prefixWord ++ tailWord_1261981).sum := by decide
  have hdescent : baseEnd_1261981 < baseStart_1261981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262033 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 8]
def baseStart_1262033 : Nat := 118140960795 + 1262033 * 2 ^ 59
def prefixEnd_1262033 : Nat := 4983230072969 + 3 ^ 40 * 1262033 * 2
def baseEnd_1262033 : Nat := 144006562407948005285227

theorem tailTrace_1262033 : CollatzResearch.WordTrace tailWord_1262033 prefixEnd_1262033 144006562407948005285227 := by
  unfold tailWord_1262033
  simp only [CollatzResearch.WordTrace]
  refine ⟨46030125036877453921646753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30686750024584969281097835 46030125036877453921646753)
  ·
    refine ⟨34522593777658090441235065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46030125036877453921646753 34522593777658090441235065)
    ·
      refine ⟨25891945333243567830926299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34522593777658090441235065 25891945333243567830926299)
      ·
        refine ⟨38837917999865351746389449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25891945333243567830926299 38837917999865351746389449)
        ·
          refine ⟨29128438499899013809792087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38837917999865351746389449 29128438499899013809792087)
          ·
            refine ⟨43692657749848520714688131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29128438499899013809792087 43692657749848520714688131)
            ·
              refine ⟨65538986624772781072032197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43692657749848520714688131 65538986624772781072032197)
              ·
                refine ⟨12288559992144896451006037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65538986624772781072032197 12288559992144896451006037)
                ·
                  refine ⟨144006562407948005285227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12288559992144896451006037 144006562407948005285227)
                  ·
                    rfl

theorem cell22_1262033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_1262033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262033 prefixEnd_1262033 := by exact prefixLift 1262033
  have htrace : WordTrace (prefixWord ++ tailWord_1262033) baseStart_1262033 baseEnd_1262033 := by
    simpa [prefixWord, tailWord_1262033, baseEnd_1262033] using wordTrace_append hprefix tailTrace_1262033
  have hstable : (prefixWord ++ tailWord_1262033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262033).length < 2 ^ (prefixWord ++ tailWord_1262033).sum := by decide
  have hdescent : baseEnd_1262033 < baseStart_1262033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262065 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_1262065 : Nat := 118140960795 + 1262065 * 2 ^ 59
def prefixEnd_1262065 : Nat := 4983230072969 + 3 ^ 40 * 1262065 * 2
def baseEnd_1262065 : Nat := 432030641477806599055583

theorem tailTrace_1262065 : CollatzResearch.WordTrace tailWord_1262065 prefixEnd_1262065 432030641477806599055583 := by
  unfold tailWord_1262065
  simp only [CollatzResearch.WordTrace]
  refine ⟨46031292172761523386811649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30687528115174348924541099 46031292172761523386811649)
  ·
    refine ⟨34523469129571142540108737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46031292172761523386811649 34523469129571142540108737)
    ·
      refine ⟨25892601847178356905081553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34523469129571142540108737 25892601847178356905081553)
      ·
        refine ⟨19419451385383767678811165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25892601847178356905081553 19419451385383767678811165)
        ·
          refine ⟨7282294269518912879554187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19419451385383767678811165 7282294269518912879554187)
          ·
            refine ⟨10923441404278369319331281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282294269518912879554187 10923441404278369319331281)
            ·
              refine ⟨8192581053208776989498461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10923441404278369319331281 8192581053208776989498461)
              ·
                refine ⟨3072217894953291371061923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8192581053208776989498461 3072217894953291371061923)
                ·
                  refine ⟨4608326842429937056592885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072217894953291371061923 4608326842429937056592885)
                  ·
                    refine ⟨432030641477806599055583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4608326842429937056592885 432030641477806599055583)
                    ·
                      rfl

theorem cell22_1262065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_1262065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262065 prefixEnd_1262065 := by exact prefixLift 1262065
  have htrace : WordTrace (prefixWord ++ tailWord_1262065) baseStart_1262065 baseEnd_1262065 := by
    simpa [prefixWord, tailWord_1262065, baseEnd_1262065] using wordTrace_append hprefix tailTrace_1262065
  have hstable : (prefixWord ++ tailWord_1262065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262065).length < 2 ^ (prefixWord ++ tailWord_1262065).sum := by decide
  have hdescent : baseEnd_1262065 < baseStart_1262065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262069 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1262069 : Nat := 118140960795 + 1262069 * 2 ^ 59
def prefixEnd_1262069 : Nat := 4983230072969 + 3 ^ 40 * 1262069 * 2
def baseEnd_1262069 : Nat := 432032010759551921955571

theorem tailTrace_1262069 : CollatzResearch.WordTrace tailWord_1262069 prefixEnd_1262069 432032010759551921955571 := by
  unfold tailWord_1262069
  simp only [CollatzResearch.WordTrace]
  refine ⟨46031438064747032069957261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30687625376498021379971507 46031438064747032069957261)
  ·
    refine ⟨17261789274280137026233973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46031438064747032069957261 17261789274280137026233973)
    ·
      refine ⟨1618292744463762846209435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17261789274280137026233973 1618292744463762846209435)
      ·
        refine ⟨2427439116695644269314153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618292744463762846209435 2427439116695644269314153)
        ·
          refine ⟨1820579337521733201985615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2427439116695644269314153 1820579337521733201985615)
          ·
            refine ⟨2730869006282599802978423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820579337521733201985615 2730869006282599802978423)
            ·
              refine ⟨4096303509423899704467635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730869006282599802978423 4096303509423899704467635)
              ·
                refine ⟨6144455264135849556701453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096303509423899704467635 6144455264135849556701453)
                ·
                  refine ⟨2304170724050943583763045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6144455264135849556701453 2304170724050943583763045)
                  ·
                    refine ⟨432032010759551921955571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304170724050943583763045 432032010759551921955571)
                    ·
                      rfl

theorem cell22_1262069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1262069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262069 prefixEnd_1262069 := by exact prefixLift 1262069
  have htrace : WordTrace (prefixWord ++ tailWord_1262069) baseStart_1262069 baseEnd_1262069 := by
    simpa [prefixWord, tailWord_1262069, baseEnd_1262069] using wordTrace_append hprefix tailTrace_1262069
  have hstable : (prefixWord ++ tailWord_1262069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262069).length < 2 ^ (prefixWord ++ tailWord_1262069).sum := by decide
  have hdescent : baseEnd_1262069 < baseStart_1262069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262144 : List Nat := [2, 1, 1, 2, 2, 2, 3, 5, 1, 3]
def baseStart_1262144 : Nat := 118140960795 + 1262144 * 2 ^ 59
def prefixEnd_1262144 : Nat := 4983230072969 + 3 ^ 40 * 1262144 * 2
def baseEnd_1262144 : Nat := 432057684792276726330341

theorem tailTrace_1262144 : CollatzResearch.WordTrace tailWord_1262144 prefixEnd_1262144 432057684792276726330341 := by
  unfold tailWord_1262144
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017086769737659939468743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30689449026316879919291657 23017086769737659939468743)
  ·
    refine ⟨34525630154606489909203115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23017086769737659939468743 34525630154606489909203115)
    ·
      refine ⟨51788445231909734863804673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34525630154606489909203115 51788445231909734863804673)
      ·
        refine ⟨38841333923932301147853505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51788445231909734863804673 38841333923932301147853505)
        ·
          refine ⟨29131000442949225860890129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38841333923932301147853505 29131000442949225860890129)
          ·
            refine ⟨21848250332211919395667597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29131000442949225860890129 21848250332211919395667597)
            ·
              refine ⟨8193093874579469773375349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21848250332211919395667597 8193093874579469773375349)
              ·
                refine ⟨768102550741825291253939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8193093874579469773375349 768102550741825291253939)
                ·
                  refine ⟨1152153826112737936880909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768102550741825291253939 1152153826112737936880909)
                  ·
                    refine ⟨432057684792276726330341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1152153826112737936880909 432057684792276726330341)
                    ·
                      rfl

theorem cell22_1262144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 3].length) (baseStart_1262144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262144 prefixEnd_1262144 := by exact prefixLift 1262144
  have htrace : WordTrace (prefixWord ++ tailWord_1262144) baseStart_1262144 baseEnd_1262144 := by
    simpa [prefixWord, tailWord_1262144, baseEnd_1262144] using wordTrace_append hprefix tailTrace_1262144
  have hstable : (prefixWord ++ tailWord_1262144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262144).length < 2 ^ (prefixWord ++ tailWord_1262144).sum := by decide
  have hdescent : baseEnd_1262144 < baseStart_1262144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262155 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 2, 5]
def baseStart_1262155 : Nat := 118140960795 + 1262155 * 2 ^ 59
def prefixEnd_1262155 : Nat := 4983230072969 + 3 ^ 40 * 1262155 * 2
def baseEnd_1262155 : Nat := 432061450317076364305307

theorem tailTrace_1262155 : CollatzResearch.WordTrace tailWord_1262155 prefixEnd_1262155 432061450317076364305307 := by
  unfold tailWord_1262155
  simp only [CollatzResearch.WordTrace]
  refine ⟨46034574742435468757587919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30689716494956979171725279 46034574742435468757587919)
  ·
    refine ⟨69051862113653203136381879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46034574742435468757587919 69051862113653203136381879)
    ·
      refine ⟨103577793170479804704572819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69051862113653203136381879 103577793170479804704572819)
      ·
        refine ⟨155366689755719707056859229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103577793170479804704572819 155366689755719707056859229)
        ·
          refine ⟨58262508658394890146322211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155366689755719707056859229 58262508658394890146322211)
          ·
            refine ⟨87393762987592335219483317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58262508658394890146322211 87393762987592335219483317)
            ·
              refine ⟨8193165280086781426826561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87393762987592335219483317 8193165280086781426826561)
              ·
                refine ⟨6144873960065086070119921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8193165280086781426826561 6144873960065086070119921)
                ·
                  refine ⟨4608655470048814552589941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6144873960065086070119921 4608655470048814552589941)
                  ·
                    refine ⟨432061450317076364305307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4608655470048814552589941 432061450317076364305307)
                    ·
                      rfl

theorem cell22_1262155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_1262155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262155 prefixEnd_1262155 := by exact prefixLift 1262155
  have htrace : WordTrace (prefixWord ++ tailWord_1262155) baseStart_1262155 baseEnd_1262155 := by
    simpa [prefixWord, tailWord_1262155, baseEnd_1262155] using wordTrace_append hprefix tailTrace_1262155
  have hstable : (prefixWord ++ tailWord_1262155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262155).length < 2 ^ (prefixWord ++ tailWord_1262155).sum := by decide
  have hdescent : baseEnd_1262155 < baseStart_1262155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262232 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1262232 : Nat := 118140960795 + 1262232 * 2 ^ 59
def prefixEnd_1262232 : Nat := 4983230072969 + 3 ^ 40 * 1262232 * 2
def baseEnd_1262232 : Nat := 432087808990673830130071

theorem tailTrace_1262232 : CollatzResearch.WordTrace tailWord_1262232 prefixEnd_1262232 432087808990673830130071 := by
  unfold tailWord_1262232
  simp only [CollatzResearch.WordTrace]
  refine ⟨23018691581578255454070475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30691588775437673938760633 23018691581578255454070475)
  ·
    refine ⟨34528037372367383181105713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23018691581578255454070475 34528037372367383181105713)
    ·
      refine ⟨25896028029275537385829285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34528037372367383181105713 25896028029275537385829285)
      ·
        refine ⟨4855505255489163259842991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25896028029275537385829285 4855505255489163259842991)
        ·
          refine ⟨7283257883233744889764487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855505255489163259842991 7283257883233744889764487)
          ·
            refine ⟨10924886824850617334646731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283257883233744889764487 10924886824850617334646731)
            ·
              refine ⟨16387330237275926001970097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10924886824850617334646731 16387330237275926001970097)
              ·
                refine ⟨12290497677956944501477573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16387330237275926001970097 12290497677956944501477573)
                ·
                  refine ⟨2304468314616927094027045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12290497677956944501477573 2304468314616927094027045)
                  ·
                    refine ⟨432087808990673830130071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304468314616927094027045 432087808990673830130071)
                    ·
                      rfl

theorem cell22_1262232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1262232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262232 prefixEnd_1262232 := by exact prefixLift 1262232
  have htrace : WordTrace (prefixWord ++ tailWord_1262232) baseStart_1262232 baseEnd_1262232 := by
    simpa [prefixWord, tailWord_1262232, baseEnd_1262232] using wordTrace_append hprefix tailTrace_1262232
  have hstable : (prefixWord ++ tailWord_1262232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262232).length < 2 ^ (prefixWord ++ tailWord_1262232).sum := by decide
  have hdescent : baseEnd_1262232 < baseStart_1262232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262369 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 6, 3]
def baseStart_1262369 : Nat := 118140960795 + 1262369 * 2 ^ 59
def prefixEnd_1262369 : Nat := 4983230072969 + 3 ^ 40 * 1262369 * 2
def baseEnd_1262369 : Nat := 432134706890451139454651

theorem tailTrace_1262369 : CollatzResearch.WordTrace tailWord_1262369 prefixEnd_1262369 432134706890451139454651 := by
  unfold tailWord_1262369
  simp only [CollatzResearch.WordTrace]
  refine ⟨46042379963660183305878161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30694919975773455537252107 46042379963660183305878161)
  ·
    refine ⟨34531784972745137479408621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46042379963660183305878161 34531784972745137479408621)
    ·
      refine ⟨12949419364779426554778233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34531784972745137479408621 12949419364779426554778233)
      ·
        refine ⟨9712064523584569916083675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12949419364779426554778233 9712064523584569916083675)
        ·
          refine ⟨14568096785376854874125513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9712064523584569916083675 14568096785376854874125513)
          ·
            refine ⟨10926072589032641155594135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14568096785376854874125513 10926072589032641155594135)
            ·
              refine ⟨16389108883548961733391203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10926072589032641155594135 16389108883548961733391203)
              ·
                refine ⟨24583663325323442600086805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16389108883548961733391203 24583663325323442600086805)
                ·
                  refine ⟨1152359218374536371879069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24583663325323442600086805 1152359218374536371879069)
                  ·
                    refine ⟨432134706890451139454651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1152359218374536371879069 432134706890451139454651)
                    ·
                      rfl

theorem cell22_1262369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_1262369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262369 prefixEnd_1262369 := by exact prefixLift 1262369
  have htrace : WordTrace (prefixWord ++ tailWord_1262369) baseStart_1262369 baseEnd_1262369 := by
    simpa [prefixWord, tailWord_1262369, baseEnd_1262369] using wordTrace_append hprefix tailTrace_1262369
  have hstable : (prefixWord ++ tailWord_1262369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262369).length < 2 ^ (prefixWord ++ tailWord_1262369).sum := by decide
  have hdescent : baseEnd_1262369 < baseStart_1262369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262386 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_1262386 : Nat := 118140960795 + 1262386 * 2 ^ 59
def prefixEnd_1262386 : Nat := 4983230072969 + 3 ^ 40 * 1262386 * 2
def baseEnd_1262386 : Nat := 432140526337868761779599

theorem tailTrace_1262386 : CollatzResearch.WordTrace tailWord_1262386 prefixEnd_1262386 432140526337868761779599 := by
  unfold tailWord_1262386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11510750001149648802311753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30695333336399063472831341 11510750001149648802311753)
  ·
    refine ⟨8633062500862236601733815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11510750001149648802311753 8633062500862236601733815)
    ·
      refine ⟨12949593751293354902600723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8633062500862236601733815 12949593751293354902600723)
      ·
        refine ⟨19424390626940032353901085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12949593751293354902600723 19424390626940032353901085)
        ·
          refine ⟨7284146485102512132712907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19424390626940032353901085 7284146485102512132712907)
          ·
            refine ⟨10926219727653768199069361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7284146485102512132712907 10926219727653768199069361)
            ·
              refine ⟨8194664795740326149302021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10926219727653768199069361 8194664795740326149302021)
              ·
                refine ⟨1536499649201311152994129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8194664795740326149302021 1536499649201311152994129)
                ·
                  refine ⟨1152374736900983364745597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1536499649201311152994129 1152374736900983364745597)
                  ·
                    refine ⟨432140526337868761779599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1152374736900983364745597 432140526337868761779599)
                    ·
                      rfl

theorem cell22_1262386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_1262386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262386 prefixEnd_1262386 := by exact prefixLift 1262386
  have htrace : WordTrace (prefixWord ++ tailWord_1262386) baseStart_1262386 baseEnd_1262386 := by
    simpa [prefixWord, tailWord_1262386, baseEnd_1262386] using wordTrace_append hprefix tailTrace_1262386
  have hstable : (prefixWord ++ tailWord_1262386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262386).length < 2 ^ (prefixWord ++ tailWord_1262386).sum := by decide
  have hdescent : baseEnd_1262386 < baseStart_1262386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262388 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1262388 : Nat := 118140960795 + 1262388 * 2 ^ 59
def prefixEnd_1262388 : Nat := 4983230072969 + 3 ^ 40 * 1262388 * 2
def baseEnd_1262388 : Nat := 144047070326247141076531

theorem tailTrace_1262388 : CollatzResearch.WordTrace tailWord_1262388 prefixEnd_1262388 144047070326247141076531 := by
  unfold tailWord_1262388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23021536475295674775409909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30695381967060899700546545 23021536475295674775409909)
  ·
    refine ⟨2158269044558969510194679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23021536475295674775409909 2158269044558969510194679)
    ·
      refine ⟨3237403566838454265292019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2158269044558969510194679 3237403566838454265292019)
      ·
        refine ⟨4856105350257681397938029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3237403566838454265292019 4856105350257681397938029)
        ·
          refine ⟨1821039506346630524226761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4856105350257681397938029 1821039506346630524226761)
          ·
            refine ⟨1365779629759972893170071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1821039506346630524226761 1365779629759972893170071)
            ·
              refine ⟨2048669444639959339755107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365779629759972893170071 2048669444639959339755107)
              ·
                refine ⟨3073004166959939009632661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048669444639959339755107 3073004166959939009632661)
                ·
                  refine ⟨144047070326247141076531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3073004166959939009632661 144047070326247141076531)
                  ·
                    rfl

theorem cell22_1262388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1262388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262388 prefixEnd_1262388 := by exact prefixLift 1262388
  have htrace : WordTrace (prefixWord ++ tailWord_1262388) baseStart_1262388 baseEnd_1262388 := by
    simpa [prefixWord, tailWord_1262388, baseEnd_1262388] using wordTrace_append hprefix tailTrace_1262388
  have hstable : (prefixWord ++ tailWord_1262388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262388).length < 2 ^ (prefixWord ++ tailWord_1262388).sum := by decide
  have hdescent : baseEnd_1262388 < baseStart_1262388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262399 : List Nat := [1, 1, 2, 2, 5, 2, 2, 7]
def baseStart_1262399 : Nat := 118140960795 + 1262399 * 2 ^ 59
def prefixEnd_1262399 : Nat := 4983230072969 + 3 ^ 40 * 1262399 * 2
def baseEnd_1262399 : Nat := 48016108500393451244951

theorem tailTrace_1262399 : CollatzResearch.WordTrace tailWord_1262399 prefixEnd_1262399 48016108500393451244951 := by
  unfold tailWord_1262399
  simp only [CollatzResearch.WordTrace]
  refine ⟨46043474153551498429470251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30695649435700998952980167 46043474153551498429470251)
  ·
    refine ⟨69065211230327247644205377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46043474153551498429470251 69065211230327247644205377)
    ·
      refine ⟨51798908422745435733154033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69065211230327247644205377 51798908422745435733154033)
      ·
        refine ⟨38849181317059076799865525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51798908422745435733154033 38849181317059076799865525)
        ·
          refine ⟨3642110748474288449987393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38849181317059076799865525 3642110748474288449987393)
          ·
            refine ⟨2731583061355716337490545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3642110748474288449987393 2731583061355716337490545)
            ·
              refine ⟨2048687296016787253117909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731583061355716337490545 2048687296016787253117909)
              ·
                refine ⟨48016108500393451244951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2048687296016787253117909 48016108500393451244951)
                ·
                  rfl

theorem cell22_1262399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 7].length) (baseStart_1262399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262399 prefixEnd_1262399 := by exact prefixLift 1262399
  have htrace : WordTrace (prefixWord ++ tailWord_1262399) baseStart_1262399 baseEnd_1262399 := by
    simpa [prefixWord, tailWord_1262399, baseEnd_1262399] using wordTrace_append hprefix tailTrace_1262399
  have hstable : (prefixWord ++ tailWord_1262399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262399).length < 2 ^ (prefixWord ++ tailWord_1262399).sum := by decide
  have hdescent : baseEnd_1262399 < baseStart_1262399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262482 : List Nat := [3, 2, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1262482 : Nat := 118140960795 + 1262482 * 2 ^ 59
def prefixEnd_1262482 : Nat := 4983230072969 + 3 ^ 40 * 1262482 * 2
def baseEnd_1262482 : Nat := 432173389099756511379305

theorem tailTrace_1262482 : CollatzResearch.WordTrace tailWord_1262482 prefixEnd_1262482 432173389099756511379305 := by
  unfold tailWord_1262482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11511625353062700901185425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30697667608167202403161133 11511625353062700901185425)
  ·
    refine ⟨8633719014797025675889069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11511625353062700901185425 8633719014797025675889069)
    ·
      refine ⟨3237644630548884628458401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8633719014797025675889069 3237644630548884628458401)
      ·
        refine ⟨2428233472911663471343801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3237644630548884628458401 2428233472911663471343801)
        ·
          refine ⟨1821175104683747603507851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2428233472911663471343801 1821175104683747603507851)
          ·
            refine ⟨2731762657025621405261777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821175104683747603507851 2731762657025621405261777)
            ·
              refine ⟨2048821992769216053946333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731762657025621405261777 2048821992769216053946333)
              ·
                refine ⟨768308247288456020229875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2048821992769216053946333 768308247288456020229875)
                ·
                  refine ⟨1152462370932684030344813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768308247288456020229875 1152462370932684030344813)
                  ·
                    refine ⟨432173389099756511379305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1152462370932684030344813 432173389099756511379305)
                    ·
                      rfl

theorem cell22_1262482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1262482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262482 prefixEnd_1262482 := by exact prefixLift 1262482
  have htrace : WordTrace (prefixWord ++ tailWord_1262482) baseStart_1262482 baseEnd_1262482 := by
    simpa [prefixWord, tailWord_1262482, baseEnd_1262482] using wordTrace_append hprefix tailTrace_1262482
  have hstable : (prefixWord ++ tailWord_1262482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262482).length < 2 ^ (prefixWord ++ tailWord_1262482).sum := by decide
  have hdescent : baseEnd_1262482 < baseStart_1262482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262519 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 1, 6]
def baseStart_1262519 : Nat := 118140960795 + 1262519 * 2 ^ 59
def prefixEnd_1262519 : Nat := 4983230072969 + 3 ^ 40 * 1262519 * 2
def baseEnd_1262519 : Nat := 432186054955900748204191

theorem tailTrace_1262519 : CollatzResearch.WordTrace tailWord_1262519 prefixEnd_1262519 432186054955900748204191 := by
  unfold tailWord_1262519
  simp only [CollatzResearch.WordTrace]
  refine ⟨46047850913116758923838611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30698567275411172615892407 46047850913116758923838611)
  ·
    refine ⟨69071776369675138385757917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46047850913116758923838611 69071776369675138385757917)
    ·
      refine ⟨25901916138628176894659219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69071776369675138385757917 25901916138628176894659219)
      ·
        refine ⟨38852874207942265341988829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25901916138628176894659219 38852874207942265341988829)
        ·
          refine ⟨14569827827978349503245811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38852874207942265341988829 14569827827978349503245811)
          ·
            refine ⟨21854741741967524254868717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14569827827978349503245811 21854741741967524254868717)
            ·
              refine ⟨8195528153237821595575769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21854741741967524254868717 8195528153237821595575769)
              ·
                refine ⟨6146646114928366196681827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8195528153237821595575769 6146646114928366196681827)
                ·
                  refine ⟨9219969172392549295022741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6146646114928366196681827 9219969172392549295022741)
                  ·
                    refine ⟨432186054955900748204191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9219969172392549295022741 432186054955900748204191)
                    ·
                      rfl

theorem cell22_1262519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_1262519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262519 prefixEnd_1262519 := by exact prefixLift 1262519
  have htrace : WordTrace (prefixWord ++ tailWord_1262519) baseStart_1262519 baseEnd_1262519 := by
    simpa [prefixWord, tailWord_1262519, baseEnd_1262519] using wordTrace_append hprefix tailTrace_1262519
  have hstable : (prefixWord ++ tailWord_1262519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262519).length < 2 ^ (prefixWord ++ tailWord_1262519).sum := by decide
  have hdescent : baseEnd_1262519 < baseStart_1262519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262521 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_1262521 : Nat := 118140960795 + 1262521 * 2 ^ 59
def prefixEnd_1262521 : Nat := 4983230072969 + 3 ^ 40 * 1262521 * 2
def baseEnd_1262521 : Nat := 432186739596773409654185

theorem tailTrace_1262521 : CollatzResearch.WordTrace tailWord_1262521 prefixEnd_1262521 432186739596773409654185 := by
  unfold tailWord_1262521
  simp only [CollatzResearch.WordTrace]
  refine ⟨46047923859109513265411417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30698615906073008843607611 46047923859109513265411417)
  ·
    refine ⟨34535942894332134949058563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46047923859109513265411417 34535942894332134949058563)
    ·
      refine ⟨51803914341498202423587845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34535942894332134949058563 51803914341498202423587845)
      ·
        refine ⟨9713233939030912954422721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51803914341498202423587845 9713233939030912954422721)
        ·
          refine ⟨7284925454273184715817041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713233939030912954422721 7284925454273184715817041)
          ·
            refine ⟨5463694090704888536862781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7284925454273184715817041 5463694090704888536862781)
            ·
              refine ⟨2048885284014333201323543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5463694090704888536862781 2048885284014333201323543)
              ·
                refine ⟨3073327926021499801985315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048885284014333201323543 3073327926021499801985315)
                ·
                  refine ⟨4609991889032249702977973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073327926021499801985315 4609991889032249702977973)
                  ·
                    refine ⟨432186739596773409654185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4609991889032249702977973 432186739596773409654185)
                    ·
                      rfl

theorem cell22_1262521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_1262521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262521 prefixEnd_1262521 := by exact prefixLift 1262521
  have htrace : WordTrace (prefixWord ++ tailWord_1262521) baseStart_1262521 baseEnd_1262521 := by
    simpa [prefixWord, tailWord_1262521, baseEnd_1262521] using wordTrace_append hprefix tailTrace_1262521
  have hstable : (prefixWord ++ tailWord_1262521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262521).length < 2 ^ (prefixWord ++ tailWord_1262521).sum := by decide
  have hdescent : baseEnd_1262521 < baseStart_1262521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262613 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 5]
def baseStart_1262613 : Nat := 118140960795 + 1262613 * 2 ^ 59
def prefixEnd_1262613 : Nat := 4983230072969 + 3 ^ 40 * 1262613 * 2
def baseEnd_1262613 : Nat := 144072744358971945451301

theorem tailTrace_1262613 : CollatzResearch.WordTrace tailWord_1262613 prefixEnd_1262613 144072744358971945451301 := by
  unfold tailWord_1262613
  simp only [CollatzResearch.WordTrace]
  refine ⟨46051279374776212977760493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30700852916517475318506995 46051279374776212977760493)
  ·
    refine ⟨17269229765541079866660185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46051279374776212977760493 17269229765541079866660185)
    ·
      refine ⟨12951922324155809899995139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17269229765541079866660185 12951922324155809899995139)
      ·
        refine ⟨19427883486233714849992709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12951922324155809899995139 19427883486233714849992709)
        ·
          refine ⟨3642728153668821534373633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19427883486233714849992709 3642728153668821534373633)
          ·
            refine ⟨2732046115251616150780225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3642728153668821534373633 2732046115251616150780225)
            ·
              refine ⟨2049034586438712113085169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2732046115251616150780225 2049034586438712113085169)
              ·
                refine ⟨1536775939829034084813877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2049034586438712113085169 1536775939829034084813877)
                ·
                  refine ⟨144072744358971945451301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1536775939829034084813877 144072744358971945451301)
                  ·
                    rfl

theorem cell22_1262613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_1262613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262613 prefixEnd_1262613 := by exact prefixLift 1262613
  have htrace : WordTrace (prefixWord ++ tailWord_1262613) baseStart_1262613 baseEnd_1262613 := by
    simpa [prefixWord, tailWord_1262613, baseEnd_1262613] using wordTrace_append hprefix tailTrace_1262613
  have hstable : (prefixWord ++ tailWord_1262613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262613).length < 2 ^ (prefixWord ++ tailWord_1262613).sum := by decide
  have hdescent : baseEnd_1262613 < baseStart_1262613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262628 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1262628 : Nat := 118140960795 + 1262628 * 2 ^ 59
def prefixEnd_1262628 : Nat := 4983230072969 + 3 ^ 40 * 1262628 * 2
def baseEnd_1262628 : Nat := 432223367883460797228857

theorem tailTrace_1262628 : CollatzResearch.WordTrace tailWord_1262628 prefixEnd_1262628 432223367883460797228857 := by
  unfold tailWord_1262628
  simp only [CollatzResearch.WordTrace]
  refine ⟨23025913234860935269778269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30701217646481247026371025 23025913234860935269778269)
  ·
    refine ⟨8634717463072850726166851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23025913234860935269778269 8634717463072850726166851)
    ·
      refine ⟨12952076194609276089250277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8634717463072850726166851 12952076194609276089250277)
      ·
        refine ⟨2428514286489239266734427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12952076194609276089250277 2428514286489239266734427)
        ·
          refine ⟨3642771429733858900101641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428514286489239266734427 3642771429733858900101641)
          ·
            refine ⟨2732078572300394175076231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3642771429733858900101641 2732078572300394175076231)
            ·
              refine ⟨4098117858450591262614347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732078572300394175076231 4098117858450591262614347)
              ·
                refine ⟨6147176787675886893921521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098117858450591262614347 6147176787675886893921521)
                ·
                  refine ⟨4610382590756915170441141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6147176787675886893921521 4610382590756915170441141)
                  ·
                    refine ⟨432223367883460797228857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4610382590756915170441141 432223367883460797228857)
                    ·
                      rfl

theorem cell22_1262628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1262628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262628 prefixEnd_1262628 := by exact prefixLift 1262628
  have htrace : WordTrace (prefixWord ++ tailWord_1262628) baseStart_1262628 baseEnd_1262628 := by
    simpa [prefixWord, tailWord_1262628, baseEnd_1262628] using wordTrace_append hprefix tailTrace_1262628
  have hstable : (prefixWord ++ tailWord_1262628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262628).length < 2 ^ (prefixWord ++ tailWord_1262628).sum := by decide
  have hdescent : baseEnd_1262628 < baseStart_1262628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262641 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 6]
def baseStart_1262641 : Nat := 118140960795 + 1262641 * 2 ^ 59
def prefixEnd_1262641 : Nat := 4983230072969 + 3 ^ 40 * 1262641 * 2
def baseEnd_1262641 : Nat := 144075939349711032217939

theorem tailTrace_1262641 : CollatzResearch.WordTrace tailWord_1262641 prefixEnd_1262641 144075939349711032217939 := by
  unfold tailWord_1262641
  simp only [CollatzResearch.WordTrace]
  refine ⟨46052300618674773759779777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30701533745783182506519851 46052300618674773759779777)
  ·
    refine ⟨34539225464006080319834833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46052300618674773759779777 34539225464006080319834833)
    ·
      refine ⟨25904419098004560239876125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34539225464006080319834833 25904419098004560239876125)
      ·
        refine ⟨9714157161751710089953547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25904419098004560239876125 9714157161751710089953547)
        ·
          refine ⟨14571235742627565134930321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9714157161751710089953547 14571235742627565134930321)
          ·
            refine ⟨10928426806970673851197741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14571235742627565134930321 10928426806970673851197741)
            ·
              refine ⟨4098160052614002694199153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10928426806970673851197741 4098160052614002694199153)
              ·
                refine ⟨3073620039460502020649365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4098160052614002694199153 3073620039460502020649365)
                ·
                  refine ⟨144075939349711032217939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3073620039460502020649365 144075939349711032217939)
                  ·
                    rfl

theorem cell22_1262641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_1262641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262641 prefixEnd_1262641 := by exact prefixLift 1262641
  have htrace : WordTrace (prefixWord ++ tailWord_1262641) baseStart_1262641 baseEnd_1262641 := by
    simpa [prefixWord, tailWord_1262641, baseEnd_1262641] using wordTrace_append hprefix tailTrace_1262641
  have hstable : (prefixWord ++ tailWord_1262641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262641).length < 2 ^ (prefixWord ++ tailWord_1262641).sum := by decide
  have hdescent : baseEnd_1262641 < baseStart_1262641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262656 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_1262656 : Nat := 118140960795 + 1262656 * 2 ^ 59
def prefixEnd_1262656 : Nat := 4983230072969 + 3 ^ 40 * 1262656 * 2
def baseEnd_1262656 : Nat := 432232952855678057528771

theorem tailTrace_1262656 : CollatzResearch.WordTrace tailWord_1262656 prefixEnd_1262656 432232952855678057528771 := by
  unfold tailWord_1262656
  simp only [CollatzResearch.WordTrace]
  refine ⟨23026423856810215660787911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30701898475746954214383881 23026423856810215660787911)
  ·
    refine ⟨34539635785215323491181867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23026423856810215660787911 34539635785215323491181867)
    ·
      refine ⟨51809453677822985236772801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34539635785215323491181867 51809453677822985236772801)
      ·
        refine ⟨38857090258367238927579601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51809453677822985236772801 38857090258367238927579601)
        ·
          refine ⟨29142817693775429195684701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38857090258367238927579601 29142817693775429195684701)
          ·
            refine ⟨10928556635165785948381763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29142817693775429195684701 10928556635165785948381763)
            ·
              refine ⟨16392834952748678922572645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10928556635165785948381763 16392834952748678922572645)
              ·
                refine ⟨3073656553640377297982371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16392834952748678922572645 3073656553640377297982371)
                ·
                  refine ⟨4610484830460565946973557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073656553640377297982371 4610484830460565946973557)
                  ·
                    refine ⟨432232952855678057528771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4610484830460565946973557 432232952855678057528771)
                    ·
                      rfl

theorem cell22_1262656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_1262656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262656 prefixEnd_1262656 := by exact prefixLift 1262656
  have htrace : WordTrace (prefixWord ++ tailWord_1262656) baseStart_1262656 baseEnd_1262656 := by
    simpa [prefixWord, tailWord_1262656, baseEnd_1262656] using wordTrace_append hprefix tailTrace_1262656
  have hstable : (prefixWord ++ tailWord_1262656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262656).length < 2 ^ (prefixWord ++ tailWord_1262656).sum := by decide
  have hdescent : baseEnd_1262656 < baseStart_1262656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262690 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1262690 : Nat := 118140960795 + 1262690 * 2 ^ 59
def prefixEnd_1262690 : Nat := 4983230072969 + 3 ^ 40 * 1262690 * 2
def baseEnd_1262690 : Nat := 432244591750513302178667

theorem tailTrace_1262690 : CollatzResearch.WordTrace tailWord_1262690 prefixEnd_1262690 432244591750513302178667 := by
  unfold tailWord_1262690
  simp only [CollatzResearch.WordTrace]
  refine ⟨11513521948874313782078381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30702725196998170085542349 11513521948874313782078381)
  ·
    refine ⟨4317570730827867668279393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11513521948874313782078381 4317570730827867668279393)
    ·
      refine ⟨3238178048120900751209545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4317570730827867668279393 3238178048120900751209545)
      ·
        refine ⟨2428633536090675563407159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3238178048120900751209545 2428633536090675563407159)
        ·
          refine ⟨3642950304136013345110739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428633536090675563407159 3642950304136013345110739)
          ·
            refine ⟨5464425456204020017666109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642950304136013345110739 5464425456204020017666109)
            ·
              refine ⟨2049159546076507506624791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5464425456204020017666109 2049159546076507506624791)
              ·
                refine ⟨3073739319114761259937187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049159546076507506624791 3073739319114761259937187)
                ·
                  refine ⟨4610608978672141889905781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073739319114761259937187 4610608978672141889905781)
                  ·
                    refine ⟨432244591750513302178667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4610608978672141889905781 432244591750513302178667)
                    ·
                      rfl

theorem cell22_1262690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1262690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262690 prefixEnd_1262690 := by exact prefixLift 1262690
  have htrace : WordTrace (prefixWord ++ tailWord_1262690) baseStart_1262690 baseEnd_1262690 := by
    simpa [prefixWord, tailWord_1262690, baseEnd_1262690] using wordTrace_append hprefix tailTrace_1262690
  have hstable : (prefixWord ++ tailWord_1262690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262690).length < 2 ^ (prefixWord ++ tailWord_1262690).sum := by decide
  have hdescent : baseEnd_1262690 < baseStart_1262690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262709 : List Nat := [1, 3, 4, 3, 1, 2, 1, 3, 4]
def baseStart_1262709 : Nat := 118140960795 + 1262709 * 2 ^ 59
def prefixEnd_1262709 : Nat := 4983230072969 + 3 ^ 40 * 1262709 * 2
def baseEnd_1262709 : Nat := 144083698612934528651203

theorem tailTrace_1262709 : CollatzResearch.WordTrace tailWord_1262709 prefixEnd_1262709 144083698612934528651203 := by
  unfold tailWord_1262709
  simp only [CollatzResearch.WordTrace]
  refine ⟨46054780782428421373255181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30703187188285614248836787 46054780782428421373255181)
  ·
    refine ⟨17270542793410658014970693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46054780782428421373255181 17270542793410658014970693)
    ·
      refine ⟨3238226773764498377807005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17270542793410658014970693 3238226773764498377807005)
      ·
        refine ⟨1214335040161686891677627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3238226773764498377807005 1214335040161686891677627)
        ·
          refine ⟨1821502560242530337516441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214335040161686891677627 1821502560242530337516441)
          ·
            refine ⟨1366126920181897753137331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1821502560242530337516441 1366126920181897753137331)
            ·
              refine ⟨2049190380272846629705997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366126920181897753137331 2049190380272846629705997)
              ·
                refine ⟨768446392602317486139749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2049190380272846629705997 768446392602317486139749)
                ·
                  refine ⟨144083698612934528651203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768446392602317486139749 144083698612934528651203)
                  ·
                    rfl

theorem cell22_1262709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_1262709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262709 prefixEnd_1262709 := by exact prefixLift 1262709
  have htrace : WordTrace (prefixWord ++ tailWord_1262709) baseStart_1262709 baseEnd_1262709 := by
    simpa [prefixWord, tailWord_1262709, baseEnd_1262709] using wordTrace_append hprefix tailTrace_1262709
  have hstable : (prefixWord ++ tailWord_1262709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262709).length < 2 ^ (prefixWord ++ tailWord_1262709).sum := by decide
  have hdescent : baseEnd_1262709 < baseStart_1262709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262776 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 10]
def baseStart_1262776 : Nat := 118140960795 + 1262776 * 2 ^ 59
def prefixEnd_1262776 : Nat := 4983230072969 + 3 ^ 40 * 1262776 * 2
def baseEnd_1262776 : Nat := 144091343769345914842801

theorem tailTrace_1262776 : CollatzResearch.WordTrace tailWord_1262776 prefixEnd_1262776 144091343769345914842801 := by
  unfold tailWord_1262776
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028612236592845907972091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30704816315457127877296121 23028612236592845907972091)
  ·
    refine ⟨34542918354889268861958137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23028612236592845907972091 34542918354889268861958137)
    ·
      refine ⟨25907188766166951646468603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34542918354889268861958137 25907188766166951646468603)
      ·
        refine ⟨38860783149250427469702905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25907188766166951646468603 38860783149250427469702905)
        ·
          refine ⟨29145587361937820602277179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38860783149250427469702905 29145587361937820602277179)
          ·
            refine ⟨43718381042906730903415769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29145587361937820602277179 43718381042906730903415769)
            ·
              refine ⟨32788785782180048177561827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43718381042906730903415769 32788785782180048177561827)
              ·
                refine ⟨49183178673270072266342741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32788785782180048177561827 49183178673270072266342741)
                ·
                  refine ⟨144091343769345914842801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49183178673270072266342741 144091343769345914842801)
                  ·
                    rfl

theorem cell22_1262776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_1262776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262776 prefixEnd_1262776 := by exact prefixLift 1262776
  have htrace : WordTrace (prefixWord ++ tailWord_1262776) baseStart_1262776 baseEnd_1262776 := by
    simpa [prefixWord, tailWord_1262776, baseEnd_1262776] using wordTrace_append hprefix tailTrace_1262776
  have hstable : (prefixWord ++ tailWord_1262776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262776).length < 2 ^ (prefixWord ++ tailWord_1262776).sum := by decide
  have hdescent : baseEnd_1262776 < baseStart_1262776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262829 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_1262829 : Nat := 118140960795 + 1262829 * 2 ^ 59
def prefixEnd_1262829 : Nat := 4983230072969 + 3 ^ 40 * 1262829 * 2
def baseEnd_1262829 : Nat := 432292174291163272953241

theorem tailTrace_1262829 : CollatzResearch.WordTrace tailWord_1262829 prefixEnd_1262829 432292174291163272953241 := by
  unfold tailWord_1262829
  simp only [CollatzResearch.WordTrace]
  refine ⟨46059157541993681867623541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30706105027995787911749027 46059157541993681867623541)
  ·
    refine ⟨4318046019561907675089707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46059157541993681867623541 4318046019561907675089707)
    ·
      refine ⟨6477069029342861512634561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4318046019561907675089707 6477069029342861512634561)
      ·
        refine ⟨4857801772007146134475921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6477069029342861512634561 4857801772007146134475921)
        ·
          refine ⟨3643351329005359600856941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4857801772007146134475921 3643351329005359600856941)
          ·
            refine ⟨1366256748377009850321353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3643351329005359600856941 1366256748377009850321353)
            ·
              refine ⟨1024692561282757387741015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366256748377009850321353 1024692561282757387741015)
              ·
                refine ⟨1537038841924136081611523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024692561282757387741015 1537038841924136081611523)
                ·
                  refine ⟨2305558262886204122417285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537038841924136081611523 2305558262886204122417285)
                  ·
                    refine ⟨432292174291163272953241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305558262886204122417285 432292174291163272953241)
                    ·
                      rfl

theorem cell22_1262829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_1262829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262829 prefixEnd_1262829 := by exact prefixLift 1262829
  have htrace : WordTrace (prefixWord ++ tailWord_1262829) baseStart_1262829 baseEnd_1262829 := by
    simpa [prefixWord, tailWord_1262829, baseEnd_1262829] using wordTrace_append hprefix tailTrace_1262829
  have hstable : (prefixWord ++ tailWord_1262829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262829).length < 2 ^ (prefixWord ++ tailWord_1262829).sum := by decide
  have hdescent : baseEnd_1262829 < baseStart_1262829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262878 : List Nat := [4, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1262878 : Nat := 118140960795 + 1262878 * 2 ^ 59
def prefixEnd_1262878 : Nat := 4983230072969 + 3 ^ 40 * 1262878 * 2
def baseEnd_1262878 : Nat := 144102982664181159492697

theorem tailTrace_1262878 : CollatzResearch.WordTrace tailWord_1262878 prefixEnd_1262878 144102982664181159492697 := by
  unfold tailWord_1262878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5757618089852020404519661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30707296479210775490771525 5757618089852020404519661)
  ·
    refine ⟨2159106783694507651694873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5757618089852020404519661 2159106783694507651694873)
    ·
      refine ⟨1619330087770880738771155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2159106783694507651694873 1619330087770880738771155)
      ·
        refine ⟨2428995131656321108156733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619330087770880738771155 2428995131656321108156733)
        ·
          refine ⟨910873174371120415558775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2428995131656321108156733 910873174371120415558775)
          ·
            refine ⟨1366309761556680623338163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910873174371120415558775 1366309761556680623338163)
            ·
              refine ⟨2049464642335020935007245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366309761556680623338163 2049464642335020935007245)
              ·
                refine ⟨768549240875632850627717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2049464642335020935007245 768549240875632850627717)
                ·
                  refine ⟨144102982664181159492697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768549240875632850627717 144102982664181159492697)
                  ·
                    rfl

theorem cell22_1262878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1262878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262878 prefixEnd_1262878 := by exact prefixLift 1262878
  have htrace : WordTrace (prefixWord ++ tailWord_1262878) baseStart_1262878 baseEnd_1262878 := by
    simpa [prefixWord, tailWord_1262878, baseEnd_1262878] using wordTrace_append hprefix tailTrace_1262878
  have hstable : (prefixWord ++ tailWord_1262878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262878).length < 2 ^ (prefixWord ++ tailWord_1262878).sum := by decide
  have hdescent : baseEnd_1262878 < baseStart_1262878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262883 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 7]
def baseStart_1262883 : Nat := 118140960795 + 1262883 * 2 ^ 59
def prefixEnd_1262883 : Nat := 4983230072969 + 3 ^ 40 * 1262883 * 2
def baseEnd_1262883 : Nat := 144103553198241710701025

theorem tailTrace_1262883 : CollatzResearch.WordTrace tailWord_1262883 prefixEnd_1262883 144103553198241710701025 := by
  unfold tailWord_1262883
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061127083798049090089303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30707418055865366060059535 46061127083798049090089303)
  ·
    refine ⟨69091690625697073635133955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46061127083798049090089303 69091690625697073635133955)
    ·
      refine ⟨103637535938545610452700933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69091690625697073635133955 103637535938545610452700933)
      ·
        refine ⟨19432037988477301959881425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103637535938545610452700933 19432037988477301959881425)
        ·
          refine ⟨14574028491357976469911069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19432037988477301959881425 14574028491357976469911069)
          ·
            refine ⟨5465260684259241176216651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14574028491357976469911069 5465260684259241176216651)
            ·
              refine ⟨8197891026388861764324977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465260684259241176216651 8197891026388861764324977)
              ·
                refine ⟨6148418269791646323243733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8197891026388861764324977 6148418269791646323243733)
                ·
                  refine ⟨144103553198241710701025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6148418269791646323243733 144103553198241710701025)
                  ·
                    rfl

theorem cell22_1262883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_1262883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262883 prefixEnd_1262883 := by exact prefixLift 1262883
  have htrace : WordTrace (prefixWord ++ tailWord_1262883) baseStart_1262883 baseEnd_1262883 := by
    simpa [prefixWord, tailWord_1262883, baseEnd_1262883] using wordTrace_append hprefix tailTrace_1262883
  have hstable : (prefixWord ++ tailWord_1262883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262883).length < 2 ^ (prefixWord ++ tailWord_1262883).sum := by decide
  have hdescent : baseEnd_1262883 < baseStart_1262883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262900 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1262900 : Nat := 118140960795 + 1262900 * 2 ^ 59
def prefixEnd_1262900 : Nat := 4983230072969 + 3 ^ 40 * 1262900 * 2
def baseEnd_1262900 : Nat := 144105493014047584809341

theorem tailTrace_1262900 : CollatzResearch.WordTrace tailWord_1262900 prefixEnd_1262900 144105493014047584809341 := by
  unfold tailWord_1262900
  simp only [CollatzResearch.WordTrace]
  refine ⟨23030873562368230496729077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30707831416490973995638769 23030873562368230496729077)
  ·
    refine ⟨2159144396472021609068351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23030873562368230496729077 2159144396472021609068351)
    ·
      refine ⟨3238716594708032413602527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2159144396472021609068351 3238716594708032413602527)
      ·
        refine ⟨4858074892062048620403791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238716594708032413602527 4858074892062048620403791)
        ·
          refine ⟨7287112338093072930605687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4858074892062048620403791 7287112338093072930605687)
          ·
            refine ⟨10930668507139609395908531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7287112338093072930605687 10930668507139609395908531)
            ·
              refine ⟨16396002760709414093862797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10930668507139609395908531 16396002760709414093862797)
              ·
                refine ⟨6148501035266030285198549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16396002760709414093862797 6148501035266030285198549)
                ·
                  refine ⟨144105493014047584809341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6148501035266030285198549 144105493014047584809341)
                  ·
                    rfl

theorem cell22_1262900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1262900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262900 prefixEnd_1262900 := by exact prefixLift 1262900
  have htrace : WordTrace (prefixWord ++ tailWord_1262900) baseStart_1262900 baseEnd_1262900 := by
    simpa [prefixWord, tailWord_1262900, baseEnd_1262900] using wordTrace_append hprefix tailTrace_1262900
  have hstable : (prefixWord ++ tailWord_1262900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262900).length < 2 ^ (prefixWord ++ tailWord_1262900).sum := by decide
  have hdescent : baseEnd_1262900 < baseStart_1262900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262928 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 8]
def baseStart_1262928 : Nat := 118140960795 + 1262928 * 2 ^ 59
def prefixEnd_1262928 : Nat := 4983230072969 + 3 ^ 40 * 1262928 * 2
def baseEnd_1262928 : Nat := 144108688004786671575979

theorem tailTrace_1262928 : CollatzResearch.WordTrace tailWord_1262928 prefixEnd_1262928 144108688004786671575979 := by
  unfold tailWord_1262928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23031384184317510887738719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30708512245756681183651625 23031384184317510887738719)
  ·
    refine ⟨34547076276476266331608079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23031384184317510887738719 34547076276476266331608079)
    ·
      refine ⟨51820614414714399497412119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34547076276476266331608079 51820614414714399497412119)
      ·
        refine ⟨77730921622071599246118179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51820614414714399497412119 77730921622071599246118179)
        ·
          refine ⟨116596382433107398869177269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77730921622071599246118179 116596382433107398869177269)
          ·
            refine ⟨10930910853103818643985369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116596382433107398869177269 10930910853103818643985369)
            ·
              refine ⟨8198183139827863982989027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10930910853103818643985369 8198183139827863982989027)
              ·
                refine ⟨12297274709741795974483541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8198183139827863982989027 12297274709741795974483541)
                ·
                  refine ⟨144108688004786671575979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12297274709741795974483541 144108688004786671575979)
                  ·
                    rfl

theorem cell22_1262928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_1262928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262928 prefixEnd_1262928 := by exact prefixLift 1262928
  have htrace : WordTrace (prefixWord ++ tailWord_1262928) baseStart_1262928 baseEnd_1262928 := by
    simpa [prefixWord, tailWord_1262928, baseEnd_1262928] using wordTrace_append hprefix tailTrace_1262928
  have hstable : (prefixWord ++ tailWord_1262928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262928).length < 2 ^ (prefixWord ++ tailWord_1262928).sum := by decide
  have hdescent : baseEnd_1262928 < baseStart_1262928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262962 : List Nat := [3, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_1262962 : Nat := 118140960795 + 1262962 * 2 ^ 59
def prefixEnd_1262962 : Nat := 4983230072969 + 3 ^ 40 * 1262962 * 2
def baseEnd_1262962 : Nat := 144112567636398419792611

theorem tailTrace_1262962 : CollatzResearch.WordTrace tailWord_1262962 prefixEnd_1262962 144112567636398419792611 := by
  unfold tailWord_1262962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11516002112627961395553785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30709338967007897054810093 11516002112627961395553785)
  ·
    refine ⟨8637001584470971046665339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11516002112627961395553785 8637001584470971046665339)
    ·
      refine ⟨12955502376706456569998009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8637001584470971046665339 12955502376706456569998009)
      ·
        refine ⟨9716626782529842427498507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12955502376706456569998009 9716626782529842427498507)
        ·
          refine ⟨14574940173794763641247761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716626782529842427498507 14574940173794763641247761)
          ·
            refine ⟨10931205130346072730935821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14574940173794763641247761 10931205130346072730935821)
            ·
              refine ⟨4099201923879777274100933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10931205130346072730935821 4099201923879777274100933)
              ·
                refine ⟨768600360727458238893925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4099201923879777274100933 768600360727458238893925)
                ·
                  refine ⟨144112567636398419792611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 768600360727458238893925 144112567636398419792611)
                  ·
                    rfl

theorem cell22_1262962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_1262962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1262962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1262962 prefixEnd_1262962 := by exact prefixLift 1262962
  have htrace : WordTrace (prefixWord ++ tailWord_1262962) baseStart_1262962 baseEnd_1262962 := by
    simpa [prefixWord, tailWord_1262962, baseEnd_1262962] using wordTrace_append hprefix tailTrace_1262962
  have hstable : (prefixWord ++ tailWord_1262962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262962).length < 2 ^ (prefixWord ++ tailWord_1262962).sum := by decide
  have hdescent : baseEnd_1262962 < baseStart_1262962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263112 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 6, 3]
def baseStart_1263112 : Nat := 118140960795 + 1263112 * 2 ^ 59
def prefixEnd_1263112 : Nat := 4983230072969 + 3 ^ 40 * 1263112 * 2
def baseEnd_1263112 : Nat := 432389050974644868127373

theorem tailTrace_1263112 : CollatzResearch.WordTrace tailWord_1263112 prefixEnd_1263112 432389050974644868127373 := by
  unfold tailWord_1263112
  simp only [CollatzResearch.WordTrace]
  refine ⟨23034739699984210600087795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30712986266645614133450393 23034739699984210600087795)
  ·
    refine ⟨34552109549976315900131693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23034739699984210600087795 34552109549976315900131693)
    ·
      refine ⟨12957041081241118462549385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34552109549976315900131693 12957041081241118462549385)
      ·
        refine ⟨9717780810930838846912039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12957041081241118462549385 9717780810930838846912039)
        ·
          refine ⟨14576671216396258270368059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9717780810930838846912039 14576671216396258270368059)
          ·
            refine ⟨21865006824594387405552089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14576671216396258270368059 21865006824594387405552089)
            ·
              refine ⟨16398755118445790554164067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21865006824594387405552089 16398755118445790554164067)
              ·
                refine ⟨24598132677668685831246101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16398755118445790554164067 24598132677668685831246101)
                ·
                  refine ⟨1153037469265719648339661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24598132677668685831246101 1153037469265719648339661)
                  ·
                    refine ⟨432389050974644868127373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153037469265719648339661 432389050974644868127373)
                    ·
                      rfl

theorem cell22_1263112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_1263112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263112 prefixEnd_1263112 := by exact prefixLift 1263112
  have htrace : WordTrace (prefixWord ++ tailWord_1263112) baseStart_1263112 baseEnd_1263112 := by
    simpa [prefixWord, tailWord_1263112, baseEnd_1263112] using wordTrace_append hprefix tailTrace_1263112
  have hstable : (prefixWord ++ tailWord_1263112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263112).length < 2 ^ (prefixWord ++ tailWord_1263112).sum := by decide
  have hdescent : baseEnd_1263112 < baseStart_1263112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263116 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_1263116 : Nat := 118140960795 + 1263116 * 2 ^ 59
def prefixEnd_1263116 : Nat := 4983230072969 + 3 ^ 40 * 1263116 * 2
def baseEnd_1263116 : Nat := 432390420256390191027361

theorem tailTrace_1263116 : CollatzResearch.WordTrace tailWord_1263116 prefixEnd_1263116 432390420256390191027361 := by
  unfold tailWord_1263116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23034812645976964941660601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30713083527969286588880801 23034812645976964941660601)
  ·
    refine ⟨17276109484482723706245451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23034812645976964941660601 17276109484482723706245451)
    ·
      refine ⟨25914164226724085559368177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17276109484482723706245451 25914164226724085559368177)
      ·
        refine ⟨19435623170043064169526133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25914164226724085559368177 19435623170043064169526133)
        ·
          refine ⟨1822089672191537265893075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19435623170043064169526133 1822089672191537265893075)
          ·
            refine ⟨2733134508287305898839613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822089672191537265893075 2733134508287305898839613)
            ·
              refine ⟨1024925440607739712064855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2733134508287305898839613 1024925440607739712064855)
              ·
                refine ⟨1537388160911609568097283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024925440607739712064855 1537388160911609568097283)
                ·
                  refine ⟨2306082241367414352145925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537388160911609568097283 2306082241367414352145925)
                  ·
                    refine ⟨432390420256390191027361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306082241367414352145925 432390420256390191027361)
                    ·
                      rfl

theorem cell22_1263116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_1263116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263116 prefixEnd_1263116 := by exact prefixLift 1263116
  have htrace : WordTrace (prefixWord ++ tailWord_1263116) baseStart_1263116 baseEnd_1263116 := by
    simpa [prefixWord, tailWord_1263116, baseEnd_1263116] using wordTrace_append hprefix tailTrace_1263116
  have hstable : (prefixWord ++ tailWord_1263116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263116).length < 2 ^ (prefixWord ++ tailWord_1263116).sum := by decide
  have hdescent : baseEnd_1263116 < baseStart_1263116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263125 : List Nat := [1, 3, 2, 1, 3, 12]
def baseStart_1263125 : Nat := 118140960795 + 1263125 * 2 ^ 59
def prefixEnd_1263125 : Nat := 4983230072969 + 3 ^ 40 * 1263125 * 2
def baseEnd_1263125 : Nat := 5338191372102681080893

theorem tailTrace_1263125 : CollatzResearch.WordTrace tailWord_1263125 prefixEnd_1263125 5338191372102681080893 := by
  unfold tailWord_1263125
  simp only [CollatzResearch.WordTrace]
  refine ⟨46069953548921324420398829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30713302365947549613599219 46069953548921324420398829)
  ·
    refine ⟨17276232580845496657649561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46069953548921324420398829 17276232580845496657649561)
    ·
      refine ⟨12957174435634122493237171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17276232580845496657649561 12957174435634122493237171)
      ·
        refine ⟨19435761653451183739855757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12957174435634122493237171 19435761653451183739855757)
        ·
          refine ⟨7288410620044193902445909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19435761653451183739855757 7288410620044193902445909)
          ·
            refine ⟨5338191372102681080893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7288410620044193902445909 5338191372102681080893)
            ·
              rfl

theorem cell22_1263125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 12].length) (baseStart_1263125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263125 prefixEnd_1263125 := by exact prefixLift 1263125
  have htrace : WordTrace (prefixWord ++ tailWord_1263125) baseStart_1263125 baseEnd_1263125 := by
    simpa [prefixWord, tailWord_1263125, baseEnd_1263125] using wordTrace_append hprefix tailTrace_1263125
  have hstable : (prefixWord ++ tailWord_1263125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263125).length < 2 ^ (prefixWord ++ tailWord_1263125).sum := by decide
  have hdescent : baseEnd_1263125 < baseStart_1263125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263191 : List Nat := [1, 1, 3, 2, 2, 3, 2, 4, 1, 3]
def baseStart_1263191 : Nat := 118140960795 + 1263191 * 2 ^ 59
def prefixEnd_1263191 : Nat := 4983230072969 + 3 ^ 40 * 1263191 * 2
def baseEnd_1263191 : Nat := 432416094289114995402131

theorem tailTrace_1263191 : CollatzResearch.WordTrace tailWord_1263191 prefixEnd_1263191 432416094289114995402131 := by
  unfold tailWord_1263191
  simp only [CollatzResearch.WordTrace]
  refine ⟨46072360766682217692301427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30714907177788145128200951 46072360766682217692301427)
  ·
    refine ⟨69108541150023326538452141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46072360766682217692301427 69108541150023326538452141)
    ·
      refine ⟨25915702931258747451919553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69108541150023326538452141 25915702931258747451919553)
      ·
        refine ⟨19436777198444060588939665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25915702931258747451919553 19436777198444060588939665)
        ·
          refine ⟨14577582898833045441704749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19436777198444060588939665 14577582898833045441704749)
          ·
            refine ⟨5466593587062392040639281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14577582898833045441704749 5466593587062392040639281)
            ·
              refine ⟨4099945190296794030479461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5466593587062392040639281 4099945190296794030479461)
              ·
                refine ⟨768739723180648880714899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4099945190296794030479461 768739723180648880714899)
                ·
                  refine ⟨1153109584770973321072349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768739723180648880714899 1153109584770973321072349)
                  ·
                    refine ⟨432416094289114995402131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153109584770973321072349 432416094289114995402131)
                    ·
                      rfl

theorem cell22_1263191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_1263191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263191 prefixEnd_1263191 := by exact prefixLift 1263191
  have htrace : WordTrace (prefixWord ++ tailWord_1263191) baseStart_1263191 baseEnd_1263191 := by
    simpa [prefixWord, tailWord_1263191, baseEnd_1263191] using wordTrace_append hprefix tailTrace_1263191
  have hstable : (prefixWord ++ tailWord_1263191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263191).length < 2 ^ (prefixWord ++ tailWord_1263191).sum := by decide
  have hdescent : baseEnd_1263191 < baseStart_1263191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263217 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_1263217 : Nat := 118140960795 + 1263217 * 2 ^ 59
def prefixEnd_1263217 : Nat := 4983230072969 + 3 ^ 40 * 1263217 * 2
def baseEnd_1263217 : Nat := 432424994620459594252051

theorem tailTrace_1263217 : CollatzResearch.WordTrace tailWord_1263217 prefixEnd_1263217 432424994620459594252051 := by
  unfold tailWord_1263217
  simp only [CollatzResearch.WordTrace]
  refine ⟨46073309064588024132747905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30715539376392016088498603 46073309064588024132747905)
  ·
    refine ⟨34554981798441018099560929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46073309064588024132747905 34554981798441018099560929)
    ·
      refine ⟨25916236348830763574670697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34554981798441018099560929 25916236348830763574670697)
      ·
        refine ⟨19437177261623072681003023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25916236348830763574670697 19437177261623072681003023)
        ·
          refine ⟨29155765892434609021504535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19437177261623072681003023 29155765892434609021504535)
          ·
            refine ⟨43733648838651913532256803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29155765892434609021504535 43733648838651913532256803)
            ·
              refine ⟨65600473257977870298385205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43733648838651913532256803 65600473257977870298385205)
              ·
                refine ⟨6150044367935425340473613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65600473257977870298385205 6150044367935425340473613)
                ·
                  refine ⟨2306266637975784502677605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6150044367935425340473613 2306266637975784502677605)
                  ·
                    refine ⟨432424994620459594252051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306266637975784502677605 432424994620459594252051)
                    ·
                      rfl

theorem cell22_1263217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_1263217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263217 prefixEnd_1263217 := by exact prefixLift 1263217
  have htrace : WordTrace (prefixWord ++ tailWord_1263217) baseStart_1263217 baseEnd_1263217 := by
    simpa [prefixWord, tailWord_1263217, baseEnd_1263217] using wordTrace_append hprefix tailTrace_1263217
  have hstable : (prefixWord ++ tailWord_1263217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263217).length < 2 ^ (prefixWord ++ tailWord_1263217).sum := by decide
  have hdescent : baseEnd_1263217 < baseStart_1263217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263279 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 2, 4]
def baseStart_1263279 : Nat := 118140960795 + 1263279 * 2 ^ 59
def prefixEnd_1263279 : Nat := 4983230072969 + 3 ^ 40 * 1263279 * 2
def baseEnd_1263279 : Nat := 432446218487512099201861

theorem tailTrace_1263279 : CollatzResearch.WordTrace tailWord_1263279 prefixEnd_1263279 432446218487512099201861 := by
  unfold tailWord_1263279
  simp only [CollatzResearch.WordTrace]
  refine ⟨46075570390363408721504891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30717046926908939147669927 46075570390363408721504891)
  ·
    refine ⟨69113355585545113082257337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46075570390363408721504891 69113355585545113082257337)
    ·
      refine ⟨51835016689158834811693003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69113355585545113082257337 51835016689158834811693003)
      ·
        refine ⟨77752525033738252217539505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51835016689158834811693003 77752525033738252217539505)
        ·
          refine ⟨58314393775303689163154629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77752525033738252217539505 58314393775303689163154629)
          ·
            refine ⟨10933948832869441718091493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58314393775303689163154629 10933948832869441718091493)
            ·
              refine ⟨2050115406163020322142155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10933948832869441718091493 2050115406163020322142155)
              ·
                refine ⟨3075173109244530483213233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050115406163020322142155 3075173109244530483213233)
                ·
                  refine ⟨2306379831933397862409925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075173109244530483213233 2306379831933397862409925)
                  ·
                    refine ⟨432446218487512099201861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306379831933397862409925 432446218487512099201861)
                    ·
                      rfl

theorem cell22_1263279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_1263279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263279 prefixEnd_1263279 := by exact prefixLift 1263279
  have htrace : WordTrace (prefixWord ++ tailWord_1263279) baseStart_1263279 baseEnd_1263279 := by
    simpa [prefixWord, tailWord_1263279, baseEnd_1263279] using wordTrace_append hprefix tailTrace_1263279
  have hstable : (prefixWord ++ tailWord_1263279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263279).length < 2 ^ (prefixWord ++ tailWord_1263279).sum := by decide
  have hdescent : baseEnd_1263279 < baseStart_1263279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263337 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_1263337 : Nat := 118140960795 + 1263337 * 2 ^ 59
def prefixEnd_1263337 : Nat := 4983230072969 + 3 ^ 40 * 1263337 * 2
def baseEnd_1263337 : Nat := 432466073072819281251683

theorem tailTrace_1263337 : CollatzResearch.WordTrace tailWord_1263337 prefixEnd_1263337 432466073072819281251683 := by
  unfold tailWord_1263337
  simp only [CollatzResearch.WordTrace]
  refine ⟨46077685824153284627116265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30718457216102189751410843 46077685824153284627116265)
  ·
    refine ⟨34558264368114963470337199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46077685824153284627116265 34558264368114963470337199)
    ·
      refine ⟨51837396552172445205505799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34558264368114963470337199 51837396552172445205505799)
      ·
        refine ⟨77756094828258667808258699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51837396552172445205505799 77756094828258667808258699)
        ·
          refine ⟨116634142242388001712388049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77756094828258667808258699 116634142242388001712388049)
          ·
            refine ⟨87475606681791001284291037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116634142242388001712388049 87475606681791001284291037)
            ·
              refine ⟨32803352505671625481609139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87475606681791001284291037 32803352505671625481609139)
              ·
                refine ⟨49205028758507438222413709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32803352505671625481609139 49205028758507438222413709)
                ·
                  refine ⟨18451885784440289333405141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49205028758507438222413709 18451885784440289333405141)
                  ·
                    refine ⟨432466073072819281251683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18451885784440289333405141 432466073072819281251683)
                    ·
                      rfl

theorem cell22_1263337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_1263337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263337 prefixEnd_1263337 := by exact prefixLift 1263337
  have htrace : WordTrace (prefixWord ++ tailWord_1263337) baseStart_1263337 baseEnd_1263337 := by
    simpa [prefixWord, tailWord_1263337, baseEnd_1263337] using wordTrace_append hprefix tailTrace_1263337
  have hstable : (prefixWord ++ tailWord_1263337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263337).length < 2 ^ (prefixWord ++ tailWord_1263337).sum := by decide
  have hdescent : baseEnd_1263337 < baseStart_1263337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263343 : List Nat := [1, 1, 2, 1, 5, 1, 4, 3, 1, 3]
def baseStart_1263343 : Nat := 118140960795 + 1263343 * 2 ^ 59
def prefixEnd_1263343 : Nat := 4983230072969 + 3 ^ 40 * 1263343 * 2
def baseEnd_1263343 : Nat := 432468126995437265601665

theorem tailTrace_1263343 : CollatzResearch.WordTrace tailWord_1263343 prefixEnd_1263343 432468126995437265601665 := by
  unfold tailWord_1263343
  simp only [CollatzResearch.WordTrace]
  refine ⟨46077904662131547651834683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30718603108087698434556455 46077904662131547651834683)
  ·
    refine ⟨69116856993197321477752025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46077904662131547651834683 69116856993197321477752025)
    ·
      refine ⟨51837642744897991108314019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69116856993197321477752025 51837642744897991108314019)
      ·
        refine ⟨77756464117346986662471029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51837642744897991108314019 77756464117346986662471029)
        ·
          refine ⟨7289668511001279999606659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77756464117346986662471029 7289668511001279999606659)
          ·
            refine ⟨10934502766501919999409989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7289668511001279999606659 10934502766501919999409989)
            ·
              refine ⟨2050219268719109999889373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10934502766501919999409989 2050219268719109999889373)
              ·
                refine ⟨768832225769666249958515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2050219268719109999889373 768832225769666249958515)
                ·
                  refine ⟨1153248338654499374937773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768832225769666249958515 1153248338654499374937773)
                  ·
                    refine ⟨432468126995437265601665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153248338654499374937773 432468126995437265601665)
                    ·
                      rfl

theorem cell22_1263343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 3].length) (baseStart_1263343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263343 prefixEnd_1263343 := by exact prefixLift 1263343
  have htrace : WordTrace (prefixWord ++ tailWord_1263343) baseStart_1263343 baseEnd_1263343 := by
    simpa [prefixWord, tailWord_1263343, baseEnd_1263343] using wordTrace_append hprefix tailTrace_1263343
  have hstable : (prefixWord ++ tailWord_1263343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263343).length < 2 ^ (prefixWord ++ tailWord_1263343).sum := by decide
  have hdescent : baseEnd_1263343 < baseStart_1263343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263366 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1263366 : Nat := 118140960795 + 1263366 * 2 ^ 59
def prefixEnd_1263366 : Nat := 4983230072969 + 3 ^ 40 * 1263366 * 2
def baseEnd_1263366 : Nat := 432476000365472872276595

theorem tailTrace_1263366 : CollatzResearch.WordTrace tailWord_1263366 prefixEnd_1263366 432476000365472872276595 := by
  unfold tailWord_1263366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439960735657756955622561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30719162360698815053281301 1439960735657756955622561)
  ·
    refine ⟨1079970551743317716716921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1439960735657756955622561 1079970551743317716716921)
    ·
      refine ⟨809977913807488287537691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079970551743317716716921 809977913807488287537691)
      ·
        refine ⟨1214966870711232431306537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809977913807488287537691 1214966870711232431306537)
        ·
          refine ⟨911225153033424323479903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1214966870711232431306537 911225153033424323479903)
          ·
            refine ⟨1366837729550136485219855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911225153033424323479903 1366837729550136485219855)
            ·
              refine ⟨2050256594325204727829783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366837729550136485219855 2050256594325204727829783)
              ·
                refine ⟨3075384891487807091744675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050256594325204727829783 3075384891487807091744675)
                ·
                  refine ⟨4613077337231710637617013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075384891487807091744675 4613077337231710637617013)
                  ·
                    refine ⟨432476000365472872276595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4613077337231710637617013 432476000365472872276595)
                    ·
                      rfl

theorem cell22_1263366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1263366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263366 prefixEnd_1263366 := by exact prefixLift 1263366
  have htrace : WordTrace (prefixWord ++ tailWord_1263366) baseStart_1263366 baseEnd_1263366 := by
    simpa [prefixWord, tailWord_1263366, baseEnd_1263366] using wordTrace_append hprefix tailTrace_1263366
  have hstable : (prefixWord ++ tailWord_1263366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263366).length < 2 ^ (prefixWord ++ tailWord_1263366).sum := by decide
  have hdescent : baseEnd_1263366 < baseStart_1263366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263384 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 6]
def baseStart_1263384 : Nat := 118140960795 + 1263384 * 2 ^ 59
def prefixEnd_1263384 : Nat := 4983230072969 + 3 ^ 40 * 1263384 * 2
def baseEnd_1263384 : Nat := 144160720711108941775513

theorem tailTrace_1263384 : CollatzResearch.WordTrace tailWord_1263384 prefixEnd_1263384 144160720711108941775513 := by
  unfold tailWord_1263384
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039700027491505827038603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30719600036655341102718137 23039700027491505827038603)
  ·
    refine ⟨34559550041237258740557905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23039700027491505827038603 34559550041237258740557905)
    ·
      refine ⟨25919662530927944055418429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34559550041237258740557905 25919662530927944055418429)
      ·
        refine ⟨9719873449097979020781911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25919662530927944055418429 9719873449097979020781911)
        ·
          refine ⟨14579810173646968531172867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9719873449097979020781911 14579810173646968531172867)
          ·
            refine ⟨21869715260470452796759301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14579810173646968531172867 21869715260470452796759301)
            ·
              refine ⟨4100571611338209899392369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21869715260470452796759301 4100571611338209899392369)
              ·
                refine ⟨3075428708503657424544277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100571611338209899392369 3075428708503657424544277)
                ·
                  refine ⟨144160720711108941775513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3075428708503657424544277 144160720711108941775513)
                  ·
                    rfl

theorem cell22_1263384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_1263384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263384 prefixEnd_1263384 := by exact prefixLift 1263384
  have htrace : WordTrace (prefixWord ++ tailWord_1263384) baseStart_1263384 baseEnd_1263384 := by
    simpa [prefixWord, tailWord_1263384, baseEnd_1263384] using wordTrace_append hprefix tailTrace_1263384
  have hstable : (prefixWord ++ tailWord_1263384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263384).length < 2 ^ (prefixWord ++ tailWord_1263384).sum := by decide
  have hdescent : baseEnd_1263384 < baseStart_1263384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263386 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_1263386 : Nat := 118140960795 + 1263386 * 2 ^ 59
def prefixEnd_1263386 : Nat := 4983230072969 + 3 ^ 40 * 1263386 * 2
def baseEnd_1263386 : Nat := 432482846774199486776533

theorem tailTrace_1263386 : CollatzResearch.WordTrace tailWord_1263386 prefixEnd_1263386 432482846774199486776533 := by
  unfold tailWord_1263386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11519868250243941498912503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30719648667317177330433341 11519868250243941498912503)
  ·
    refine ⟨17279802375365912248368755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11519868250243941498912503 17279802375365912248368755)
    ·
      refine ⟨25919703563048868372553133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17279802375365912248368755 25919703563048868372553133)
      ·
        refine ⟨9719888836143325639707425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25919703563048868372553133 9719888836143325639707425)
        ·
          refine ⟨7289916627107494229780569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9719888836143325639707425 7289916627107494229780569)
          ·
            refine ⟨5467437470330620672335427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7289916627107494229780569 5467437470330620672335427)
            ·
              refine ⟨8201156205495931008503141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467437470330620672335427 8201156205495931008503141)
              ·
                refine ⟨1537716788530487064094339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8201156205495931008503141 1537716788530487064094339)
                ·
                  refine ⟨2306575182795730596141509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537716788530487064094339 2306575182795730596141509)
                  ·
                    refine ⟨432482846774199486776533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306575182795730596141509 432482846774199486776533)
                    ·
                      rfl

theorem cell22_1263386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_1263386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263386 prefixEnd_1263386 := by exact prefixLift 1263386
  have htrace : WordTrace (prefixWord ++ tailWord_1263386) baseStart_1263386 baseEnd_1263386 := by
    simpa [prefixWord, tailWord_1263386, baseEnd_1263386] using wordTrace_append hprefix tailTrace_1263386
  have hstable : (prefixWord ++ tailWord_1263386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263386).length < 2 ^ (prefixWord ++ tailWord_1263386).sum := by decide
  have hdescent : baseEnd_1263386 < baseStart_1263386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263416 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 4, 3]
def baseStart_1263416 : Nat := 118140960795 + 1263416 * 2 ^ 59
def prefixEnd_1263416 : Nat := 4983230072969 + 3 ^ 40 * 1263416 * 2
def baseEnd_1263416 : Nat := 432493116387289408526441

theorem tailTrace_1263416 : CollatzResearch.WordTrace tailWord_1263416 prefixEnd_1263416 432493116387289408526441 := by
  unfold tailWord_1263416
  simp only [CollatzResearch.WordTrace]
  refine ⟨23040283595433540559621051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30720378127244720746161401 23040283595433540559621051)
  ·
    refine ⟨34560425393150310839431577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23040283595433540559621051 34560425393150310839431577)
    ·
      refine ⟨25920319044862733129573683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34560425393150310839431577 25920319044862733129573683)
      ·
        refine ⟨38880478567294099694360525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25920319044862733129573683 38880478567294099694360525)
        ·
          refine ⟨14580179462735287385385197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38880478567294099694360525 14580179462735287385385197)
          ·
            refine ⟨5467567298525732769519449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14580179462735287385385197 5467567298525732769519449)
            ·
              refine ⟨4100675473894299577139587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467567298525732769519449 4100675473894299577139587)
              ·
                refine ⟨6151013210841449365709381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100675473894299577139587 6151013210841449365709381)
                ·
                  refine ⟨1153314977032771756070509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6151013210841449365709381 1153314977032771756070509)
                  ·
                    refine ⟨432493116387289408526441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153314977032771756070509 432493116387289408526441)
                    ·
                      rfl

theorem cell22_1263416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_1263416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263416 prefixEnd_1263416 := by exact prefixLift 1263416
  have htrace : WordTrace (prefixWord ++ tailWord_1263416) baseStart_1263416 baseEnd_1263416 := by
    simpa [prefixWord, tailWord_1263416, baseEnd_1263416] using wordTrace_append hprefix tailTrace_1263416
  have hstable : (prefixWord ++ tailWord_1263416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263416).length < 2 ^ (prefixWord ++ tailWord_1263416).sum := by decide
  have hdescent : baseEnd_1263416 < baseStart_1263416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263429 : List Nat := [1, 3, 1, 1, 1, 2, 6, 7]
def baseStart_1263429 : Nat := 118140960795 + 1263429 * 2 ^ 59
def prefixEnd_1263429 : Nat := 4983230072969 + 3 ^ 40 * 1263429 * 2
def baseEnd_1263429 : Nat := 48055285172551300883489

theorem tailTrace_1263429 : CollatzResearch.WordTrace tailWord_1263429 prefixEnd_1263429 48055285172551300883489 := by
  unfold tailWord_1263429
  simp only [CollatzResearch.WordTrace]
  refine ⟨46081041339819984339465341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30720694226546656226310227 46081041339819984339465341)
  ·
    refine ⟨17280390502432494127299503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46081041339819984339465341 17280390502432494127299503)
    ·
      refine ⟨25920585753648741190949255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17280390502432494127299503 25920585753648741190949255)
      ·
        refine ⟨38880878630473111786423883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25920585753648741190949255 38880878630473111786423883)
        ·
          refine ⟨58321317945709667679635825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38880878630473111786423883 58321317945709667679635825)
          ·
            refine ⟨43740988459282250759726869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58321317945709667679635825 43740988459282250759726869)
            ·
              refine ⟨2050358834028855504362197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43740988459282250759726869 2050358834028855504362197)
              ·
                refine ⟨48055285172551300883489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2050358834028855504362197 48055285172551300883489)
                ·
                  rfl

theorem cell22_1263429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 7].length) (baseStart_1263429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263429 prefixEnd_1263429 := by exact prefixLift 1263429
  have htrace : WordTrace (prefixWord ++ tailWord_1263429) baseStart_1263429 baseEnd_1263429 := by
    simpa [prefixWord, tailWord_1263429, baseEnd_1263429] using wordTrace_append hprefix tailTrace_1263429
  have hstable : (prefixWord ++ tailWord_1263429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263429).length < 2 ^ (prefixWord ++ tailWord_1263429).sum := by decide
  have hdescent : baseEnd_1263429 < baseStart_1263429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263491 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 5]
def baseStart_1263491 : Nat := 118140960795 + 1263491 * 2 ^ 59
def prefixEnd_1263491 : Nat := 4983230072969 + 3 ^ 40 * 1263491 * 2
def baseEnd_1263491 : Nat := 144172930140004737633737

theorem tailTrace_1263491 : CollatzResearch.WordTrace tailWord_1263491 prefixEnd_1263491 144172930140004737633737 := by
  unfold tailWord_1263491
  simp only [CollatzResearch.WordTrace]
  refine ⟨46083302665595368928222327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30722201777063579285481551 46083302665595368928222327)
  ·
    refine ⟨69124953998393053392333491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46083302665595368928222327 69124953998393053392333491)
    ·
      refine ⟨103687430997589580088500237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69124953998393053392333491 103687430997589580088500237)
      ·
        refine ⟨38882786624096092533187589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103687430997589580088500237 38882786624096092533187589)
        ·
          refine ⟨7290522492018017349972673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38882786624096092533187589 7290522492018017349972673)
          ·
            refine ⟨5467891869013513012479505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7290522492018017349972673 5467891869013513012479505)
            ·
              refine ⟨4100918901760134759359629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467891869013513012479505 4100918901760134759359629)
              ·
                refine ⟨1537844588160050534759861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4100918901760134759359629 1537844588160050534759861)
                ·
                  refine ⟨144172930140004737633737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1537844588160050534759861 144172930140004737633737)
                  ·
                    rfl

theorem cell22_1263491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 5].length) (baseStart_1263491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263491 prefixEnd_1263491 := by exact prefixLift 1263491
  have htrace : WordTrace (prefixWord ++ tailWord_1263491) baseStart_1263491 baseEnd_1263491 := by
    simpa [prefixWord, tailWord_1263491, baseEnd_1263491] using wordTrace_append hprefix tailTrace_1263491
  have hstable : (prefixWord ++ tailWord_1263491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263491).length < 2 ^ (prefixWord ++ tailWord_1263491).sum := by decide
  have hdescent : baseEnd_1263491 < baseStart_1263491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263566 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1263566 : Nat := 118140960795 + 1263566 * 2 ^ 59
def prefixEnd_1263566 : Nat := 4983230072969 + 3 ^ 40 * 1263566 * 2
def baseEnd_1263566 : Nat := 432544464452739017275981

theorem tailTrace_1263566 : CollatzResearch.WordTrace tailWord_1263566 prefixEnd_1263566 432544464452739017275981 := by
  unfold tailWord_1263566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760754767540457092150319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30724025426882437824801701 5760754767540457092150319)
  ·
    refine ⟨8641132151310685638225479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5760754767540457092150319 8641132151310685638225479)
    ·
      refine ⟨12961698226966028457338219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8641132151310685638225479 12961698226966028457338219)
      ·
        refine ⟨19442547340449042686007329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12961698226966028457338219 19442547340449042686007329)
        ·
          refine ⟨14581910505336782014505497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19442547340449042686007329 14581910505336782014505497)
          ·
            refine ⟨10936432879002586510879123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14581910505336782014505497 10936432879002586510879123)
            ·
              refine ⟨16404649318503879766318685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10936432879002586510879123 16404649318503879766318685)
              ·
                refine ⟨6151743494438954912369507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16404649318503879766318685 6151743494438954912369507)
                ·
                  refine ⟨9227615241658432368554261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6151743494438954912369507 9227615241658432368554261)
                  ·
                    refine ⟨432544464452739017275981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9227615241658432368554261 432544464452739017275981)
                    ·
                      rfl

theorem cell22_1263566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1263566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263566 prefixEnd_1263566 := by exact prefixLift 1263566
  have htrace : WordTrace (prefixWord ++ tailWord_1263566) baseStart_1263566 baseEnd_1263566 := by
    simpa [prefixWord, tailWord_1263566, baseEnd_1263566] using wordTrace_append hprefix tailTrace_1263566
  have hstable : (prefixWord ++ tailWord_1263566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263566).length < 2 ^ (prefixWord ++ tailWord_1263566).sum := by decide
  have hdescent : baseEnd_1263566 < baseStart_1263566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263583 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 2, 4]
def baseStart_1263583 : Nat := 118140960795 + 1263583 * 2 ^ 59
def prefixEnd_1263583 : Nat := 4983230072969 + 3 ^ 40 * 1263583 * 2
def baseEnd_1263583 : Nat := 432550283900156639600929

theorem tailTrace_1263583 : CollatzResearch.WordTrace tailWord_1263583 prefixEnd_1263583 432550283900156639600929 := by
  unfold tailWord_1263583
  simp only [CollatzResearch.WordTrace]
  refine ⟨46086658181262068640571403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30724438787508045760380935 46086658181262068640571403)
  ·
    refine ⟨69129987271893102960857105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46086658181262068640571403 69129987271893102960857105)
    ·
      refine ⟨51847490453919827220642829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69129987271893102960857105 51847490453919827220642829)
      ·
        refine ⟨19442808920219935207741061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51847490453919827220642829 19442808920219935207741061)
        ·
          refine ⟨3645526672541237851451449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19442808920219935207741061 3645526672541237851451449)
          ·
            refine ⟨2734145004405928388588587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3645526672541237851451449 2734145004405928388588587)
            ·
              refine ⟨4101217506608892582882881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734145004405928388588587 4101217506608892582882881)
              ·
                refine ⟨3075913129956669437162161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101217506608892582882881 3075913129956669437162161)
                ·
                  refine ⟨2306934847467502077871621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075913129956669437162161 2306934847467502077871621)
                  ·
                    refine ⟨432550283900156639600929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306934847467502077871621 432550283900156639600929)
                    ·
                      rfl

theorem cell22_1263583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_1263583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263583 prefixEnd_1263583 := by exact prefixLift 1263583
  have htrace : WordTrace (prefixWord ++ tailWord_1263583) baseStart_1263583 baseEnd_1263583 := by
    simpa [prefixWord, tailWord_1263583, baseEnd_1263583] using wordTrace_append hprefix tailTrace_1263583
  have hstable : (prefixWord ++ tailWord_1263583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263583).length < 2 ^ (prefixWord ++ tailWord_1263583).sum := by decide
  have hdescent : baseEnd_1263583 < baseStart_1263583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263598 : List Nat := [4, 1, 2, 1, 3, 2, 2, 7]
def baseStart_1263598 : Nat := 118140960795 + 1263598 * 2 ^ 59
def prefixEnd_1263598 : Nat := 4983230072969 + 3 ^ 40 * 1263598 * 2
def baseEnd_1263598 : Nat := 48061713189633511163987

theorem tailTrace_1263598 : CollatzResearch.WordTrace tailWord_1263598 prefixEnd_1263598 48061713189633511163987 := by
  unfold tailWord_1263598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760900659525965775295931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30724803517471817468244965 5760900659525965775295931)
  ·
    refine ⟨8641350989288948662943897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5760900659525965775295931 8641350989288948662943897)
    ·
      refine ⟨6481013241966711497207923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8641350989288948662943897 6481013241966711497207923)
      ·
        refine ⟨9721519862950067245811885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6481013241966711497207923 9721519862950067245811885)
        ·
          refine ⟨3645569948606275217179457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9721519862950067245811885 3645569948606275217179457)
          ·
            refine ⟨2734177461454706412884593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3645569948606275217179457 2734177461454706412884593)
            ·
              refine ⟨2050633096091029809663445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734177461454706412884593 2050633096091029809663445)
              ·
                refine ⟨48061713189633511163987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2050633096091029809663445 48061713189633511163987)
                ·
                  rfl

theorem cell22_1263598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_1263598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263598 prefixEnd_1263598 := by exact prefixLift 1263598
  have htrace : WordTrace (prefixWord ++ tailWord_1263598) baseStart_1263598 baseEnd_1263598 := by
    simpa [prefixWord, tailWord_1263598, baseEnd_1263598] using wordTrace_append hprefix tailTrace_1263598
  have hstable : (prefixWord ++ tailWord_1263598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263598).length < 2 ^ (prefixWord ++ tailWord_1263598).sum := by decide
  have hdescent : baseEnd_1263598 < baseStart_1263598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263613 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_1263613 : Nat := 118140960795 + 1263613 * 2 ^ 59
def prefixEnd_1263613 : Nat := 4983230072969 + 3 ^ 40 * 1263613 * 2
def baseEnd_1263613 : Nat := 432560553513246561350837

theorem tailTrace_1263613 : CollatzResearch.WordTrace tailWord_1263613 prefixEnd_1263613 432560553513246561350837 := by
  unfold tailWord_1263613
  simp only [CollatzResearch.WordTrace]
  refine ⟨46087752371153383764163493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30725168247435589176108995 46087752371153383764163493)
  ·
    refine ⟨8641453569591259455780655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46087752371153383764163493 8641453569591259455780655)
    ·
      refine ⟨12962180354386889183670983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8641453569591259455780655 12962180354386889183670983)
      ·
        refine ⟨19443270531580333775506475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12962180354386889183670983 19443270531580333775506475)
        ·
          refine ⟨29164905797370500663259713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19443270531580333775506475 29164905797370500663259713)
          ·
            refine ⟨21873679348027875497444785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29164905797370500663259713 21873679348027875497444785)
            ·
              refine ⟨16405259511020906623083589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21873679348027875497444785 16405259511020906623083589)
              ·
                refine ⟨3075986158316419991828173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16405259511020906623083589 3075986158316419991828173)
                ·
                  refine ⟨1153494809368657496935565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3075986158316419991828173 1153494809368657496935565)
                  ·
                    refine ⟨432560553513246561350837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153494809368657496935565 432560553513246561350837)
                    ·
                      rfl

theorem cell22_1263613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_1263613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263613 prefixEnd_1263613 := by exact prefixLift 1263613
  have htrace : WordTrace (prefixWord ++ tailWord_1263613) baseStart_1263613 baseEnd_1263613 := by
    simpa [prefixWord, tailWord_1263613, baseEnd_1263613] using wordTrace_append hprefix tailTrace_1263613
  have hstable : (prefixWord ++ tailWord_1263613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263613).length < 2 ^ (prefixWord ++ tailWord_1263613).sum := by decide
  have hdescent : baseEnd_1263613 < baseStart_1263613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263641 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_1263641 : Nat := 118140960795 + 1263641 * 2 ^ 59
def prefixEnd_1263641 : Nat := 4983230072969 + 3 ^ 40 * 1263641 * 2
def baseEnd_1263641 : Nat := 432570138485463821650751

theorem tailTrace_1263641 : CollatzResearch.WordTrace tailWord_1263641 prefixEnd_1263641 432570138485463821650751 := by
  unfold tailWord_1263641
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088773615051944546182777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30725849076701296364121851 46088773615051944546182777)
  ·
    refine ⟨34566580211288958409637083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46088773615051944546182777 34566580211288958409637083)
    ·
      refine ⟨51849870316933437614455625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34566580211288958409637083 51849870316933437614455625)
      ·
        refine ⟨38887402737700078210841719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51849870316933437614455625 38887402737700078210841719)
        ·
          refine ⟨58331104106550117316262579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38887402737700078210841719 58331104106550117316262579)
          ·
            refine ⟨87496656159825175974393869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58331104106550117316262579 87496656159825175974393869)
            ·
              refine ⟨32811246059934440990397701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87496656159825175974393869 32811246059934440990397701)
              ·
                refine ⟨6152108636237707685699569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32811246059934440990397701 6152108636237707685699569)
                ·
                  refine ⟨4614081477178280764274677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6152108636237707685699569 4614081477178280764274677)
                  ·
                    refine ⟨432570138485463821650751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4614081477178280764274677 432570138485463821650751)
                    ·
                      rfl

theorem cell22_1263641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_1263641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263641 prefixEnd_1263641 := by exact prefixLift 1263641
  have htrace : WordTrace (prefixWord ++ tailWord_1263641) baseStart_1263641 baseEnd_1263641 := by
    simpa [prefixWord, tailWord_1263641, baseEnd_1263641] using wordTrace_append hprefix tailTrace_1263641
  have hstable : (prefixWord ++ tailWord_1263641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263641).length < 2 ^ (prefixWord ++ tailWord_1263641).sum := by decide
  have hdescent : baseEnd_1263641 < baseStart_1263641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263658 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1263658 : Nat := 118140960795 + 1263658 * 2 ^ 59
def prefixEnd_1263658 : Nat := 4983230072969 + 3 ^ 40 * 1263658 * 2
def baseEnd_1263658 : Nat := 432575957932881443975699

theorem tailTrace_1263658 : CollatzResearch.WordTrace tailWord_1263658 prefixEnd_1263658 432575957932881443975699 := by
  unfold tailWord_1263658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522348413997589112387907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30726262437326904299701085 11522348413997589112387907)
  ·
    refine ⟨17283522620996383668581861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11522348413997589112387907 17283522620996383668581861)
    ·
      refine ⟨3240660491436821937859099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17283522620996383668581861 3240660491436821937859099)
      ·
        refine ⟨4860990737155232906788649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3240660491436821937859099 4860990737155232906788649)
        ·
          refine ⟨3645743052866424680091487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4860990737155232906788649 3645743052866424680091487)
          ·
            refine ⟨5468614579299637020137231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645743052866424680091487 5468614579299637020137231)
            ·
              refine ⟨8202921868949455530205847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468614579299637020137231 8202921868949455530205847)
              ·
                refine ⟨12304382803424183295308771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8202921868949455530205847 12304382803424183295308771)
                ·
                  refine ⟨18456574205136274942963157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12304382803424183295308771 18456574205136274942963157)
                  ·
                    refine ⟨432575957932881443975699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18456574205136274942963157 432575957932881443975699)
                    ·
                      rfl

theorem cell22_1263658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1263658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263658 prefixEnd_1263658 := by exact prefixLift 1263658
  have htrace : WordTrace (prefixWord ++ tailWord_1263658) baseStart_1263658 baseEnd_1263658 := by
    simpa [prefixWord, tailWord_1263658, baseEnd_1263658] using wordTrace_append hprefix tailTrace_1263658
  have hstable : (prefixWord ++ tailWord_1263658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263658).length < 2 ^ (prefixWord ++ tailWord_1263658).sum := by decide
  have hdescent : baseEnd_1263658 < baseStart_1263658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263671 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 8]
def baseStart_1263671 : Nat := 118140960795 + 1263671 * 2 ^ 59
def prefixEnd_1263671 : Nat := 4983230072969 + 3 ^ 40 * 1263671 * 2
def baseEnd_1263671 : Nat := 144193469366184581133553

theorem tailTrace_1263671 : CollatzResearch.WordTrace tailWord_1263671 prefixEnd_1263671 144193469366184581133553 := by
  unfold tailWord_1263671
  simp only [CollatzResearch.WordTrace]
  refine ⟨46089867804943259669774867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30726578536628839779849911 46089867804943259669774867)
  ·
    refine ⟨69134801707414889504662301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46089867804943259669774867 69134801707414889504662301)
    ·
      refine ⟨25925550640280583564248363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69134801707414889504662301 25925550640280583564248363)
      ·
        refine ⟨38888325960420875346372545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25925550640280583564248363 38888325960420875346372545)
        ·
          refine ⟨29166244470315656509779409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38888325960420875346372545 29166244470315656509779409)
          ·
            refine ⟨21874683352736742382334557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29166244470315656509779409 21874683352736742382334557)
            ·
              refine ⟨8203006257276278393375459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21874683352736742382334557 8203006257276278393375459)
              ·
                refine ⟨12304509385914417590063189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8203006257276278393375459 12304509385914417590063189)
                ·
                  refine ⟨144193469366184581133553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12304509385914417590063189 144193469366184581133553)
                  ·
                    rfl

theorem cell22_1263671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 8].length) (baseStart_1263671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263671 prefixEnd_1263671 := by exact prefixLift 1263671
  have htrace : WordTrace (prefixWord ++ tailWord_1263671) baseStart_1263671 baseEnd_1263671 := by
    simpa [prefixWord, tailWord_1263671, baseEnd_1263671] using wordTrace_append hprefix tailTrace_1263671
  have hstable : (prefixWord ++ tailWord_1263671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263671).length < 2 ^ (prefixWord ++ tailWord_1263671).sum := by decide
  have hdescent : baseEnd_1263671 < baseStart_1263671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263812 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1263812 : Nat := 118140960795 + 1263812 * 2 ^ 59
def prefixEnd_1263812 : Nat := 4983230072969 + 3 ^ 40 * 1263812 * 2
def baseEnd_1263812 : Nat := 144209558426692125208409

theorem tailTrace_1263812 : CollatzResearch.WordTrace tailWord_1263812 prefixEnd_1263812 144209558426692125208409 := by
  unfold tailWord_1263812
  simp only [CollatzResearch.WordTrace]
  refine ⟨23047505248716220375328845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30730006998288293833771793 23047505248716220375328845)
  ·
    refine ⟨8642814468268582640748317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23047505248716220375328845 8642814468268582640748317)
    ·
      refine ⟨3241055425600718490280619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8642814468268582640748317 3241055425600718490280619)
      ·
        refine ⟨4861583138401077735420929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241055425600718490280619 4861583138401077735420929)
        ·
          refine ⟨3646187353800808301565697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4861583138401077735420929 3646187353800808301565697)
          ·
            refine ⟨2734640515350606226174273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3646187353800808301565697 2734640515350606226174273)
            ·
              refine ⟨2050980386512954669630705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734640515350606226174273 2050980386512954669630705)
              ·
                refine ⟨1538235289884716002223029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2050980386512954669630705 1538235289884716002223029)
                ·
                  refine ⟨144209558426692125208409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1538235289884716002223029 144209558426692125208409)
                  ·
                    rfl

theorem cell22_1263812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1263812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263812 prefixEnd_1263812 := by exact prefixLift 1263812
  have htrace : WordTrace (prefixWord ++ tailWord_1263812) baseStart_1263812 baseEnd_1263812 := by
    simpa [prefixWord, tailWord_1263812, baseEnd_1263812] using wordTrace_append hprefix tailTrace_1263812
  have hstable : (prefixWord ++ tailWord_1263812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263812).length < 2 ^ (prefixWord ++ tailWord_1263812).sum := by decide
  have hdescent : baseEnd_1263812 < baseStart_1263812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263823 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 6]
def baseStart_1263823 : Nat := 118140960795 + 1263823 * 2 ^ 59
def prefixEnd_1263823 : Nat := 4983230072969 + 3 ^ 40 * 1263823 * 2
def baseEnd_1263823 : Nat := 144210813601625337866731

theorem tailTrace_1263823 : CollatzResearch.WordTrace tailWord_1263823 prefixEnd_1263823 144210813601625337866731 := by
  unfold tailWord_1263823
  simp only [CollatzResearch.WordTrace]
  refine ⟨46095411700392589629308123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30730274466928393086205415 46095411700392589629308123)
  ·
    refine ⟨69143117550588884443962185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46095411700392589629308123 69143117550588884443962185)
    ·
      refine ⟨51857338162941663332971639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69143117550588884443962185 51857338162941663332971639)
      ·
        refine ⟨77786007244412494999457459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51857338162941663332971639 77786007244412494999457459)
        ·
          refine ⟨116679010866618742499186189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77786007244412494999457459 116679010866618742499186189)
          ·
            refine ⟨43754629074982028437194821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116679010866618742499186189 43754629074982028437194821)
            ·
              refine ⟨8203992951559130331974029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43754629074982028437194821 8203992951559130331974029)
              ·
                refine ⟨3076497356834673874490261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8203992951559130331974029 3076497356834673874490261)
                ·
                  refine ⟨144210813601625337866731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3076497356834673874490261 144210813601625337866731)
                  ·
                    rfl

theorem cell22_1263823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 6].length) (baseStart_1263823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263823 prefixEnd_1263823 := by exact prefixLift 1263823
  have htrace : WordTrace (prefixWord ++ tailWord_1263823) baseStart_1263823 baseEnd_1263823 := by
    simpa [prefixWord, tailWord_1263823, baseEnd_1263823] using wordTrace_append hprefix tailTrace_1263823
  have hstable : (prefixWord ++ tailWord_1263823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263823).length < 2 ^ (prefixWord ++ tailWord_1263823).sum := by decide
  have hdescent : baseEnd_1263823 < baseStart_1263823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263855 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 1, 5]
def baseStart_1263855 : Nat := 118140960795 + 1263855 * 2 ^ 59
def prefixEnd_1263855 : Nat := 4983230072969 + 3 ^ 40 * 1263855 * 2
def baseEnd_1263855 : Nat := 432643395058838596800095

theorem tailTrace_1263855 : CollatzResearch.WordTrace tailWord_1263855 prefixEnd_1263855 432643395058838596800095 := by
  unfold tailWord_1263855
  simp only [CollatzResearch.WordTrace]
  refine ⟨46096578836276659094473019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30731052557517772729648679 46096578836276659094473019)
  ·
    refine ⟨69144868254414988641709529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46096578836276659094473019 69144868254414988641709529)
    ·
      refine ⟨51858651190811241481282147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69144868254414988641709529 51858651190811241481282147)
      ·
        refine ⟨77787976786216862221923221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51858651190811241481282147 77787976786216862221923221)
        ·
          refine ⟨3646311411853915416652651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77787976786216862221923221 3646311411853915416652651)
          ·
            refine ⟨5469467117780873124978977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646311411853915416652651 5469467117780873124978977)
            ·
              refine ⟨4102100338335654843734233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5469467117780873124978977 4102100338335654843734233)
              ·
                refine ⟨3076575253751741132800675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4102100338335654843734233 3076575253751741132800675)
                ·
                  refine ⟨4614862880627611699201013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076575253751741132800675 4614862880627611699201013)
                  ·
                    refine ⟨432643395058838596800095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4614862880627611699201013 432643395058838596800095)
                    ·
                      rfl

theorem cell22_1263855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_1263855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263855 prefixEnd_1263855 := by exact prefixLift 1263855
  have htrace : WordTrace (prefixWord ++ tailWord_1263855) baseStart_1263855 baseEnd_1263855 := by
    simpa [prefixWord, tailWord_1263855, baseEnd_1263855] using wordTrace_append hprefix tailTrace_1263855
  have hstable : (prefixWord ++ tailWord_1263855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263855).length < 2 ^ (prefixWord ++ tailWord_1263855).sum := by decide
  have hdescent : baseEnd_1263855 < baseStart_1263855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263872 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 2, 3]
def baseStart_1263872 : Nat := 118140960795 + 1263872 * 2 ^ 59
def prefixEnd_1263872 : Nat := 4983230072969 + 3 ^ 40 * 1263872 * 2
def baseEnd_1263872 : Nat := 432649214506256219125043

theorem tailTrace_1263872 : CollatzResearch.WordTrace tailWord_1263872 prefixEnd_1263872 432649214506256219125043 := by
  unfold tailWord_1263872
  simp only [CollatzResearch.WordTrace]
  refine ⟨23048599438607535498920935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30731465918143380665227913 23048599438607535498920935)
  ·
    refine ⟨34572899157911303248381403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23048599438607535498920935 34572899157911303248381403)
    ·
      refine ⟨51859348736866954872572105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34572899157911303248381403 51859348736866954872572105)
      ·
        refine ⟨38894511552650216154429079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51859348736866954872572105 38894511552650216154429079)
        ·
          refine ⟨58341767328975324231643619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38894511552650216154429079 58341767328975324231643619)
          ·
            refine ⟨87512650993462986347465429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58341767328975324231643619 87512650993462986347465429)
            ·
              refine ⟨2051077757659288742518721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87512650993462986347465429 2051077757659288742518721)
              ·
                refine ⟨1538308318244466556889041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051077757659288742518721 1538308318244466556889041)
                ·
                  refine ⟨1153731238683349917666781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538308318244466556889041 1153731238683349917666781)
                  ·
                    refine ⟨432649214506256219125043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153731238683349917666781 432649214506256219125043)
                    ·
                      rfl

theorem cell22_1263872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_1263872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263872 prefixEnd_1263872 := by exact prefixLift 1263872
  have htrace : WordTrace (prefixWord ++ tailWord_1263872) baseStart_1263872 baseEnd_1263872 := by
    simpa [prefixWord, tailWord_1263872, baseEnd_1263872] using wordTrace_append hprefix tailTrace_1263872
  have hstable : (prefixWord ++ tailWord_1263872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263872).length < 2 ^ (prefixWord ++ tailWord_1263872).sum := by decide
  have hdescent : baseEnd_1263872 < baseStart_1263872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263874 : List Nat := [3, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1263874 : Nat := 118140960795 + 1263874 * 2 ^ 59
def prefixEnd_1263874 : Nat := 4983230072969 + 3 ^ 40 * 1263874 * 2
def baseEnd_1263874 : Nat := 144216633049042960191679

theorem tailTrace_1263874 : CollatzResearch.WordTrace tailWord_1263874 prefixEnd_1263874 144216633049042960191679 := by
  unfold tailWord_1263874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524317955801956334853669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30731514548805216892943117 11524317955801956334853669)
  ·
    refine ⟨2160809616712866812785063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11524317955801956334853669 2160809616712866812785063)
    ·
      refine ⟨3241214425069300219177595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2160809616712866812785063 3241214425069300219177595)
      ·
        refine ⟨4861821637603950328766393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241214425069300219177595 4861821637603950328766393)
        ·
          refine ⟨3646366228202962746574795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4861821637603950328766393 3646366228202962746574795)
          ·
            refine ⟨5469549342304444119862193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646366228202962746574795 5469549342304444119862193)
            ·
              refine ⟨4102162006728333089896645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5469549342304444119862193 4102162006728333089896645)
              ·
                refine ⟨769155376261562454355621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4102162006728333089896645 769155376261562454355621)
                ·
                  refine ⟨144216633049042960191679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769155376261562454355621 144216633049042960191679)
                  ·
                    rfl

theorem cell22_1263874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1263874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263874 prefixEnd_1263874 := by exact prefixLift 1263874
  have htrace : WordTrace (prefixWord ++ tailWord_1263874) baseStart_1263874 baseEnd_1263874 := by
    simpa [prefixWord, tailWord_1263874, baseEnd_1263874] using wordTrace_append hprefix tailTrace_1263874
  have hstable : (prefixWord ++ tailWord_1263874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263874).length < 2 ^ (prefixWord ++ tailWord_1263874).sum := by decide
  have hdescent : baseEnd_1263874 < baseStart_1263874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263889 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 2, 3]
def baseStart_1263889 : Nat := 118140960795 + 1263889 * 2 ^ 59
def prefixEnd_1263889 : Nat := 4983230072969 + 3 ^ 40 * 1263889 * 2
def baseEnd_1263889 : Nat := 432655033953673841449991

theorem tailTrace_1263889 : CollatzResearch.WordTrace tailWord_1263889 prefixEnd_1263889 432655033953673841449991 := by
  unfold tailWord_1263889
  simp only [CollatzResearch.WordTrace]
  refine ⟨46097818918153482901210721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30731879278768988600807147 46097818918153482901210721)
  ·
    refine ⟨34573364188615112175908041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46097818918153482901210721 34573364188615112175908041)
    ·
      refine ⟨25930023141461334131931031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34573364188615112175908041 25930023141461334131931031)
      ·
        refine ⟨38895034712192001197896547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25930023141461334131931031 38895034712192001197896547)
        ·
          refine ⟨58342552068288001796844821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38895034712192001197896547 58342552068288001796844821)
          ·
            refine ⟨2734807128201000084227101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58342552068288001796844821 2734807128201000084227101)
            ·
              refine ⟨1025552673075375031585163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2734807128201000084227101 1025552673075375031585163)
              ·
                refine ⟨1538329009613062547377745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025552673075375031585163 1538329009613062547377745)
                ·
                  refine ⟨1153746757209796910533309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538329009613062547377745 1153746757209796910533309)
                  ·
                    refine ⟨432655033953673841449991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153746757209796910533309 432655033953673841449991)
                    ·
                      rfl

theorem cell22_1263889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_1263889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263889 prefixEnd_1263889 := by exact prefixLift 1263889
  have htrace : WordTrace (prefixWord ++ tailWord_1263889) baseStart_1263889 baseEnd_1263889 := by
    simpa [prefixWord, tailWord_1263889, baseEnd_1263889] using wordTrace_append hprefix tailTrace_1263889
  have hstable : (prefixWord ++ tailWord_1263889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263889).length < 2 ^ (prefixWord ++ tailWord_1263889).sum := by decide
  have hdescent : baseEnd_1263889 < baseStart_1263889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263930 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_1263930 : Nat := 118140960795 + 1263930 * 2 ^ 59
def prefixEnd_1263930 : Nat := 4983230072969 + 3 ^ 40 * 1263930 * 2
def baseEnd_1263930 : Nat := 144223023030521133724955

theorem tailTrace_1263930 : CollatzResearch.WordTrace tailWord_1263930 prefixEnd_1263930 144223023030521133724955 := by
  unfold tailWord_1263930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524828577751236725863311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30732876207336631268968829 11524828577751236725863311)
  ·
    refine ⟨17287242866626855088794967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11524828577751236725863311 17287242866626855088794967)
    ·
      refine ⟨25930864299940282633192451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17287242866626855088794967 25930864299940282633192451)
      ·
        refine ⟨38896296449910423949788677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25930864299940282633192451 38896296449910423949788677)
        ·
          refine ⟨7293055584358204490585377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38896296449910423949788677 7293055584358204490585377)
          ·
            refine ⟨5469791688268653367939033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7293055584358204490585377 5469791688268653367939033)
            ·
              refine ⟨4102343766201490025954275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5469791688268653367939033 4102343766201490025954275)
              ·
                refine ⟨6153515649302235038931413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102343766201490025954275 6153515649302235038931413)
                ·
                  refine ⟨144223023030521133724955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6153515649302235038931413 144223023030521133724955)
                  ·
                    rfl

theorem cell22_1263930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_1263930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263930 prefixEnd_1263930 := by exact prefixLift 1263930
  have htrace : WordTrace (prefixWord ++ tailWord_1263930) baseStart_1263930 baseEnd_1263930 := by
    simpa [prefixWord, tailWord_1263930, baseEnd_1263930] using wordTrace_append hprefix tailTrace_1263930
  have hstable : (prefixWord ++ tailWord_1263930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263930).length < 2 ^ (prefixWord ++ tailWord_1263930).sum := by decide
  have hdescent : baseEnd_1263930 < baseStart_1263930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263934 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1263934 : Nat := 118140960795 + 1263934 * 2 ^ 59
def prefixEnd_1263934 : Nat := 4983230072969 + 3 ^ 40 * 1263934 * 2
def baseEnd_1263934 : Nat := 432670438373308724074853

theorem tailTrace_1263934 : CollatzResearch.WordTrace tailWord_1263934 prefixEnd_1263934 432670438373308724074853 := by
  unfold tailWord_1263934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762432525373806948324857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30732973468660303724399237 5762432525373806948324857)
  ·
    refine ⟨4321824394030355211243643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5762432525373806948324857 4321824394030355211243643)
    ·
      refine ⟨6482736591045532816865465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321824394030355211243643 6482736591045532816865465)
      ·
        refine ⟨4862052443284149612649099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6482736591045532816865465 4862052443284149612649099)
        ·
          refine ⟨7293078664926224418973649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862052443284149612649099 7293078664926224418973649)
          ·
            refine ⟨5469808998694668314230237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7293078664926224418973649 5469808998694668314230237)
            ·
              refine ⟨2051178374510500617836339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5469808998694668314230237 2051178374510500617836339)
              ·
                refine ⟨3076767561765750926754509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051178374510500617836339 3076767561765750926754509)
                ·
                  refine ⟨1153787835662156597532941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3076767561765750926754509 1153787835662156597532941)
                  ·
                    refine ⟨432670438373308724074853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153787835662156597532941 432670438373308724074853)
                    ·
                      rfl

theorem cell22_1263934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1263934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263934 prefixEnd_1263934 := by exact prefixLift 1263934
  have htrace : WordTrace (prefixWord ++ tailWord_1263934) baseStart_1263934 baseEnd_1263934 := by
    simpa [prefixWord, tailWord_1263934, baseEnd_1263934] using wordTrace_append hprefix tailTrace_1263934
  have hstable : (prefixWord ++ tailWord_1263934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263934).length < 2 ^ (prefixWord ++ tailWord_1263934).sum := by decide
  have hdescent : baseEnd_1263934 < baseStart_1263934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263940 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1263940 : Nat := 118140960795 + 1263940 * 2 ^ 59
def prefixEnd_1263940 : Nat := 4983230072969 + 3 ^ 40 * 1263940 * 2
def baseEnd_1263940 : Nat := 432672492295926708424835

theorem tailTrace_1263940 : CollatzResearch.WordTrace tailWord_1263940 prefixEnd_1263940 432672492295926708424835 := by
  unfold tailWord_1263940
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049839520484359305658637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30733119360645812407544849 23049839520484359305658637)
  ·
    refine ⟨8643689820181634739621989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23049839520484359305658637 8643689820181634739621989)
    ·
      refine ⟨1620691841284056513679123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8643689820181634739621989 1620691841284056513679123)
      ·
        refine ⟨2431037761926084770518685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620691841284056513679123 2431037761926084770518685)
        ·
          refine ⟨911639160722281788944507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2431037761926084770518685 911639160722281788944507)
          ·
            refine ⟨1367458741083422683416761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911639160722281788944507 1367458741083422683416761)
            ·
              refine ⟨1025594055812567012562571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367458741083422683416761 1025594055812567012562571)
              ·
                refine ⟨1538391083718850518843857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025594055812567012562571 1538391083718850518843857)
                ·
                  refine ⟨1153793312789137889132893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538391083718850518843857 1153793312789137889132893)
                  ·
                    refine ⟨432672492295926708424835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153793312789137889132893 432672492295926708424835)
                    ·
                      rfl

theorem cell22_1263940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1263940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1263940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1263940 prefixEnd_1263940 := by exact prefixLift 1263940
  have htrace : WordTrace (prefixWord ++ tailWord_1263940) baseStart_1263940 baseEnd_1263940 := by
    simpa [prefixWord, tailWord_1263940, baseEnd_1263940] using wordTrace_append hprefix tailTrace_1263940
  have hstable : (prefixWord ++ tailWord_1263940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263940).length < 2 ^ (prefixWord ++ tailWord_1263940).sum := by decide
  have hdescent : baseEnd_1263940 < baseStart_1263940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264005 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_1264005 : Nat := 118140960795 + 1264005 * 2 ^ 59
def prefixEnd_1264005 : Nat := 4983230072969 + 3 ^ 40 * 1264005 * 2
def baseEnd_1264005 : Nat := 432694743124288205549635

theorem tailTrace_1264005 : CollatzResearch.WordTrace tailWord_1264005 prefixEnd_1264005 432694743124288205549635 := by
  unfold tailWord_1264005
  simp only [CollatzResearch.WordTrace]
  refine ⟨46102049785733234712433469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30734699857155489808288979 46102049785733234712433469)
  ·
    refine ⟨17288268669649963017162551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46102049785733234712433469 17288268669649963017162551)
    ·
      refine ⟨25932403004474944525743827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17288268669649963017162551 25932403004474944525743827)
      ·
        refine ⟨38898604506712416788615741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25932403004474944525743827 38898604506712416788615741)
        ·
          refine ⟨14586976690017156295730903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38898604506712416788615741 14586976690017156295730903)
          ·
            refine ⟨21880465035025734443596355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14586976690017156295730903 21880465035025734443596355)
            ·
              refine ⟨32820697552538601665394533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21880465035025734443596355 32820697552538601665394533)
              ·
                refine ⟨6153880791100987812261475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32820697552538601665394533 6153880791100987812261475)
                ·
                  refine ⟨9230821186651481718392213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153880791100987812261475 9230821186651481718392213)
                  ·
                    refine ⟨432694743124288205549635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9230821186651481718392213 432694743124288205549635)
                    ·
                      rfl

theorem cell22_1264005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_1264005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264005 prefixEnd_1264005 := by exact prefixLift 1264005
  have htrace : WordTrace (prefixWord ++ tailWord_1264005) baseStart_1264005 baseEnd_1264005 := by
    simpa [prefixWord, tailWord_1264005, baseEnd_1264005] using wordTrace_append hprefix tailTrace_1264005
  have hstable : (prefixWord ++ tailWord_1264005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264005).length < 2 ^ (prefixWord ++ tailWord_1264005).sum := by decide
  have hdescent : baseEnd_1264005 < baseStart_1264005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264007 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1264007 : Nat := 118140960795 + 1264007 * 2 ^ 59
def prefixEnd_1264007 : Nat := 4983230072969 + 3 ^ 40 * 1264007 * 2
def baseEnd_1264007 : Nat := 432695427765160866999629

theorem tailTrace_1264007 : CollatzResearch.WordTrace tailWord_1264007 prefixEnd_1264007 432695427765160866999629 := by
  unfold tailWord_1264007
  simp only [CollatzResearch.WordTrace]
  refine ⟨46102122731725989054006275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30734748487817326036004183 46102122731725989054006275)
  ·
    refine ⟨69153184097588983581009413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46102122731725989054006275 69153184097588983581009413)
    ·
      refine ⟨12966222018297934421439265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69153184097588983581009413 12966222018297934421439265)
      ·
        refine ⟨9724666513723450816079449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12966222018297934421439265 9724666513723450816079449)
        ·
          refine ⟨7293499885292588112059587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9724666513723450816079449 7293499885292588112059587)
          ·
            refine ⟨10940249827938882168089381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293499885292588112059587 10940249827938882168089381)
            ·
              refine ⟨2051296842738540406516759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10940249827938882168089381 2051296842738540406516759)
              ·
                refine ⟨3076945264107810609775139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051296842738540406516759 3076945264107810609775139)
                ·
                  refine ⟨4615417896161715914662709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076945264107810609775139 4615417896161715914662709)
                  ·
                    refine ⟨432695427765160866999629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4615417896161715914662709 432695427765160866999629)
                    ·
                      rfl

theorem cell22_1264007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1264007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264007 prefixEnd_1264007 := by exact prefixLift 1264007
  have htrace : WordTrace (prefixWord ++ tailWord_1264007) baseStart_1264007 baseEnd_1264007 := by
    simpa [prefixWord, tailWord_1264007, baseEnd_1264007] using wordTrace_append hprefix tailTrace_1264007
  have hstable : (prefixWord ++ tailWord_1264007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264007).length < 2 ^ (prefixWord ++ tailWord_1264007).sum := by decide
  have hdescent : baseEnd_1264007 < baseStart_1264007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264103 : List Nat := [1, 1, 5, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1264103 : Nat := 118140960795 + 1264103 * 2 ^ 59
def prefixEnd_1264103 : Nat := 4983230072969 + 3 ^ 40 * 1264103 * 2
def baseEnd_1264103 : Nat := 432728290527048616599335

theorem tailTrace_1264103 : CollatzResearch.WordTrace tailWord_1264103 prefixEnd_1264103 432728290527048616599335 := by
  unfold tailWord_1264103
  simp only [CollatzResearch.WordTrace]
  refine ⟨46105624139378197449500963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30737082759585464966333975 46105624139378197449500963)
  ·
    refine ⟨69158436209067296174251445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46105624139378197449500963 69158436209067296174251445)
    ·
      refine ⟨6483603394600059016336073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69158436209067296174251445 6483603394600059016336073)
      ·
        refine ⟨4862702545950044262252055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6483603394600059016336073 4862702545950044262252055)
        ·
          refine ⟨7294053818925066393378083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862702545950044262252055 7294053818925066393378083)
          ·
            refine ⟨10941080728387599590067125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294053818925066393378083 10941080728387599590067125)
            ·
              refine ⟨1025726318286337461568793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10941080728387599590067125 1025726318286337461568793)
              ·
                refine ⟨769294738714753096176595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025726318286337461568793 769294738714753096176595)
                ·
                  refine ⟨1153942108072129644264893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769294738714753096176595 1153942108072129644264893)
                  ·
                    refine ⟨432728290527048616599335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153942108072129644264893 432728290527048616599335)
                    ·
                      rfl

theorem cell22_1264103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1264103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264103 prefixEnd_1264103 := by exact prefixLift 1264103
  have htrace : WordTrace (prefixWord ++ tailWord_1264103) baseStart_1264103 baseEnd_1264103 := by
    simpa [prefixWord, tailWord_1264103, baseEnd_1264103] using wordTrace_append hprefix tailTrace_1264103
  have hstable : (prefixWord ++ tailWord_1264103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264103).length < 2 ^ (prefixWord ++ tailWord_1264103).sum := by decide
  have hdescent : baseEnd_1264103 < baseStart_1264103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264112 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_1264112 : Nat := 118140960795 + 1264112 * 2 ^ 59
def prefixEnd_1264112 : Nat := 4983230072969 + 3 ^ 40 * 1264112 * 2
def baseEnd_1264112 : Nat := 432731371410975593124307

theorem tailTrace_1264112 : CollatzResearch.WordTrace tailWord_1264112 prefixEnd_1264112 432731371410975593124307 := by
  unfold tailWord_1264112
  simp only [CollatzResearch.WordTrace]
  refine ⟨23052976198172795993289295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30737301597563727991052393 23052976198172795993289295)
  ·
    refine ⟨34579464297259193989933943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23052976198172795993289295 34579464297259193989933943)
    ·
      refine ⟨51869196445888790984900915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34579464297259193989933943 51869196445888790984900915)
      ·
        refine ⟨77803794668833186477351373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51869196445888790984900915 77803794668833186477351373)
        ·
          refine ⟨29176423000812444929006765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77803794668833186477351373 29176423000812444929006765)
          ·
            refine ⟨10941158625304666848377537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29176423000812444929006765 10941158625304666848377537)
            ·
              refine ⟨8205868968978500136283153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10941158625304666848377537 8205868968978500136283153)
              ·
                refine ⟨6154401726733875102212365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8205868968978500136283153 6154401726733875102212365)
                ·
                  refine ⟨2307900647525203163329637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6154401726733875102212365 2307900647525203163329637)
                  ·
                    refine ⟨432731371410975593124307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2307900647525203163329637 432731371410975593124307)
                    ·
                      rfl

theorem cell22_1264112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_1264112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264112 prefixEnd_1264112 := by exact prefixLift 1264112
  have htrace : WordTrace (prefixWord ++ tailWord_1264112) baseStart_1264112 baseEnd_1264112 := by
    simpa [prefixWord, tailWord_1264112, baseEnd_1264112] using wordTrace_append hprefix tailTrace_1264112
  have hstable : (prefixWord ++ tailWord_1264112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264112).length < 2 ^ (prefixWord ++ tailWord_1264112).sum := by decide
  have hdescent : baseEnd_1264112 < baseStart_1264112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264129 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1264129 : Nat := 118140960795 + 1264129 * 2 ^ 59
def prefixEnd_1264129 : Nat := 4983230072969 + 3 ^ 40 * 1264129 * 2
def baseEnd_1264129 : Nat := 432737190858393215449255

theorem tailTrace_1264129 : CollatzResearch.WordTrace tailWord_1264129 prefixEnd_1264129 432737190858393215449255 := by
  unfold tailWord_1264129
  simp only [CollatzResearch.WordTrace]
  refine ⟨46106572437284003889947441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30737714958189335926631627 46106572437284003889947441)
  ·
    refine ⟨34579929327963002917460581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46106572437284003889947441 34579929327963002917460581)
    ·
      refine ⟨6483736748993063047023859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34579929327963002917460581 6483736748993063047023859)
      ·
        refine ⟨9725605123489594570535789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6483736748993063047023859 9725605123489594570535789)
        ·
          refine ⟨3647101921308597963950921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9725605123489594570535789 3647101921308597963950921)
          ·
            refine ⟨2735326440981448472963191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3647101921308597963950921 2735326440981448472963191)
            ·
              refine ⟨4102989661472172709444787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735326440981448472963191 4102989661472172709444787)
              ·
                refine ⟨6154484492208259064167181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102989661472172709444787 6154484492208259064167181)
                ·
                  refine ⟨2307931684578097149062693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6154484492208259064167181 2307931684578097149062693)
                  ·
                    refine ⟨432737190858393215449255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2307931684578097149062693 432737190858393215449255)
                    ·
                      rfl

theorem cell22_1264129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1264129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264129 prefixEnd_1264129 := by exact prefixLift 1264129
  have htrace : WordTrace (prefixWord ++ tailWord_1264129) baseStart_1264129 baseEnd_1264129 := by
    simpa [prefixWord, tailWord_1264129, baseEnd_1264129] using wordTrace_append hprefix tailTrace_1264129
  have hstable : (prefixWord ++ tailWord_1264129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264129).length < 2 ^ (prefixWord ++ tailWord_1264129).sum := by decide
  have hdescent : baseEnd_1264129 < baseStart_1264129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264204 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_1264204 : Nat := 118140960795 + 1264204 * 2 ^ 59
def prefixEnd_1264204 : Nat := 4983230072969 + 3 ^ 40 * 1264204 * 2
def baseEnd_1264204 : Nat := 432762864891118019824025

theorem tailTrace_1264204 : CollatzResearch.WordTrace tailWord_1264204 prefixEnd_1264204 432762864891118019824025 := by
  unfold tailWord_1264204
  simp only [CollatzResearch.WordTrace]
  refine ⟨23054653956006145849463833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30739538608008194465951777 23054653956006145849463833)
  ·
    refine ⟨17290990467004609387097875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23054653956006145849463833 17290990467004609387097875)
    ·
      refine ⟨25936485700506914080646813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17290990467004609387097875 25936485700506914080646813)
      ·
        refine ⟨9726182137690092780242555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25936485700506914080646813 9726182137690092780242555)
        ·
          refine ⟨14589273206535139170363833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9726182137690092780242555 14589273206535139170363833)
          ·
            refine ⟨10941954904901354377772875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14589273206535139170363833 10941954904901354377772875)
            ·
              refine ⟨16412932357352031566659313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10941954904901354377772875 16412932357352031566659313)
              ·
                refine ⟨12309699268014023674994485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16412932357352031566659313 12309699268014023674994485)
                ·
                  refine ⟨1154034306376314719530733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12309699268014023674994485 1154034306376314719530733)
                  ·
                    refine ⟨432762864891118019824025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154034306376314719530733 432762864891118019824025)
                    ·
                      rfl

theorem cell22_1264204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_1264204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264204 prefixEnd_1264204 := by exact prefixLift 1264204
  have htrace : WordTrace (prefixWord ++ tailWord_1264204) baseStart_1264204 baseEnd_1264204 := by
    simpa [prefixWord, tailWord_1264204, baseEnd_1264204] using wordTrace_append hprefix tailTrace_1264204
  have hstable : (prefixWord ++ tailWord_1264204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264204).length < 2 ^ (prefixWord ++ tailWord_1264204).sum := by decide
  have hdescent : baseEnd_1264204 < baseStart_1264204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264311 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 1, 5]
def baseStart_1264311 : Nat := 118140960795 + 1264311 * 2 ^ 59
def prefixEnd_1264311 : Nat := 4983230072969 + 3 ^ 40 * 1264311 * 2
def baseEnd_1264311 : Nat := 432799493177805407398697

theorem tailTrace_1264311 : CollatzResearch.WordTrace tailWord_1264311 prefixEnd_1264311 432799493177805407398697 := by
  unfold tailWord_1264311
  simp only [CollatzResearch.WordTrace]
  refine ⟨46113210522624648973072787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30742140348416432648715191 46113210522624648973072787)
  ·
    refine ⟨69169815783936973459609181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46113210522624648973072787 69169815783936973459609181)
    ·
      refine ⟨25938680918976365047353443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69169815783936973459609181 25938680918976365047353443)
      ·
        refine ⟨38908021378464547571030165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25938680918976365047353443 38908021378464547571030165)
        ·
          refine ⟨1823813502115525667392039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38908021378464547571030165 1823813502115525667392039)
          ·
            refine ⟨2735720253173288501088059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823813502115525667392039 2735720253173288501088059)
            ·
              refine ⟨4103580379759932751632089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735720253173288501088059 4103580379759932751632089)
              ·
                refine ⟨3077685284819949563724067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4103580379759932751632089 3077685284819949563724067)
                ·
                  refine ⟨4616527927229924345586101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077685284819949563724067 4616527927229924345586101)
                  ·
                    refine ⟨432799493177805407398697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4616527927229924345586101 432799493177805407398697)
                    ·
                      rfl

theorem cell22_1264311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_1264311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264311 prefixEnd_1264311 := by exact prefixLift 1264311
  have htrace : WordTrace (prefixWord ++ tailWord_1264311) baseStart_1264311 baseEnd_1264311 := by
    simpa [prefixWord, tailWord_1264311, baseEnd_1264311] using wordTrace_append hprefix tailTrace_1264311
  have hstable : (prefixWord ++ tailWord_1264311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264311).length < 2 ^ (prefixWord ++ tailWord_1264311).sum := by decide
  have hdescent : baseEnd_1264311 < baseStart_1264311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264324 : List Nat := [2, 3, 3, 1, 1, 12]
def baseStart_1264324 : Nat := 118140960795 + 1264324 * 2 ^ 59
def prefixEnd_1264324 : Nat := 4983230072969 + 3 ^ 40 * 1264324 * 2
def baseEnd_1264324 : Nat := 5343258559796021071897

theorem tailTrace_1264324 : CollatzResearch.WordTrace tailWord_1264324 prefixEnd_1264324 5343258559796021071897 := by
  unfold tailWord_1264324
  simp only [CollatzResearch.WordTrace]
  refine ⟨23056842335788776096648013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30742456447718368128864017 23056842335788776096648013)
  ·
    refine ⟨8646315875920791036243005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23056842335788776096648013 8646315875920791036243005)
    ·
      refine ⟨3242368453470296638591127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8646315875920791036243005 3242368453470296638591127)
      ·
        refine ⟨4863552680205444957886691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242368453470296638591127 4863552680205444957886691)
        ·
          refine ⟨7295329020308167436830037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863552680205444957886691 7295329020308167436830037)
          ·
            refine ⟨5343258559796021071897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7295329020308167436830037 5343258559796021071897)
            ·
              rfl

theorem cell22_1264324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 12].length) (baseStart_1264324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264324 prefixEnd_1264324 := by exact prefixLift 1264324
  have htrace : WordTrace (prefixWord ++ tailWord_1264324) baseStart_1264324 baseEnd_1264324 := by
    simpa [prefixWord, tailWord_1264324, baseEnd_1264324] using wordTrace_append hprefix tailTrace_1264324
  have hstable : (prefixWord ++ tailWord_1264324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264324).length < 2 ^ (prefixWord ++ tailWord_1264324).sum := by decide
  have hdescent : baseEnd_1264324 < baseStart_1264324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264328 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1264328 : Nat := 118140960795 + 1264328 * 2 ^ 59
def prefixEnd_1264328 : Nat := 4983230072969 + 3 ^ 40 * 1264328 * 2
def baseEnd_1264328 : Nat := 432805312625223029723645

theorem tailTrace_1264328 : CollatzResearch.WordTrace tailWord_1264328 prefixEnd_1264328 432805312625223029723645 := by
  unfold tailWord_1264328
  simp only [CollatzResearch.WordTrace]
  refine ⟨23056915281781530438220819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30742553709042040584294425 23056915281781530438220819)
  ·
    refine ⟨34585372922672295657331229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23056915281781530438220819 34585372922672295657331229)
    ·
      refine ⟨12969514846002110871499211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34585372922672295657331229 12969514846002110871499211)
      ·
        refine ⟨19454272269003166307248817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12969514846002110871499211 19454272269003166307248817)
        ·
          refine ⟨14590704201752374730436613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19454272269003166307248817 14590704201752374730436613)
          ·
            refine ⟨2735757037828570261956865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14590704201752374730436613 2735757037828570261956865)
            ·
              refine ⟨2051817778371427696467649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735757037828570261956865 2051817778371427696467649)
              ·
                refine ⟨1538863333778570772350737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051817778371427696467649 1538863333778570772350737)
                ·
                  refine ⟨1154147500333928079263053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538863333778570772350737 1154147500333928079263053)
                  ·
                    refine ⟨432805312625223029723645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154147500333928079263053 432805312625223029723645)
                    ·
                      rfl

theorem cell22_1264328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1264328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264328 prefixEnd_1264328 := by exact prefixLift 1264328
  have htrace : WordTrace (prefixWord ++ tailWord_1264328) baseStart_1264328 baseEnd_1264328 := by
    simpa [prefixWord, tailWord_1264328, baseEnd_1264328] using wordTrace_append hprefix tailTrace_1264328
  have hstable : (prefixWord ++ tailWord_1264328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264328).length < 2 ^ (prefixWord ++ tailWord_1264328).sum := by decide
  have hdescent : baseEnd_1264328 < baseStart_1264328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264330 : List Nat := [3, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_1264330 : Nat := 118140960795 + 1264330 * 2 ^ 59
def prefixEnd_1264330 : Nat := 4983230072969 + 3 ^ 40 * 1264330 * 2
def baseEnd_1264330 : Nat := 144268665755365230391213

theorem tailTrace_1264330 : CollatzResearch.WordTrace tailWord_1264330 prefixEnd_1264330 144268665755365230391213 := by
  unfold tailWord_1264330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11528475877388953804503611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30742602339703876812009629 11528475877388953804503611)
  ·
    refine ⟨17292713816083430706755417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11528475877388953804503611 17292713816083430706755417)
    ·
      refine ⟨12969535362062573030066563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17292713816083430706755417 12969535362062573030066563)
      ·
        refine ⟨19454303043093859545099845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12969535362062573030066563 19454303043093859545099845)
        ·
          refine ⟨3647681820580098664706221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19454303043093859545099845 3647681820580098664706221)
          ·
            refine ⟨1367880682717536999264833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3647681820580098664706221 1367880682717536999264833)
            ·
              refine ⟨1025910512038152749448625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367880682717536999264833 1025910512038152749448625)
              ·
                refine ⟨769432884028614562086469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025910512038152749448625 769432884028614562086469)
                ·
                  refine ⟨144268665755365230391213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769432884028614562086469 144268665755365230391213)
                  ·
                    rfl

theorem cell22_1264330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_1264330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264330 prefixEnd_1264330 := by exact prefixLift 1264330
  have htrace : WordTrace (prefixWord ++ tailWord_1264330) baseStart_1264330 baseEnd_1264330 := by
    simpa [prefixWord, tailWord_1264330, baseEnd_1264330] using wordTrace_append hprefix tailTrace_1264330
  have hstable : (prefixWord ++ tailWord_1264330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264330).length < 2 ^ (prefixWord ++ tailWord_1264330).sum := by decide
  have hdescent : baseEnd_1264330 < baseStart_1264330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264356 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_1264356 : Nat := 118140960795 + 1264356 * 2 ^ 59
def prefixEnd_1264356 : Nat := 4983230072969 + 3 ^ 40 * 1264356 * 2
def baseEnd_1264356 : Nat := 432814897597440290023559

theorem tailTrace_1264356 : CollatzResearch.WordTrace tailWord_1264356 prefixEnd_1264356 432814897597440290023559 := by
  unfold tailWord_1264356
  simp only [CollatzResearch.WordTrace]
  refine ⟨23057425903730810829230461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30743234538307747772307281 23057425903730810829230461)
  ·
    refine ⟨8646534713899054060961423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23057425903730810829230461 8646534713899054060961423)
    ·
      refine ⟨12969802070848581091442135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8646534713899054060961423 12969802070848581091442135)
      ·
        refine ⟨19454703106272871637163203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12969802070848581091442135 19454703106272871637163203)
        ·
          refine ⟨29182054659409307455744805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19454703106272871637163203 29182054659409307455744805)
          ·
            refine ⟨5471635248639245147952151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29182054659409307455744805 5471635248639245147952151)
            ·
              refine ⟨8207452872958867721928227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471635248639245147952151 8207452872958867721928227)
              ·
                refine ⟨12311179309438301582892341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8207452872958867721928227 12311179309438301582892341)
                ·
                  refine ⟨1154173060259840773396157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12311179309438301582892341 1154173060259840773396157)
                  ·
                    refine ⟨432814897597440290023559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154173060259840773396157 432814897597440290023559)
                    ·
                      rfl

theorem cell22_1264356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_1264356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264356 prefixEnd_1264356 := by exact prefixLift 1264356
  have htrace : WordTrace (prefixWord ++ tailWord_1264356) baseStart_1264356 baseEnd_1264356 := by
    simpa [prefixWord, tailWord_1264356, baseEnd_1264356] using wordTrace_append hprefix tailTrace_1264356
  have hstable : (prefixWord ++ tailWord_1264356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264356).length < 2 ^ (prefixWord ++ tailWord_1264356).sum := by decide
  have hdescent : baseEnd_1264356 < baseStart_1264356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264360 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 2, 4]
def baseStart_1264360 : Nat := 118140960795 + 1264360 * 2 ^ 59
def prefixEnd_1264360 : Nat := 4983230072969 + 3 ^ 40 * 1264360 * 2
def baseEnd_1264360 : Nat := 432816266879185612923547

theorem tailTrace_1264360 : CollatzResearch.WordTrace tailWord_1264360 prefixEnd_1264360 432816266879185612923547 := by
  unfold tailWord_1264360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23057498849723565170803267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30743331799631420227737689 23057498849723565170803267)
  ·
    refine ⟨34586248274585347756204901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23057498849723565170803267 34586248274585347756204901)
    ·
      refine ⟨6484921551484752704288419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34586248274585347756204901 6484921551484752704288419)
      ·
        refine ⟨9727382327227129056432629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6484921551484752704288419 9727382327227129056432629)
        ·
          refine ⟨911942093177543349040559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9727382327227129056432629 911942093177543349040559)
          ·
            refine ⟨1367913139766315023560839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911942093177543349040559 1367913139766315023560839)
            ·
              refine ⟨2051869709649472535341259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367913139766315023560839 2051869709649472535341259)
              ·
                refine ⟨3077804564474208803011889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051869709649472535341259 3077804564474208803011889)
                ·
                  refine ⟨2308353423355656602258917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3077804564474208803011889 2308353423355656602258917)
                  ·
                    refine ⟨432816266879185612923547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2308353423355656602258917 432816266879185612923547)
                    ·
                      rfl

theorem cell22_1264360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_1264360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264360 prefixEnd_1264360 := by exact prefixLift 1264360
  have htrace : WordTrace (prefixWord ++ tailWord_1264360) baseStart_1264360 baseEnd_1264360 := by
    simpa [prefixWord, tailWord_1264360, baseEnd_1264360] using wordTrace_append hprefix tailTrace_1264360
  have hstable : (prefixWord ++ tailWord_1264360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264360).length < 2 ^ (prefixWord ++ tailWord_1264360).sum := by decide
  have hdescent : baseEnd_1264360 < baseStart_1264360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264369 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 7]
def baseStart_1264369 : Nat := 118140960795 + 1264369 * 2 ^ 59
def prefixEnd_1264369 : Nat := 4983230072969 + 3 ^ 40 * 1264369 * 2
def baseEnd_1264369 : Nat := 144273115921037529816173

theorem tailTrace_1264369 : CollatzResearch.WordTrace tailWord_1264369 prefixEnd_1264369 144273115921037529816173 := by
  unfold tailWord_1264369
  simp only [CollatzResearch.WordTrace]
  refine ⟨46115325956414524878684161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30743550637609683252456107 46115325956414524878684161)
  ·
    refine ⟨34586494467310893659013121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46115325956414524878684161 34586494467310893659013121)
    ·
      refine ⟨25939870850483170244259841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34586494467310893659013121 25939870850483170244259841)
      ·
        refine ⟨19454903137862377683194881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25939870850483170244259841 19454903137862377683194881)
        ·
          refine ⟨14591177353396783262396161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19454903137862377683194881 14591177353396783262396161)
          ·
            refine ⟨10943383015047587446797121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14591177353396783262396161 10943383015047587446797121)
            ·
              refine ⟨8207537261285690585097841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10943383015047587446797121 8207537261285690585097841)
              ·
                refine ⟨6155652945964267938823381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8207537261285690585097841 6155652945964267938823381)
                ·
                  refine ⟨144273115921037529816173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6155652945964267938823381 144273115921037529816173)
                  ·
                    rfl

theorem cell22_1264369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_1264369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264369 prefixEnd_1264369 := by exact prefixLift 1264369
  have htrace : WordTrace (prefixWord ++ tailWord_1264369) baseStart_1264369 baseEnd_1264369 := by
    simpa [prefixWord, tailWord_1264369, baseEnd_1264369] using wordTrace_append hprefix tailTrace_1264369
  have hstable : (prefixWord ++ tailWord_1264369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264369).length < 2 ^ (prefixWord ++ tailWord_1264369).sum := by decide
  have hdescent : baseEnd_1264369 < baseStart_1264369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264454 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1264454 : Nat := 118140960795 + 1264454 * 2 ^ 59
def prefixEnd_1264454 : Nat := 4983230072969 + 3 ^ 40 * 1264454 * 2
def baseEnd_1264454 : Nat := 144282815000066900357753

theorem tailTrace_1264454 : CollatzResearch.WordTrace tailWord_1264454 prefixEnd_1264454 144282815000066900357753 := by
  unfold tailWord_1264454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441200817534580762360263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30745617440737722930352277 1441200817534580762360263)
  ·
    refine ⟨2161801226301871143540395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1441200817534580762360263 2161801226301871143540395)
    ·
      refine ⟨3242701839452806715310593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2161801226301871143540395 3242701839452806715310593)
      ·
        refine ⟨2432026379589605036482945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3242701839452806715310593 2432026379589605036482945)
        ·
          refine ⟨1824019784692203777362209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2432026379589605036482945 1824019784692203777362209)
          ·
            refine ⟨1368014838519152833021657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824019784692203777362209 1368014838519152833021657)
            ·
              refine ⟨1026011128889364624766243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368014838519152833021657 1026011128889364624766243)
              ·
                refine ⟨1539016693334046937149365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026011128889364624766243 1539016693334046937149365)
                ·
                  refine ⟨144282815000066900357753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1539016693334046937149365 144282815000066900357753)
                  ·
                    rfl

theorem cell22_1264454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1264454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264454 prefixEnd_1264454 := by exact prefixLift 1264454
  have htrace : WordTrace (prefixWord ++ tailWord_1264454) baseStart_1264454 baseEnd_1264454 := by
    simpa [prefixWord, tailWord_1264454, baseEnd_1264454] using wordTrace_append hprefix tailTrace_1264454
  have hstable : (prefixWord ++ tailWord_1264454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264454).length < 2 ^ (prefixWord ++ tailWord_1264454).sum := by decide
  have hdescent : baseEnd_1264454 < baseStart_1264454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264600 : List Nat := [2, 1, 2, 2, 2, 3, 3, 3, 4]
def baseStart_1264600 : Nat := 118140960795 + 1264600 * 2 ^ 59
def prefixEnd_1264600 : Nat := 4983230072969 + 3 ^ 40 * 1264600 * 2
def baseEnd_1264600 : Nat := 144299474594634995640937

theorem tailTrace_1264600 : CollatzResearch.WordTrace tailWord_1264600 prefixEnd_1264600 144299474594634995640937 := by
  unfold tailWord_1264600
  simp only [CollatzResearch.WordTrace]
  refine ⟨23061875609288825665171627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30749167479051767553562169 23061875609288825665171627)
  ·
    refine ⟨34592813413933238497757441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23061875609288825665171627 34592813413933238497757441)
    ·
      refine ⟨25944610060449928873318081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34592813413933238497757441 25944610060449928873318081)
      ·
        refine ⟨19458457545337446654988561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25944610060449928873318081 19458457545337446654988561)
        ·
          refine ⟨14593843159003084991241421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19458457545337446654988561 14593843159003084991241421)
          ·
            refine ⟨5472691184626156871715533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14593843159003084991241421 5472691184626156871715533)
            ·
              refine ⟨2052259194234808826893325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5472691184626156871715533 2052259194234808826893325)
              ·
                refine ⟨769597197838053310084997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2052259194234808826893325 769597197838053310084997)
                ·
                  refine ⟨144299474594634995640937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769597197838053310084997 144299474594634995640937)
                  ·
                    rfl

theorem cell22_1264600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_1264600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264600 prefixEnd_1264600 := by exact prefixLift 1264600
  have htrace : WordTrace (prefixWord ++ tailWord_1264600) baseStart_1264600 baseEnd_1264600 := by
    simpa [prefixWord, tailWord_1264600, baseEnd_1264600] using wordTrace_append hprefix tailTrace_1264600
  have hstable : (prefixWord ++ tailWord_1264600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264600).length < 2 ^ (prefixWord ++ tailWord_1264600).sum := by decide
  have hdescent : baseEnd_1264600 < baseStart_1264600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264615 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1264615 : Nat := 118140960795 + 1264615 * 2 ^ 59
def prefixEnd_1264615 : Nat := 4983230072969 + 3 ^ 40 * 1264615 * 2
def baseEnd_1264615 : Nat := 432903558590449947797765

theorem tailTrace_1264615 : CollatzResearch.WordTrace tailWord_1264615 prefixEnd_1264615 432903558590449947797765 := by
  unfold tailWord_1264615
  simp only [CollatzResearch.WordTrace]
  refine ⟨46124298313523308892139299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30749532209015539261426199 46124298313523308892139299)
  ·
    refine ⟨69186447470284963338208949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46124298313523308892139299 69186447470284963338208949)
    ·
      refine ⟨6486229450339215312957089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69186447470284963338208949 6486229450339215312957089)
      ·
        refine ⟨4864672087754411484717817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6486229450339215312957089 4864672087754411484717817)
        ·
          refine ⟨3648504065815808613538363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4864672087754411484717817 3648504065815808613538363)
          ·
            refine ⟨5472756098723712920307545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648504065815808613538363 5472756098723712920307545)
            ·
              refine ⟨4104567074042784690230659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5472756098723712920307545 4104567074042784690230659)
              ·
                refine ⟨6156850611064177035345989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104567074042784690230659 6156850611064177035345989)
                ·
                  refine ⟨1154409489574533194127373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6156850611064177035345989 1154409489574533194127373)
                  ·
                    refine ⟨432903558590449947797765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154409489574533194127373 432903558590449947797765)
                    ·
                      rfl

theorem cell22_1264615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1264615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264615 prefixEnd_1264615 := by exact prefixLift 1264615
  have htrace : WordTrace (prefixWord ++ tailWord_1264615) baseStart_1264615 baseEnd_1264615 := by
    simpa [prefixWord, tailWord_1264615, baseEnd_1264615] using wordTrace_append hprefix tailTrace_1264615
  have hstable : (prefixWord ++ tailWord_1264615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264615).length < 2 ^ (prefixWord ++ tailWord_1264615).sum := by decide
  have hdescent : baseEnd_1264615 < baseStart_1264615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264677 : List Nat := [1, 3, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_1264677 : Nat := 118140960795 + 1264677 * 2 ^ 59
def prefixEnd_1264677 : Nat := 4983230072969 + 3 ^ 40 * 1264677 * 2
def baseEnd_1264677 : Nat := 432924782457502452747575

theorem tailTrace_1264677 : CollatzResearch.WordTrace tailWord_1264677 prefixEnd_1264677 432924782457502452747575 := by
  unfold tailWord_1264677
  simp only [CollatzResearch.WordTrace]
  refine ⟨46126559639298693480896285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30751039759532462320597523 46126559639298693480896285)
  ·
    refine ⟨17297459864737010055336107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46126559639298693480896285 17297459864737010055336107)
    ·
      refine ⟨25946189797105515083004161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17297459864737010055336107 25946189797105515083004161)
      ·
        refine ⟨19459642347829136312253121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25946189797105515083004161 19459642347829136312253121)
        ·
          refine ⟨14594731760871852234189841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19459642347829136312253121 14594731760871852234189841)
          ·
            refine ⟨10946048820653889175642381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14594731760871852234189841 10946048820653889175642381)
            ·
              refine ⟨4104768307745208440865893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10946048820653889175642381 4104768307745208440865893)
              ·
                refine ⟨769644057702226582662355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4104768307745208440865893 769644057702226582662355)
                ·
                  refine ⟨1154466086553339873993533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769644057702226582662355 1154466086553339873993533)
                  ·
                    refine ⟨432924782457502452747575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154466086553339873993533 432924782457502452747575)
                    ·
                      rfl

theorem cell22_1264677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_1264677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264677 prefixEnd_1264677 := by exact prefixLift 1264677
  have htrace : WordTrace (prefixWord ++ tailWord_1264677) baseStart_1264677 baseEnd_1264677 := by
    simpa [prefixWord, tailWord_1264677, baseEnd_1264677] using wordTrace_append hprefix tailTrace_1264677
  have hstable : (prefixWord ++ tailWord_1264677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264677).length < 2 ^ (prefixWord ++ tailWord_1264677).sum := by decide
  have hdescent : baseEnd_1264677 < baseStart_1264677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264688 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_1264688 : Nat := 118140960795 + 1264688 * 2 ^ 59
def prefixEnd_1264688 : Nat := 4983230072969 + 3 ^ 40 * 1264688 * 2
def baseEnd_1264688 : Nat := 432928547982302090722541

theorem tailTrace_1264688 : CollatzResearch.WordTrace tailWord_1264688 prefixEnd_1264688 432928547982302090722541 := by
  unfold tailWord_1264688
  simp only [CollatzResearch.WordTrace]
  refine ⟨23063480421129421179773359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30751307228172561573031145 23063480421129421179773359)
  ·
    refine ⟨34595220631694131769660039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23063480421129421179773359 34595220631694131769660039)
    ·
      refine ⟨51892830947541197654490059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34595220631694131769660039 51892830947541197654490059)
      ·
        refine ⟨77839246421311796481735089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51892830947541197654490059 77839246421311796481735089)
        ·
          refine ⟨58379434815983847361301317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77839246421311796481735089 58379434815983847361301317)
          ·
            refine ⟨10946144027996971380243997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58379434815983847361301317 10946144027996971380243997)
            ·
              refine ⟨4104804010498864267591499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10946144027996971380243997 4104804010498864267591499)
              ·
                refine ⟨6157206015748296401387249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104804010498864267591499 6157206015748296401387249)
                ·
                  refine ⟨4617904511811222301040437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157206015748296401387249 4617904511811222301040437)
                  ·
                    refine ⟨432928547982302090722541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4617904511811222301040437 432928547982302090722541)
                    ·
                      rfl

theorem cell22_1264688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_1264688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264688 prefixEnd_1264688 := by exact prefixLift 1264688
  have htrace : WordTrace (prefixWord ++ tailWord_1264688) baseStart_1264688 baseEnd_1264688 := by
    simpa [prefixWord, tailWord_1264688, baseEnd_1264688] using wordTrace_append hprefix tailTrace_1264688
  have hstable : (prefixWord ++ tailWord_1264688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264688).length < 2 ^ (prefixWord ++ tailWord_1264688).sum := by decide
  have hdescent : baseEnd_1264688 < baseStart_1264688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264718 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1264718 : Nat := 118140960795 + 1264718 * 2 ^ 59
def prefixEnd_1264718 : Nat := 4983230072969 + 3 ^ 40 * 1264718 * 2
def baseEnd_1264718 : Nat := 144312939198464004157483

theorem tailTrace_1264718 : CollatzResearch.WordTrace tailWord_1264718 prefixEnd_1264718 144312939198464004157483 := by
  unfold tailWord_1264718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766006879018769685392351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30752036688100104988759205 5766006879018769685392351)
  ·
    refine ⟨8649010318528154528088527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5766006879018769685392351 8649010318528154528088527)
    ·
      refine ⟨12973515477792231792132791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8649010318528154528088527 12973515477792231792132791)
      ·
        refine ⟨19460273216688347688199187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12973515477792231792132791 19460273216688347688199187)
        ·
          refine ⟨29190409825032521532298781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19460273216688347688199187 29190409825032521532298781)
          ·
            refine ⟨10946403684387195574612043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29190409825032521532298781 10946403684387195574612043)
            ·
              refine ⟨16419605526580793361918065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946403684387195574612043 16419605526580793361918065)
              ·
                refine ⟨12314704144935595021438549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16419605526580793361918065 12314704144935595021438549)
                ·
                  refine ⟨144312939198464004157483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12314704144935595021438549 144312939198464004157483)
                  ·
                    rfl

theorem cell22_1264718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1264718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264718 prefixEnd_1264718 := by exact prefixLift 1264718
  have htrace : WordTrace (prefixWord ++ tailWord_1264718) baseStart_1264718 baseEnd_1264718 := by
    simpa [prefixWord, tailWord_1264718, baseEnd_1264718] using wordTrace_append hprefix tailTrace_1264718
  have hstable : (prefixWord ++ tailWord_1264718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264718).length < 2 ^ (prefixWord ++ tailWord_1264718).sum := by decide
  have hdescent : baseEnd_1264718 < baseStart_1264718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264735 : List Nat := [1, 1, 2, 3, 1, 1, 3, 6, 4]
def baseStart_1264735 : Nat := 118140960795 + 1264735 * 2 ^ 59
def prefixEnd_1264735 : Nat := 4983230072969 + 3 ^ 40 * 1264735 * 2
def baseEnd_1264735 : Nat := 144314879014269878265799

theorem tailTrace_1264735 : CollatzResearch.WordTrace tailWord_1264735 prefixEnd_1264735 144314879014269878265799 := by
  unfold tailWord_1264735
  simp only [CollatzResearch.WordTrace]
  refine ⟨46128675073088569386507659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30752450048725712924338439 46128675073088569386507659)
  ·
    refine ⟨69193012609632854079761489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46128675073088569386507659 69193012609632854079761489)
    ·
      refine ⟨51894759457224640559821117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69193012609632854079761489 51894759457224640559821117)
      ·
        refine ⟨19460534796459240209932919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51894759457224640559821117 19460534796459240209932919)
        ·
          refine ⟨29190802194688860314899379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19460534796459240209932919 29190802194688860314899379)
          ·
            refine ⟨43786203292033290472349069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29190802194688860314899379 43786203292033290472349069)
            ·
              refine ⟨16419826234512483927130901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43786203292033290472349069 16419826234512483927130901)
              ·
                refine ⟨769679354742772684084261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16419826234512483927130901 769679354742772684084261)
                ·
                  refine ⟨144314879014269878265799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769679354742772684084261 144314879014269878265799)
                  ·
                    rfl

theorem cell22_1264735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 4].length) (baseStart_1264735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264735 prefixEnd_1264735 := by exact prefixLift 1264735
  have htrace : WordTrace (prefixWord ++ tailWord_1264735) baseStart_1264735 baseEnd_1264735 := by
    simpa [prefixWord, tailWord_1264735, baseEnd_1264735] using wordTrace_append hprefix tailTrace_1264735
  have hstable : (prefixWord ++ tailWord_1264735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264735).length < 2 ^ (prefixWord ++ tailWord_1264735).sum := by decide
  have hdescent : baseEnd_1264735 < baseStart_1264735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264748 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1264748 : Nat := 118140960795 + 1264748 * 2 ^ 59
def prefixEnd_1264748 : Nat := 4983230072969 + 3 ^ 40 * 1264748 * 2
def baseEnd_1264748 : Nat := 432949087208481934222357

theorem tailTrace_1264748 : CollatzResearch.WordTrace tailWord_1264748 prefixEnd_1264748 432949087208481934222357 := by
  unfold tailWord_1264748
  simp only [CollatzResearch.WordTrace]
  refine ⟨23064574611020736303365449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30752766148027648404487265 23064574611020736303365449)
  ·
    refine ⟨17298430958265552227524087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23064574611020736303365449 17298430958265552227524087)
    ·
      refine ⟨25947646437398328341286131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17298430958265552227524087 25947646437398328341286131)
      ·
        refine ⟨38921469656097492511929197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25947646437398328341286131 38921469656097492511929197)
        ·
          refine ⟨14595551121036559691973449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38921469656097492511929197 14595551121036559691973449)
          ·
            refine ⟨10946663340777419768980087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14595551121036559691973449 10946663340777419768980087)
            ·
              refine ⟨16419995011166129653470131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946663340777419768980087 16419995011166129653470131)
              ·
                refine ⟨24629992516749194480205197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16419995011166129653470131 24629992516749194480205197)
                ·
                  refine ⟨9236247193780947930076949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24629992516749194480205197 9236247193780947930076949)
                  ·
                    refine ⟨432949087208481934222357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9236247193780947930076949 432949087208481934222357)
                    ·
                      rfl

theorem cell22_1264748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1264748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264748 prefixEnd_1264748 := by exact prefixLift 1264748
  have htrace : WordTrace (prefixWord ++ tailWord_1264748) baseStart_1264748 baseEnd_1264748 := by
    simpa [prefixWord, tailWord_1264748, baseEnd_1264748] using wordTrace_append hprefix tailTrace_1264748
  have hstable : (prefixWord ++ tailWord_1264748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264748).length < 2 ^ (prefixWord ++ tailWord_1264748).sum := by decide
  have hdescent : baseEnd_1264748 < baseStart_1264748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264765 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_1264765 : Nat := 118140960795 + 1264765 * 2 ^ 59
def prefixEnd_1264765 : Nat := 4983230072969 + 3 ^ 40 * 1264765 * 2
def baseEnd_1264765 : Nat := 432954906655899556547305

theorem tailTrace_1264765 : CollatzResearch.WordTrace tailWord_1264765 prefixEnd_1264765 432954906655899556547305 := by
  unfold tailWord_1264765
  simp only [CollatzResearch.WordTrace]
  refine ⟨46129769262979884510099749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30753179508653256340066499 46129769262979884510099749)
  ·
    refine ⟨8649331736808728345643703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46129769262979884510099749 8649331736808728345643703)
    ·
      refine ⟨12973997605213092518465555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8649331736808728345643703 12973997605213092518465555)
      ·
        refine ⟨19460996407819638777698333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12973997605213092518465555 19460996407819638777698333)
        ·
          refine ⟨7297873652932364541636875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19460996407819638777698333 7297873652932364541636875)
          ·
            refine ⟨10946810479398546812455313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297873652932364541636875 10946810479398546812455313)
            ·
              refine ⟨8210107859548910109341485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10946810479398546812455313 8210107859548910109341485)
              ·
                refine ⟨3078790447330841291003057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8210107859548910109341485 3078790447330841291003057)
                ·
                  refine ⟨2309092835498130968252293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078790447330841291003057 2309092835498130968252293)
                  ·
                    refine ⟨432954906655899556547305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309092835498130968252293 432954906655899556547305)
                    ·
                      rfl

theorem cell22_1264765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_1264765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264765 prefixEnd_1264765 := by exact prefixLift 1264765
  have htrace : WordTrace (prefixWord ++ tailWord_1264765) baseStart_1264765 baseEnd_1264765 := by
    simpa [prefixWord, tailWord_1264765, baseEnd_1264765] using wordTrace_append hprefix tailTrace_1264765
  have hstable : (prefixWord ++ tailWord_1264765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264765).length < 2 ^ (prefixWord ++ tailWord_1264765).sum := by decide
  have hdescent : baseEnd_1264765 < baseStart_1264765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264769 : List Nat := [1, 2, 4, 2, 2, 3, 1, 3, 4]
def baseStart_1264769 : Nat := 118140960795 + 1264769 * 2 ^ 59
def prefixEnd_1264769 : Nat := 4983230072969 + 3 ^ 40 * 1264769 * 2
def baseEnd_1264769 : Nat := 144318758645881626482431

theorem tailTrace_1264769 : CollatzResearch.WordTrace tailWord_1264769 prefixEnd_1264769 144318758645881626482431 := by
  unfold tailWord_1264769
  simp only [CollatzResearch.WordTrace]
  refine ⟨46129915154965393193245361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30753276769976928795496907 46129915154965393193245361)
  ·
    refine ⟨34597436366224044894934021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46129915154965393193245361 34597436366224044894934021)
    ·
      refine ⟨6487019318667008417800129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34597436366224044894934021 6487019318667008417800129)
      ·
        refine ⟨4865264489000256313350097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6487019318667008417800129 4865264489000256313350097)
        ·
          refine ⟨3648948366750192235012573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4865264489000256313350097 3648948366750192235012573)
          ·
            refine ⟨1368355637531322088129715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3648948366750192235012573 1368355637531322088129715)
            ·
              refine ⟨2052533456296983132194573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368355637531322088129715 2052533456296983132194573)
              ·
                refine ⟨769700046111368674572965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2052533456296983132194573 769700046111368674572965)
                ·
                  refine ⟨144318758645881626482431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 769700046111368674572965 144318758645881626482431)
                  ·
                    rfl

theorem cell22_1264769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_1264769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264769 prefixEnd_1264769 := by exact prefixLift 1264769
  have htrace : WordTrace (prefixWord ++ tailWord_1264769) baseStart_1264769 baseEnd_1264769 := by
    simpa [prefixWord, tailWord_1264769, baseEnd_1264769] using wordTrace_append hprefix tailTrace_1264769
  have hstable : (prefixWord ++ tailWord_1264769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264769).length < 2 ^ (prefixWord ++ tailWord_1264769).sum := by decide
  have hdescent : baseEnd_1264769 < baseStart_1264769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264782 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1264782 : Nat := 118140960795 + 1264782 * 2 ^ 59
def prefixEnd_1264782 : Nat := 4983230072969 + 3 ^ 40 * 1264782 * 2
def baseEnd_1264782 : Nat := 432960726103317178872253

theorem tailTrace_1264782 : CollatzResearch.WordTrace tailWord_1264782 prefixEnd_1264782 432960726103317178872253 := by
  unfold tailWord_1264782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766298662989787051683575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30753592869278864275645733 5766298662989787051683575)
  ·
    refine ⟨8649447994484680577525363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5766298662989787051683575 8649447994484680577525363)
    ·
      refine ⟨12974171991727020866288045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8649447994484680577525363 12974171991727020866288045)
      ·
        refine ⟨4865314496897632824858017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12974171991727020866288045 4865314496897632824858017)
        ·
          refine ⟨3648985872673224618643513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4865314496897632824858017 3648985872673224618643513)
          ·
            refine ⟨2736739404504918463982635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648985872673224618643513 2736739404504918463982635)
            ·
              refine ⟨4105109106757377695973953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736739404504918463982635 4105109106757377695973953)
              ·
                refine ⟨3078831830068033271980465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4105109106757377695973953 3078831830068033271980465)
                ·
                  refine ⟨2309123872551024953985349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078831830068033271980465 2309123872551024953985349)
                  ·
                    refine ⟨432960726103317178872253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309123872551024953985349 432960726103317178872253)
                    ·
                      rfl

theorem cell22_1264782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1264782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264782 prefixEnd_1264782 := by exact prefixLift 1264782
  have htrace : WordTrace (prefixWord ++ tailWord_1264782) baseStart_1264782 baseEnd_1264782 := by
    simpa [prefixWord, tailWord_1264782, baseEnd_1264782] using wordTrace_append hprefix tailTrace_1264782
  have hstable : (prefixWord ++ tailWord_1264782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264782).length < 2 ^ (prefixWord ++ tailWord_1264782).sum := by decide
  have hdescent : baseEnd_1264782 < baseStart_1264782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264842 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_1264842 : Nat := 118140960795 + 1264842 * 2 ^ 59
def prefixEnd_1264842 : Nat := 4983230072969 + 3 ^ 40 * 1264842 * 2
def baseEnd_1264842 : Nat := 144327088443165674124023

theorem tailTrace_1264842 : CollatzResearch.WordTrace tailWord_1264842 prefixEnd_1264842 144327088443165674124023 := by
  unfold tailWord_1264842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533144420925231665163195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30755051789133951107101853 11533144420925231665163195)
  ·
    refine ⟨17299716631387847497744793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11533144420925231665163195 17299716631387847497744793)
    ·
      refine ⟨12974787473540885623308595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17299716631387847497744793 12974787473540885623308595)
      ·
        refine ⟨19462181210311328434962893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12974787473540885623308595 19462181210311328434962893)
        ·
          refine ⟨7298317953866748163111085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19462181210311328434962893 7298317953866748163111085)
          ·
            refine ⟨2736869232700030561166657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7298317953866748163111085 2736869232700030561166657)
            ·
              refine ⟨2052651924525022920874993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736869232700030561166657 2052651924525022920874993)
              ·
                refine ⟨1539488943393767190656245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052651924525022920874993 1539488943393767190656245)
                ·
                  refine ⟨144327088443165674124023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1539488943393767190656245 144327088443165674124023)
                  ·
                    rfl

theorem cell22_1264842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_1264842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264842 prefixEnd_1264842 := by exact prefixLift 1264842
  have htrace : WordTrace (prefixWord ++ tailWord_1264842) baseStart_1264842 baseEnd_1264842 := by
    simpa [prefixWord, tailWord_1264842, baseEnd_1264842] using wordTrace_append hprefix tailTrace_1264842
  have hstable : (prefixWord ++ tailWord_1264842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264842).length < 2 ^ (prefixWord ++ tailWord_1264842).sum := by decide
  have hdescent : baseEnd_1264842 < baseStart_1264842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264846 : List Nat := [4, 1, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_1264846 : Nat := 118140960795 + 1264846 * 2 ^ 59
def prefixEnd_1264846 : Nat := 4983230072969 + 3 ^ 40 * 1264846 * 2
def baseEnd_1264846 : Nat := 432982634611242345272057

theorem tailTrace_1264846 : CollatzResearch.WordTrace tailWord_1264846 prefixEnd_1264846 432982634611242345272057 := by
  unfold tailWord_1264846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766590446960804417974799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30755149050457623562532261 5766590446960804417974799)
  ·
    refine ⟨8649885670441206626962199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5766590446960804417974799 8649885670441206626962199)
    ·
      refine ⟨12974828505661809940443299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8649885670441206626962199 12974828505661809940443299)
      ·
        refine ⟨19462242758492714910664949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12974828505661809940443299 19462242758492714910664949)
        ·
          refine ⟨1824585258608692022874839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19462242758492714910664949 1824585258608692022874839)
          ·
            refine ⟨2736877887913038034312259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824585258608692022874839 2736877887913038034312259)
            ·
              refine ⟨4105316831869557051468389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736877887913038034312259 4105316831869557051468389)
              ·
                refine ⟨769746905975541947150323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4105316831869557051468389 769746905975541947150323)
                ·
                  refine ⟨1154620358963312920725485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769746905975541947150323 1154620358963312920725485)
                  ·
                    refine ⟨432982634611242345272057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154620358963312920725485 432982634611242345272057)
                    ·
                      rfl

theorem cell22_1264846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_1264846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264846 prefixEnd_1264846 := by exact prefixLift 1264846
  have htrace : WordTrace (prefixWord ++ tailWord_1264846) baseStart_1264846 baseEnd_1264846 := by
    simpa [prefixWord, tailWord_1264846, baseEnd_1264846] using wordTrace_append hprefix tailTrace_1264846
  have hstable : (prefixWord ++ tailWord_1264846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264846).length < 2 ^ (prefixWord ++ tailWord_1264846).sum := by decide
  have hdescent : baseEnd_1264846 < baseStart_1264846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264855 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 3, 4]
def baseStart_1264855 : Nat := 118140960795 + 1264855 * 2 ^ 59
def prefixEnd_1264855 : Nat := 4983230072969 + 3 ^ 40 * 1264855 * 2
def baseEnd_1264855 : Nat := 432985715495169321797029

theorem tailTrace_1264855 : CollatzResearch.WordTrace tailWord_1264855 prefixEnd_1264855 432985715495169321797029 := by
  unfold tailWord_1264855
  simp only [CollatzResearch.WordTrace]
  refine ⟨46133051832653829880876019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30755367888435886587250679 46133051832653829880876019)
  ·
    refine ⟨69199577748980744821314029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46133051832653829880876019 69199577748980744821314029)
    ·
      refine ⟨25949841655867779307992761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69199577748980744821314029 25949841655867779307992761)
      ·
        refine ⟨19462381241900834480994571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25949841655867779307992761 19462381241900834480994571)
        ·
          refine ⟨29193571862851251721491857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19462381241900834480994571 29193571862851251721491857)
          ·
            refine ⟨21895178897138438791118893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29193571862851251721491857 21895178897138438791118893)
            ·
              refine ⟨8210692086426914546669585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21895178897138438791118893 8210692086426914546669585)
              ·
                refine ⟨6158019064820185910002189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8210692086426914546669585 6158019064820185910002189)
                ·
                  refine ⟨2309257149307569716250821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6158019064820185910002189 2309257149307569716250821)
                  ·
                    refine ⟨432985715495169321797029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309257149307569716250821 432985715495169321797029)
                    ·
                      rfl

theorem cell22_1264855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_1264855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264855 prefixEnd_1264855 := by exact prefixLift 1264855
  have htrace : WordTrace (prefixWord ++ tailWord_1264855) baseStart_1264855 baseEnd_1264855 := by
    simpa [prefixWord, tailWord_1264855, baseEnd_1264855] using wordTrace_append hprefix tailTrace_1264855
  have hstable : (prefixWord ++ tailWord_1264855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264855).length < 2 ^ (prefixWord ++ tailWord_1264855).sum := by decide
  have hdescent : baseEnd_1264855 < baseStart_1264855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264872 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1264872 : Nat := 118140960795 + 1264872 * 2 ^ 59
def prefixEnd_1264872 : Nat := 4983230072969 + 3 ^ 40 * 1264872 * 2
def baseEnd_1264872 : Nat := 432991534942586944121977

theorem tailTrace_1264872 : CollatzResearch.WordTrace tailWord_1264872 prefixEnd_1264872 432991534942586944121977 := by
  unfold tailWord_1264872
  simp only [CollatzResearch.WordTrace]
  refine ⟨23066835936796120892122435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30755781249061494522829913 23066835936796120892122435)
  ·
    refine ⟨34600253905194181338183653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23066835936796120892122435 34600253905194181338183653)
    ·
      refine ⟨6487547607223909000909435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34600253905194181338183653 6487547607223909000909435)
      ·
        refine ⟨9731321410835863501364153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487547607223909000909435 9731321410835863501364153)
        ·
          refine ⟨7298491058126897626023115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9731321410835863501364153 7298491058126897626023115)
          ·
            refine ⟨10947736587190346439034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7298491058126897626023115 10947736587190346439034673)
            ·
              refine ⟨8210802440392759829276005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10947736587190346439034673 8210802440392759829276005)
              ·
                refine ⟨1539525457573642467989251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8210802440392759829276005 1539525457573642467989251)
                ·
                  refine ⟨2309288186360463701983877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539525457573642467989251 2309288186360463701983877)
                  ·
                    refine ⟨432991534942586944121977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309288186360463701983877 432991534942586944121977)
                    ·
                      rfl

theorem cell22_1264872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1264872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264872 prefixEnd_1264872 := by exact prefixLift 1264872
  have htrace : WordTrace (prefixWord ++ tailWord_1264872) baseStart_1264872 baseEnd_1264872 := by
    simpa [prefixWord, tailWord_1264872, baseEnd_1264872] using wordTrace_append hprefix tailTrace_1264872
  have hstable : (prefixWord ++ tailWord_1264872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264872).length < 2 ^ (prefixWord ++ tailWord_1264872).sum := by decide
  have hdescent : baseEnd_1264872 < baseStart_1264872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264960 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 7]
def baseStart_1264960 : Nat := 118140960795 + 1264960 * 2 ^ 59
def prefixEnd_1264960 : Nat := 4983230072969 + 3 ^ 40 * 1264960 * 2
def baseEnd_1264960 : Nat := 144340553046994682640569

theorem tailTrace_1264960 : CollatzResearch.WordTrace tailWord_1264960 prefixEnd_1264960 144340553046994682640569 := by
  unfold tailWord_1264960
  simp only [CollatzResearch.WordTrace]
  refine ⟨23068440748636716406724167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30757920998182288542298889 23068440748636716406724167)
  ·
    refine ⟨34602661122955074610086251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23068440748636716406724167 34602661122955074610086251)
    ·
      refine ⟨51903991684432611915129377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34602661122955074610086251 51903991684432611915129377)
      ·
        refine ⟨38927993763324458936347033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51903991684432611915129377 38927993763324458936347033)
        ·
          refine ⟨29195995322493344202260275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38927993763324458936347033 29195995322493344202260275)
          ·
            refine ⟨43793992983740016303390413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29195995322493344202260275 43793992983740016303390413)
            ·
              refine ⟨16422747368902506113771405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43793992983740016303390413 16422747368902506113771405)
              ·
                refine ⟨6158530263338439792664277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16422747368902506113771405 6158530263338439792664277)
                ·
                  refine ⟨144340553046994682640569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6158530263338439792664277 144340553046994682640569)
                  ·
                    rfl

theorem cell22_1264960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_1264960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264960 prefixEnd_1264960 := by exact prefixLift 1264960
  have htrace : WordTrace (prefixWord ++ tailWord_1264960) baseStart_1264960 baseEnd_1264960 := by
    simpa [prefixWord, tailWord_1264960, baseEnd_1264960] using wordTrace_append hprefix tailTrace_1264960
  have hstable : (prefixWord ++ tailWord_1264960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264960).length < 2 ^ (prefixWord ++ tailWord_1264960).sum := by decide
  have hdescent : baseEnd_1264960 < baseStart_1264960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264975 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 6, 5]
def baseStart_1264975 : Nat := 118140960795 + 1264975 * 2 ^ 59
def prefixEnd_1264975 : Nat := 4983230072969 + 3 ^ 40 * 1264975 * 2
def baseEnd_1264975 : Nat := 433026793947529008796661

theorem tailTrace_1264975 : CollatzResearch.WordTrace tailWord_1264975 prefixEnd_1264975 433026793947529008796661 := by
  unfold tailWord_1264975
  simp only [CollatzResearch.WordTrace]
  refine ⟨46137428592219090375244379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30758285728146060250162919 46137428592219090375244379)
  ·
    refine ⟨69206142888328635562866569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46137428592219090375244379 69206142888328635562866569)
    ·
      refine ⟨51904607166246476672149927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69206142888328635562866569 51904607166246476672149927)
      ·
        refine ⟨77856910749369715008224891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51904607166246476672149927 77856910749369715008224891)
        ·
          refine ⟨116785366124054572512337337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77856910749369715008224891 116785366124054572512337337)
          ·
            refine ⟨87589024593040929384253003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116785366124054572512337337 87589024593040929384253003)
            ·
              refine ⟨131383536889561394076379505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87589024593040929384253003 131383536889561394076379505)
              ·
                refine ⟨98537652667171045557284629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131383536889561394076379505 98537652667171045557284629)
                ·
                  refine ⟨4618952468773642760497717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98537652667171045557284629 4618952468773642760497717)
                  ·
                    refine ⟨433026793947529008796661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4618952468773642760497717 433026793947529008796661)
                    ·
                      rfl

theorem cell22_1264975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_1264975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264975 prefixEnd_1264975 := by exact prefixLift 1264975
  have htrace : WordTrace (prefixWord ++ tailWord_1264975) baseStart_1264975 baseEnd_1264975 := by
    simpa [prefixWord, tailWord_1264975, baseEnd_1264975] using wordTrace_append hprefix tailTrace_1264975
  have hstable : (prefixWord ++ tailWord_1264975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264975).length < 2 ^ (prefixWord ++ tailWord_1264975).sum := by decide
  have hdescent : baseEnd_1264975 < baseStart_1264975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264977 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 5]
def baseStart_1264977 : Nat := 118140960795 + 1264977 * 2 ^ 59
def prefixEnd_1264977 : Nat := 4983230072969 + 3 ^ 40 * 1264977 * 2
def baseEnd_1264977 : Nat := 144342492862800556748885

theorem tailTrace_1264977 : CollatzResearch.WordTrace tailWord_1264977 prefixEnd_1264977 144342492862800556748885 := by
  unfold tailWord_1264977
  simp only [CollatzResearch.WordTrace]
  refine ⟨46137501538211844716817185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30758334358807896477878123 46137501538211844716817185)
  ·
    refine ⟨34603126153658883537612889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46137501538211844716817185 34603126153658883537612889)
    ·
      refine ⟨25952344615244162653209667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34603126153658883537612889 25952344615244162653209667)
      ·
        refine ⟨38928516922866243979814501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25952344615244162653209667 38928516922866243979814501)
        ·
          refine ⟨7299096923037420746215219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38928516922866243979814501 7299096923037420746215219)
          ·
            refine ⟨10948645384556131119322829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7299096923037420746215219 10948645384556131119322829)
            ·
              refine ⟨4105742019208549169746061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10948645384556131119322829 4105742019208549169746061)
              ·
                refine ⟨1539653257203205938654773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4105742019208549169746061 1539653257203205938654773)
                ·
                  refine ⟨144342492862800556748885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1539653257203205938654773 144342492862800556748885)
                  ·
                    rfl

theorem cell22_1264977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_1264977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1264977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1264977 prefixEnd_1264977 := by exact prefixLift 1264977
  have htrace : WordTrace (prefixWord ++ tailWord_1264977) baseStart_1264977 baseEnd_1264977 := by
    simpa [prefixWord, tailWord_1264977, baseEnd_1264977] using wordTrace_append hprefix tailTrace_1264977
  have hstable : (prefixWord ++ tailWord_1264977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264977).length < 2 ^ (prefixWord ++ tailWord_1264977).sum := by decide
  have hdescent : baseEnd_1264977 < baseStart_1264977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265026 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1265026 : Nat := 118140960795 + 1265026 * 2 ^ 59
def prefixEnd_1265026 : Nat := 4983230072969 + 3 ^ 40 * 1265026 * 2
def baseEnd_1265026 : Nat := 433044252289781875771505

theorem tailTrace_1265026 : CollatzResearch.WordTrace tailWord_1265026 prefixEnd_1265026 433044252289781875771505 := by
  unfold tailWord_1265026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534822178758581521337733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30759525810022884056900621 11534822178758581521337733)
  ·
    refine ⟨2162779158517234035250825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11534822178758581521337733 2162779158517234035250825)
    ·
      refine ⟨1622084368887925526438119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2162779158517234035250825 1622084368887925526438119)
      ·
        refine ⟨2433126553331888289657179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622084368887925526438119 2433126553331888289657179)
        ·
          refine ⟨3649689829997832434485769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2433126553331888289657179 3649689829997832434485769)
          ·
            refine ⟨2737267372498374325864327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649689829997832434485769 2737267372498374325864327)
            ·
              refine ⟨4105901058747561488796491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737267372498374325864327 4105901058747561488796491)
              ·
                refine ⟨6158851588121342233194737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105901058747561488796491 6158851588121342233194737)
                ·
                  refine ⟨4619138691091006674896053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6158851588121342233194737 4619138691091006674896053)
                  ·
                    refine ⟨433044252289781875771505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4619138691091006674896053 433044252289781875771505)
                    ·
                      rfl

theorem cell22_1265026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1265026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265026 prefixEnd_1265026 := by exact prefixLift 1265026
  have htrace : WordTrace (prefixWord ++ tailWord_1265026) baseStart_1265026 baseEnd_1265026 := by
    simpa [prefixWord, tailWord_1265026, baseEnd_1265026] using wordTrace_append hprefix tailTrace_1265026
  have hstable : (prefixWord ++ tailWord_1265026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265026).length < 2 ^ (prefixWord ++ tailWord_1265026).sum := by decide
  have hdescent : baseEnd_1265026 < baseStart_1265026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265058 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1265058 : Nat := 118140960795 + 1265058 * 2 ^ 59
def prefixEnd_1265058 : Nat := 4983230072969 + 3 ^ 40 * 1265058 * 2
def baseEnd_1265058 : Nat := 433055206543744458971407

theorem tailTrace_1265058 : CollatzResearch.WordTrace tailWord_1265058 prefixEnd_1265058 433055206543744458971407 := by
  unfold tailWord_1265058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11535113962729598887628957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30760303900612263700343885 11535113962729598887628957)
  ·
    refine ⟨4325667736023599582860859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11535113962729598887628957 4325667736023599582860859)
    ·
      refine ⟨6488501604035399374291289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325667736023599582860859 6488501604035399374291289)
      ·
        refine ⟨4866376203026549530718467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6488501604035399374291289 4866376203026549530718467)
        ·
          refine ⟨7299564304539824296077701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4866376203026549530718467 7299564304539824296077701)
          ·
            refine ⟨1368668307101217055514569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7299564304539824296077701 1368668307101217055514569)
            ·
              refine ⟨1026501230325912791635927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368668307101217055514569 1026501230325912791635927)
              ·
                refine ⟨1539751845488869187453891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026501230325912791635927 1539751845488869187453891)
                ·
                  refine ⟨2309627768233303781180837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539751845488869187453891 2309627768233303781180837)
                  ·
                    refine ⟨433055206543744458971407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309627768233303781180837 433055206543744458971407)
                    ·
                      rfl

theorem cell22_1265058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1265058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265058 prefixEnd_1265058 := by exact prefixLift 1265058
  have htrace : WordTrace (prefixWord ++ tailWord_1265058) baseStart_1265058 baseEnd_1265058 := by
    simpa [prefixWord, tailWord_1265058, baseEnd_1265058] using wordTrace_append hprefix tailTrace_1265058
  have hstable : (prefixWord ++ tailWord_1265058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265058).length < 2 ^ (prefixWord ++ tailWord_1265058).sum := by decide
  have hdescent : baseEnd_1265058 < baseStart_1265058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265099 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 3, 3]
def baseStart_1265099 : Nat := 118140960795 + 1265099 * 2 ^ 59
def prefixEnd_1265099 : Nat := 4983230072969 + 3 ^ 40 * 1265099 * 2
def baseEnd_1265099 : Nat := 433069241681634018696281

theorem tailTrace_1265099 : CollatzResearch.WordTrace tailWord_1265099 prefixEnd_1265099 433069241681634018696281 := by
  unfold tailWord_1265099
  simp only [CollatzResearch.WordTrace]
  refine ⟨46141951243769859552758351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30761300829179906368505567 46141951243769859552758351)
  ·
    refine ⟨69212926865654789329137527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46141951243769859552758351 69212926865654789329137527)
    ·
      refine ⟨103819390298482183993706291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69212926865654789329137527 103819390298482183993706291)
      ·
        refine ⟨155729085447723275990559437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103819390298482183993706291 155729085447723275990559437)
        ·
          refine ⟨58398407042896228496459789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155729085447723275990559437 58398407042896228496459789)
          ·
            refine ⟨21899402641086085686172421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58398407042896228496459789 21899402641086085686172421)
            ·
              refine ⟨4106137995203641066157329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21899402641086085686172421 4106137995203641066157329)
              ·
                refine ⟨3079603496402730799617997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106137995203641066157329 3079603496402730799617997)
                ·
                  refine ⟨1154851311151024049856749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3079603496402730799617997 1154851311151024049856749)
                  ·
                    refine ⟨433069241681634018696281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154851311151024049856749 433069241681634018696281)
                    ·
                      rfl

theorem cell22_1265099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 3].length) (baseStart_1265099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265099 prefixEnd_1265099 := by exact prefixLift 1265099
  have htrace : WordTrace (prefixWord ++ tailWord_1265099) baseStart_1265099 baseEnd_1265099 := by
    simpa [prefixWord, tailWord_1265099, baseEnd_1265099] using wordTrace_append hprefix tailTrace_1265099
  have hstable : (prefixWord ++ tailWord_1265099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265099).length < 2 ^ (prefixWord ++ tailWord_1265099).sum := by decide
  have hdescent : baseEnd_1265099 < baseStart_1265099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265112 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 7]
def baseStart_1265112 : Nat := 118140960795 + 1265112 * 2 ^ 59
def prefixEnd_1265112 : Nat := 4983230072969 + 3 ^ 40 * 1265112 * 2
def baseEnd_1265112 : Nat := 144357897282435439373747

theorem tailTrace_1265112 : CollatzResearch.WordTrace tailWord_1265112 prefixEnd_1265112 144357897282435439373747 := by
  unfold tailWord_1265112
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071212696361381386490795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30761616928481841848654393 23071212696361381386490795)
  ·
    refine ⟨34606819044542072079736193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23071212696361381386490795 34606819044542072079736193)
    ·
      refine ⟨25955114283406554059802145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34606819044542072079736193 25955114283406554059802145)
      ·
        refine ⟨19466335712554915544851609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25955114283406554059802145 19466335712554915544851609)
        ·
          refine ⟨14599751784416186658638707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19466335712554915544851609 14599751784416186658638707)
          ·
            refine ⟨21899627676624279987958061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14599751784416186658638707 21899627676624279987958061)
            ·
              refine ⟨8212360378734104995484273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21899627676624279987958061 8212360378734104995484273)
              ·
                refine ⟨6159270284050578746613205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8212360378734104995484273 6159270284050578746613205)
                ·
                  refine ⟨144357897282435439373747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6159270284050578746613205 144357897282435439373747)
                  ·
                    rfl

theorem cell22_1265112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_1265112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265112 prefixEnd_1265112 := by exact prefixLift 1265112
  have htrace : WordTrace (prefixWord ++ tailWord_1265112) baseStart_1265112 baseEnd_1265112 := by
    simpa [prefixWord, tailWord_1265112, baseEnd_1265112] using wordTrace_append hprefix tailTrace_1265112
  have hstable : (prefixWord ++ tailWord_1265112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265112).length < 2 ^ (prefixWord ++ tailWord_1265112).sum := by decide
  have hdescent : baseEnd_1265112 < baseStart_1265112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265157 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 8]
def baseStart_1265157 : Nat := 118140960795 + 1265157 * 2 ^ 59
def prefixEnd_1265157 : Nat := 4983230072969 + 3 ^ 40 * 1265157 * 2
def baseEnd_1265157 : Nat := 144363032088980400248701

theorem tailTrace_1265157 : CollatzResearch.WordTrace tailWord_1265157 prefixEnd_1265157 144363032088980400248701 := by
  unfold tailWord_1265157
  simp only [CollatzResearch.WordTrace]
  refine ⟨46144066677559735458369725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30762711118373156972246483 46144066677559735458369725)
  ·
    refine ⟨17304025004084900796888647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46144066677559735458369725 17304025004084900796888647)
    ·
      refine ⟨25956037506127351195332971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17304025004084900796888647 25956037506127351195332971)
      ·
        refine ⟨38934056259191026792999457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25956037506127351195332971 38934056259191026792999457)
        ·
          refine ⟨29200542194393270094749593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38934056259191026792999457 29200542194393270094749593)
          ·
            refine ⟨21900406645794952571062195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29200542194393270094749593 21900406645794952571062195)
            ·
              refine ⟨32850609968692428856593293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21900406645794952571062195 32850609968692428856593293)
              ·
                refine ⟨12318978738259660821222485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32850609968692428856593293 12318978738259660821222485)
                ·
                  refine ⟨144363032088980400248701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12318978738259660821222485 144363032088980400248701)
                  ·
                    rfl

theorem cell22_1265157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_1265157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265157 prefixEnd_1265157 := by exact prefixLift 1265157
  have htrace : WordTrace (prefixWord ++ tailWord_1265157) baseStart_1265157 baseEnd_1265157 := by
    simpa [prefixWord, tailWord_1265157, baseEnd_1265157] using wordTrace_append hprefix tailTrace_1265157
  have hstable : (prefixWord ++ tailWord_1265157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265157).length < 2 ^ (prefixWord ++ tailWord_1265157).sum := by decide
  have hdescent : baseEnd_1265157 < baseStart_1265157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265251 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 3, 3]
def baseStart_1265251 : Nat := 118140960795 + 1265251 * 2 ^ 59
def prefixEnd_1265251 : Nat := 4983230072969 + 3 ^ 40 * 1265251 * 2
def baseEnd_1265251 : Nat := 433121274387956288895815

theorem tailTrace_1265251 : CollatzResearch.WordTrace tailWord_1265251 prefixEnd_1265251 433121274387956288895815 := by
  unfold tailWord_1265251
  simp only [CollatzResearch.WordTrace]
  refine ⟨46147495139219189512291607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30764996759479459674861071 46147495139219189512291607)
  ·
    refine ⟨69221242708828784268437411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46147495139219189512291607 69221242708828784268437411)
    ·
      refine ⟨103831864063243176402656117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69221242708828784268437411 103831864063243176402656117)
      ·
        refine ⟨9734237255929047787749011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103831864063243176402656117 9734237255929047787749011)
        ·
          refine ⟨14601355883893571681623517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734237255929047787749011 14601355883893571681623517)
          ·
            refine ⟨5475508456460089380608819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14601355883893571681623517 5475508456460089380608819)
            ·
              refine ⟨8213262684690134070913229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5475508456460089380608819 8213262684690134070913229)
              ·
                refine ⟨3079973506758800276592461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8213262684690134070913229 3079973506758800276592461)
                ·
                  refine ⟨1154990065034550103722173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3079973506758800276592461 1154990065034550103722173)
                  ·
                    refine ⟨433121274387956288895815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154990065034550103722173 433121274387956288895815)
                    ·
                      rfl

theorem cell22_1265251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 3].length) (baseStart_1265251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265251 prefixEnd_1265251 := by exact prefixLift 1265251
  have htrace : WordTrace (prefixWord ++ tailWord_1265251) baseStart_1265251 baseEnd_1265251 := by
    simpa [prefixWord, tailWord_1265251, baseEnd_1265251] using wordTrace_append hprefix tailTrace_1265251
  have hstable : (prefixWord ++ tailWord_1265251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265251).length < 2 ^ (prefixWord ++ tailWord_1265251).sum := by decide
  have hdescent : baseEnd_1265251 < baseStart_1265251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265324 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_1265324 : Nat := 118140960795 + 1265324 * 2 ^ 59
def prefixEnd_1265324 : Nat := 4983230072969 + 3 ^ 40 * 1265324 * 2
def baseEnd_1265324 : Nat := 433146263779808431820591

theorem tailTrace_1265324 : CollatzResearch.WordTrace tailWord_1265324 prefixEnd_1265324 433146263779808431820591 := by
  unfold tailWord_1265324
  simp only [CollatzResearch.WordTrace]
  refine ⟨23075078833977361489849513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30766771778636481986466017 23075078833977361489849513)
  ·
    refine ⟨17306309125483021117387135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23075078833977361489849513 17306309125483021117387135)
    ·
      refine ⟨25959463688224531676080703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17306309125483021117387135 25959463688224531676080703)
      ·
        refine ⟨38939195532336797514121055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25959463688224531676080703 38939195532336797514121055)
        ·
          refine ⟨58408793298505196271181583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38939195532336797514121055 58408793298505196271181583)
          ·
            refine ⟨87613189947757794406772375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58408793298505196271181583 87613189947757794406772375)
            ·
              refine ⟨131419784921636691610158563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87613189947757794406772375 131419784921636691610158563)
              ·
                refine ⟨197129677382455037415237845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131419784921636691610158563 197129677382455037415237845)
                ·
                  refine ⟨4620226813651289939419637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197129677382455037415237845 4620226813651289939419637)
                  ·
                    refine ⟨433146263779808431820591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4620226813651289939419637 433146263779808431820591)
                    ·
                      rfl

theorem cell22_1265324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_1265324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265324 prefixEnd_1265324 := by exact prefixLift 1265324
  have htrace : WordTrace (prefixWord ++ tailWord_1265324) baseStart_1265324 baseEnd_1265324 := by
    simpa [prefixWord, tailWord_1265324, baseEnd_1265324] using wordTrace_append hprefix tailTrace_1265324
  have hstable : (prefixWord ++ tailWord_1265324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265324).length < 2 ^ (prefixWord ++ tailWord_1265324).sum := by decide
  have hdescent : baseEnd_1265324 < baseStart_1265324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265339 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 1, 6]
def baseStart_1265339 : Nat := 118140960795 + 1265339 * 2 ^ 59
def prefixEnd_1265339 : Nat := 4983230072969 + 3 ^ 40 * 1265339 * 2
def baseEnd_1265339 : Nat := 433151398586353392695545

theorem tailTrace_1265339 : CollatzResearch.WordTrace tailWord_1265339 prefixEnd_1265339 433151398586353392695545 := by
  unfold tailWord_1265339
  simp only [CollatzResearch.WordTrace]
  refine ⟨46150704762900380541495071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30767136508600253694330047 46150704762900380541495071)
  ·
    refine ⟨69226057144350570812242607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46150704762900380541495071 69226057144350570812242607)
    ·
      refine ⟨103839085716525856218363911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69226057144350570812242607 103839085716525856218363911)
      ·
        refine ⟨155758628574788784327545867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103839085716525856218363911 155758628574788784327545867)
        ·
          refine ⟨233637942862183176491318801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155758628574788784327545867 233637942862183176491318801)
          ·
            refine ⟨175228457146637382368489101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233637942862183176491318801 175228457146637382368489101)
            ·
              refine ⟨65710671429989018388183413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175228457146637382368489101 65710671429989018388183413)
              ·
                refine ⟨6160375446561470473892195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65710671429989018388183413 6160375446561470473892195)
                ·
                  refine ⟨9240563169842205710838293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6160375446561470473892195 9240563169842205710838293)
                  ·
                    refine ⟨433151398586353392695545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9240563169842205710838293 433151398586353392695545)
                    ·
                      rfl

theorem cell22_1265339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_1265339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265339 prefixEnd_1265339 := by exact prefixLift 1265339
  have htrace : WordTrace (prefixWord ++ tailWord_1265339) baseStart_1265339 baseEnd_1265339 := by
    simpa [prefixWord, tailWord_1265339, baseEnd_1265339] using wordTrace_append hprefix tailTrace_1265339
  have hstable : (prefixWord ++ tailWord_1265339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265339).length < 2 ^ (prefixWord ++ tailWord_1265339).sum := by decide
  have hdescent : baseEnd_1265339 < baseStart_1265339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265341 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_1265341 : Nat := 118140960795 + 1265341 * 2 ^ 59
def prefixEnd_1265341 : Nat := 4983230072969 + 3 ^ 40 * 1265341 * 2
def baseEnd_1265341 : Nat := 433152083227226054145539

theorem tailTrace_1265341 : CollatzResearch.WordTrace tailWord_1265341 prefixEnd_1265341 433152083227226054145539 := by
  unfold tailWord_1265341
  simp only [CollatzResearch.WordTrace]
  refine ⟨46150777708893134883067877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30767185139262089922045251 46150777708893134883067877)
  ·
    refine ⟨8653270820417462790575227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46150777708893134883067877 8653270820417462790575227)
    ·
      refine ⟨12979906230626194185862841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8653270820417462790575227 12979906230626194185862841)
      ·
        refine ⟨9734929672969645639397131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12979906230626194185862841 9734929672969645639397131)
        ·
          refine ⟨14602394509454468459095697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734929672969645639397131 14602394509454468459095697)
          ·
            refine ⟨10951795882090851344321773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14602394509454468459095697 10951795882090851344321773)
            ·
              refine ⟨4106923455784069254120665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10951795882090851344321773 4106923455784069254120665)
              ·
                refine ⟨3080192591838051940590499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106923455784069254120665 3080192591838051940590499)
                ·
                  refine ⟨4620288887757077910885749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080192591838051940590499 4620288887757077910885749)
                  ·
                    refine ⟨433152083227226054145539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4620288887757077910885749 433152083227226054145539)
                    ·
                      rfl

theorem cell22_1265341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_1265341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265341 prefixEnd_1265341 := by exact prefixLift 1265341
  have htrace : WordTrace (prefixWord ++ tailWord_1265341) baseStart_1265341 baseEnd_1265341 := by
    simpa [prefixWord, tailWord_1265341, baseEnd_1265341] using wordTrace_append hprefix tailTrace_1265341
  have hstable : (prefixWord ++ tailWord_1265341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265341).length < 2 ^ (prefixWord ++ tailWord_1265341).sum := by decide
  have hdescent : baseEnd_1265341 < baseStart_1265341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265354 : List Nat := [3, 1, 2, 1, 15]
def baseStart_1265354 : Nat := 118140960795 + 1265354 * 2 ^ 59
def prefixEnd_1265354 : Nat := 4983230072969 + 3 ^ 40 * 1265354 * 2
def baseEnd_1265354 : Nat := 1782537174456371825393

theorem tailTrace_1265354 : CollatzResearch.WordTrace tailWord_1265354 prefixEnd_1265354 1782537174456371825393 := by
  unfold tailWord_1265354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537812964461509525822779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30767501238564025402194077 11537812964461509525822779)
  ·
    refine ⟨17306719446692264288734169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11537812964461509525822779 17306719446692264288734169)
    ·
      refine ⟨12980039585019198216550627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17306719446692264288734169 12980039585019198216550627)
      ·
        refine ⟨19470059377528797324825941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12980039585019198216550627 19470059377528797324825941)
        ·
          refine ⟨1782537174456371825393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 19470059377528797324825941 1782537174456371825393)
          ·
            rfl

theorem cell22_1265354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 15].length) (baseStart_1265354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265354 prefixEnd_1265354 := by exact prefixLift 1265354
  have htrace : WordTrace (prefixWord ++ tailWord_1265354) baseStart_1265354 baseEnd_1265354 := by
    simpa [prefixWord, tailWord_1265354, baseEnd_1265354] using wordTrace_append hprefix tailTrace_1265354
  have hstable : (prefixWord ++ tailWord_1265354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265354).length < 2 ^ (prefixWord ++ tailWord_1265354).sum := by decide
  have hdescent : baseEnd_1265354 < baseStart_1265354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265416 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 7]
def baseStart_1265416 : Nat := 118140960795 + 1265416 * 2 ^ 59
def prefixEnd_1265416 : Nat := 4983230072969 + 3 ^ 40 * 1265416 * 2
def baseEnd_1265416 : Nat := 144392585753316952840103

theorem tailTrace_1265416 : CollatzResearch.WordTrace tailWord_1265416 prefixEnd_1265416 144392585753316952840103 := by
  unfold tailWord_1265416
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076756591810711346024051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30769008789080948461365401 23076756591810711346024051)
  ·
    refine ⟨34615134887716067019036077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23076756591810711346024051 34615134887716067019036077)
    ·
      refine ⟨12980675582893525132138529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34615134887716067019036077 12980675582893525132138529)
      ·
        refine ⟨9735506687170143849103897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12980675582893525132138529 9735506687170143849103897)
        ·
          refine ⟨7301630015377607886827923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9735506687170143849103897 7301630015377607886827923)
          ·
            refine ⟨10952445023066411830241885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7301630015377607886827923 10952445023066411830241885)
            ·
              refine ⟨4107166883649904436340707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10952445023066411830241885 4107166883649904436340707)
              ·
                refine ⟨6160750325474856654511061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107166883649904436340707 6160750325474856654511061)
                ·
                  refine ⟨144392585753316952840103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6160750325474856654511061 144392585753316952840103)
                  ·
                    rfl

theorem cell22_1265416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_1265416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265416 prefixEnd_1265416 := by exact prefixLift 1265416
  have htrace : WordTrace (prefixWord ++ tailWord_1265416) baseStart_1265416 baseEnd_1265416 := by
    simpa [prefixWord, tailWord_1265416, baseEnd_1265416] using wordTrace_append hprefix tailTrace_1265416
  have hstable : (prefixWord ++ tailWord_1265416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265416).length < 2 ^ (prefixWord ++ tailWord_1265416).sum := by decide
  have hdescent : baseEnd_1265416 < baseStart_1265416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265420 : List Nat := [2, 2, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_1265420 : Nat := 118140960795 + 1265420 * 2 ^ 59
def prefixEnd_1265420 : Nat := 4983230072969 + 3 ^ 40 * 1265420 * 2
def baseEnd_1265420 : Nat := 433179126541696181420297

theorem tailTrace_1265420 : CollatzResearch.WordTrace tailWord_1265420 prefixEnd_1265420 433179126541696181420297 := by
  unfold tailWord_1265420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076829537803465687596857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30769106050404620916795809 23076829537803465687596857)
  ·
    refine ⟨17307622153352599265697643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23076829537803465687596857 17307622153352599265697643)
    ·
      refine ⟨25961433230028898898546465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17307622153352599265697643 25961433230028898898546465)
      ·
        refine ⟨19471074922521674173909849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25961433230028898898546465 19471074922521674173909849)
        ·
          refine ⟨14603306191891255630432387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19471074922521674173909849 14603306191891255630432387)
          ·
            refine ⟨21904959287836883445648581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14603306191891255630432387 21904959287836883445648581)
            ·
              refine ⟨4107179866469415646059109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21904959287836883445648581 4107179866469415646059109)
              ·
                refine ⟨770096224963015433636083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4107179866469415646059109 770096224963015433636083)
                ·
                  refine ⟨1155144337444523150454125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770096224963015433636083 1155144337444523150454125)
                  ·
                    refine ⟨433179126541696181420297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155144337444523150454125 433179126541696181420297)
                    ·
                      rfl

theorem cell22_1265420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_1265420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265420 prefixEnd_1265420 := by exact prefixLift 1265420
  have htrace : WordTrace (prefixWord ++ tailWord_1265420) baseStart_1265420 baseEnd_1265420 := by
    simpa [prefixWord, tailWord_1265420, baseEnd_1265420] using wordTrace_append hprefix tailTrace_1265420
  have hstable : (prefixWord ++ tailWord_1265420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265420).length < 2 ^ (prefixWord ++ tailWord_1265420).sum := by decide
  have hdescent : baseEnd_1265420 < baseStart_1265420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265514 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_1265514 : Nat := 118140960795 + 1265514 * 2 ^ 59
def prefixEnd_1265514 : Nat := 4983230072969 + 3 ^ 40 * 1265514 * 2
def baseEnd_1265514 : Nat := 433211304662711269570009

theorem tailTrace_1265514 : CollatzResearch.WordTrace tailWord_1265514 prefixEnd_1265514 433211304662711269570009 := by
  unfold tailWord_1265514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11539271884316596357278899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30771391691510923619410397 11539271884316596357278899)
  ·
    refine ⟨17308907826474894535918349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11539271884316596357278899 17308907826474894535918349)
    ·
      refine ⟨6490840434928085450969381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17308907826474894535918349 6490840434928085450969381)
      ·
        refine ⟨1217032581549016022056759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6490840434928085450969381 1217032581549016022056759)
        ·
          refine ⟨1825548872323524033085139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217032581549016022056759 1825548872323524033085139)
          ·
            refine ⟨2738323308485286049627709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825548872323524033085139 2738323308485286049627709)
            ·
              refine ⟨1026871240681982268610391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2738323308485286049627709 1026871240681982268610391)
              ·
                refine ⟨1540306861022973402915587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026871240681982268610391 1540306861022973402915587)
                ·
                  refine ⟨2310460291534460104373381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540306861022973402915587 2310460291534460104373381)
                  ·
                    refine ⟨433211304662711269570009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2310460291534460104373381 433211304662711269570009)
                    ·
                      rfl

theorem cell22_1265514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_1265514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265514 prefixEnd_1265514 := by exact prefixLift 1265514
  have htrace : WordTrace (prefixWord ++ tailWord_1265514) baseStart_1265514 baseEnd_1265514 := by
    simpa [prefixWord, tailWord_1265514, baseEnd_1265514] using wordTrace_append hprefix tailTrace_1265514
  have hstable : (prefixWord ++ tailWord_1265514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265514).length < 2 ^ (prefixWord ++ tailWord_1265514).sum := by decide
  have hdescent : baseEnd_1265514 < baseStart_1265514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265536 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_1265536 : Nat := 118140960795 + 1265536 * 2 ^ 59
def prefixEnd_1265536 : Nat := 4983230072969 + 3 ^ 40 * 1265536 * 2
def baseEnd_1265536 : Nat := 433218835712310545519941

theorem tailTrace_1265536 : CollatzResearch.WordTrace tailWord_1265536 prefixEnd_1265536 433218835712310545519941 := by
  unfold tailWord_1265536
  simp only [CollatzResearch.WordTrace]
  refine ⟨23078944971593341593208231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30771926628791122124277641 23078944971593341593208231)
  ·
    refine ⟨34618417457390012389812347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23078944971593341593208231 34618417457390012389812347)
    ·
      refine ⟨51927626186085018584718521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34618417457390012389812347 51927626186085018584718521)
      ·
        refine ⟨38945719639563763938538891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51927626186085018584718521 38945719639563763938538891)
        ·
          refine ⟨58418579459345645907808337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38945719639563763938538891 58418579459345645907808337)
          ·
            refine ⟨43813934594509234430856253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58418579459345645907808337 43813934594509234430856253)
            ·
              refine ⟨16430225472940962911571095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43813934594509234430856253 16430225472940962911571095)
              ·
                refine ⟨24645338209411444367356643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16430225472940962911571095 24645338209411444367356643)
                ·
                  refine ⟨36968007314117166551034965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24645338209411444367356643 36968007314117166551034965)
                  ·
                    refine ⟨433218835712310545519941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36968007314117166551034965 433218835712310545519941)
                    ·
                      rfl

theorem cell22_1265536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_1265536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265536 prefixEnd_1265536 := by exact prefixLift 1265536
  have htrace : WordTrace (prefixWord ++ tailWord_1265536) baseStart_1265536 baseEnd_1265536 := by
    simpa [prefixWord, tailWord_1265536, baseEnd_1265536] using wordTrace_append hprefix tailTrace_1265536
  have hstable : (prefixWord ++ tailWord_1265536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265536).length < 2 ^ (prefixWord ++ tailWord_1265536).sum := by decide
  have hdescent : baseEnd_1265536 < baseStart_1265536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265572 : List Nat := [2, 3, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_1265572 : Nat := 118140960795 + 1265572 * 2 ^ 59
def prefixEnd_1265572 : Nat := 4983230072969 + 3 ^ 40 * 1265572 * 2
def baseEnd_1265572 : Nat := 433231159248018451619831

theorem tailTrace_1265572 : CollatzResearch.WordTrace tailWord_1265572 prefixEnd_1265572 433231159248018451619831 := by
  unfold tailWord_1265572
  simp only [CollatzResearch.WordTrace]
  refine ⟨23079601485528130667363485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30772801980704174223151313 23079601485528130667363485)
  ·
    refine ⟨8654850557073049000261307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23079601485528130667363485 8654850557073049000261307)
    ·
      refine ⟨12982275835609573500391961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8654850557073049000261307 12982275835609573500391961)
      ·
        refine ⟨9736706876707180125293971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12982275835609573500391961 9736706876707180125293971)
        ·
          refine ⟨14605060315060770187940957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9736706876707180125293971 14605060315060770187940957)
          ·
            refine ⟨5476897618147788820477859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14605060315060770187940957 5476897618147788820477859)
            ·
              refine ⟨8215346427221683230716789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476897618147788820477859 8215346427221683230716789)
              ·
                refine ⟨770188727552032802879699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8215346427221683230716789 770188727552032802879699)
                ·
                  refine ⟨1155283091328049204319549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770188727552032802879699 1155283091328049204319549)
                  ·
                    refine ⟨433231159248018451619831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155283091328049204319549 433231159248018451619831)
                    ·
                      rfl

theorem cell22_1265572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_1265572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265572 prefixEnd_1265572 := by exact prefixLift 1265572
  have htrace : WordTrace (prefixWord ++ tailWord_1265572) baseStart_1265572 baseEnd_1265572 := by
    simpa [prefixWord, tailWord_1265572, baseEnd_1265572] using wordTrace_append hprefix tailTrace_1265572
  have hstable : (prefixWord ++ tailWord_1265572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265572).length < 2 ^ (prefixWord ++ tailWord_1265572).sum := by decide
  have hdescent : baseEnd_1265572 < baseStart_1265572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265585 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 5]
def baseStart_1265585 : Nat := 118140960795 + 1265585 * 2 ^ 59
def prefixEnd_1265585 : Nat := 4983230072969 + 3 ^ 40 * 1265585 * 2
def baseEnd_1265585 : Nat := 144411869804563583681597

theorem tailTrace_1265585 : CollatzResearch.WordTrace tailWord_1265585 prefixEnd_1265585 144411869804563583681597 := by
  unfold tailWord_1265585
  simp only [CollatzResearch.WordTrace]
  refine ⟨46159677120009164554950209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30773118080006109703300139 46159677120009164554950209)
  ·
    refine ⟨34619757840006873416212657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46159677120009164554950209 34619757840006873416212657)
    ·
      refine ⟨25964818380005155062159493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34619757840006873416212657 25964818380005155062159493)
      ·
        refine ⟨4868403446250966574154905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25964818380005155062159493 4868403446250966574154905)
        ·
          refine ⟨3651302584688224930616179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4868403446250966574154905 3651302584688224930616179)
          ·
            refine ⟨5476953877032337395924269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651302584688224930616179 5476953877032337395924269)
            ·
              refine ⟨2053857703887126523471601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5476953877032337395924269 2053857703887126523471601)
              ·
                refine ⟨1540393277915344892603701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053857703887126523471601 1540393277915344892603701)
                ·
                  refine ⟨144411869804563583681597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1540393277915344892603701 144411869804563583681597)
                  ·
                    rfl

theorem cell22_1265585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_1265585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265585 prefixEnd_1265585 := by exact prefixLift 1265585
  have htrace : WordTrace (prefixWord ++ tailWord_1265585) baseStart_1265585 baseEnd_1265585 := by
    simpa [prefixWord, tailWord_1265585, baseEnd_1265585] using wordTrace_append hprefix tailTrace_1265585
  have hstable : (prefixWord ++ tailWord_1265585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265585).length < 2 ^ (prefixWord ++ tailWord_1265585).sum := by decide
  have hdescent : baseEnd_1265585 < baseStart_1265585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265615 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 1, 4]
def baseStart_1265615 : Nat := 118140960795 + 1265615 * 2 ^ 59
def prefixEnd_1265615 : Nat := 4983230072969 + 3 ^ 40 * 1265615 * 2
def baseEnd_1265615 : Nat := 433245879026780672794699

theorem tailTrace_1265615 : CollatzResearch.WordTrace tailWord_1265615 prefixEnd_1265615 433245879026780672794699 := by
  unfold tailWord_1265615
  simp only [CollatzResearch.WordTrace]
  refine ⟨46160771309900479678542299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30773847539933653119028199 46160771309900479678542299)
  ·
    refine ⟨69241156964850719517813449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46160771309900479678542299 69241156964850719517813449)
    ·
      refine ⟨51930867723638039638360087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69241156964850719517813449 51930867723638039638360087)
      ·
        refine ⟨77896301585457059457540131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51930867723638039638360087 77896301585457059457540131)
        ·
          refine ⟨116844452378185589186310197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77896301585457059457540131 116844452378185589186310197)
          ·
            refine ⟨10954167410454898986216581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116844452378185589186310197 10954167410454898986216581)
            ·
              refine ⟨2053906389460293559915609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10954167410454898986216581 2053906389460293559915609)
              ·
                refine ⟨1540429792095220169936707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053906389460293559915609 1540429792095220169936707)
                ·
                  refine ⟨2310644688142830254905061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540429792095220169936707 2310644688142830254905061)
                  ·
                    refine ⟨433245879026780672794699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2310644688142830254905061 433245879026780672794699)
                    ·
                      rfl

theorem cell22_1265615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_1265615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265615 prefixEnd_1265615 := by exact prefixLift 1265615
  have htrace : WordTrace (prefixWord ++ tailWord_1265615) baseStart_1265615 baseEnd_1265615 := by
    simpa [prefixWord, tailWord_1265615, baseEnd_1265615] using wordTrace_append hprefix tailTrace_1265615
  have hstable : (prefixWord ++ tailWord_1265615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265615).length < 2 ^ (prefixWord ++ tailWord_1265615).sum := by decide
  have hdescent : baseEnd_1265615 < baseStart_1265615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265647 : List Nat := [1, 1, 2, 1, 4, 2, 5, 2, 4]
def baseStart_1265647 : Nat := 118140960795 + 1265647 * 2 ^ 59
def prefixEnd_1265647 : Nat := 4983230072969 + 3 ^ 40 * 1265647 * 2
def baseEnd_1265647 : Nat := 144418944426914418664867

theorem tailTrace_1265647 : CollatzResearch.WordTrace tailWord_1265647 prefixEnd_1265647 144418944426914418664867 := by
  unfold tailWord_1265647
  simp only [CollatzResearch.WordTrace]
  refine ⟨46161938445784549143707195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30774625630523032762471463 46161938445784549143707195)
  ·
    refine ⟨69242907668676823715560793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46161938445784549143707195 69242907668676823715560793)
    ·
      refine ⟨51932180751507617786670595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69242907668676823715560793 51932180751507617786670595)
      ·
        refine ⟨77898271127261426680005893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51932180751507617786670595 77898271127261426680005893)
        ·
          refine ⟨14605925836361517502501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77898271127261426680005893 14605925836361517502501105)
          ·
            refine ⟨10954444377271138126875829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14605925836361517502501105 10954444377271138126875829)
            ·
              refine ⟨1026979160369169199394609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10954444377271138126875829 1026979160369169199394609)
              ·
                refine ⟨770234370276876899545957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026979160369169199394609 770234370276876899545957)
                ·
                  refine ⟨144418944426914418664867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 770234370276876899545957 144418944426914418664867)
                  ·
                    rfl

theorem cell22_1265647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 4].length) (baseStart_1265647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265647 prefixEnd_1265647 := by exact prefixLift 1265647
  have htrace : WordTrace (prefixWord ++ tailWord_1265647) baseStart_1265647 baseEnd_1265647 := by
    simpa [prefixWord, tailWord_1265647, baseEnd_1265647] using wordTrace_append hprefix tailTrace_1265647
  have hstable : (prefixWord ++ tailWord_1265647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265647).length < 2 ^ (prefixWord ++ tailWord_1265647).sum := by decide
  have hdescent : baseEnd_1265647 < baseStart_1265647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265741 : List Nat := [1, 6, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1265741 : Nat := 118140960795 + 1265741 * 2 ^ 59
def prefixEnd_1265741 : Nat := 4983230072969 + 3 ^ 40 * 1265741 * 2
def baseEnd_1265741 : Nat := 433289011401758344144313

theorem tailTrace_1265741 : CollatzResearch.WordTrace tailWord_1265741 prefixEnd_1265741 433289011401758344144313 := by
  unfold tailWord_1265741
  simp only [CollatzResearch.WordTrace]
  refine ⟨46165366907444003197629077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30776911271629335465086051 46165366907444003197629077)
  ·
    refine ⟨2164001573786437649888863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46165366907444003197629077 2164001573786437649888863)
    ·
      refine ⟨3246002360679656474833295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164001573786437649888863 3246002360679656474833295)
      ·
        refine ⟨4869003541019484712249943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246002360679656474833295 4869003541019484712249943)
        ·
          refine ⟨7303505311529227068374915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869003541019484712249943 7303505311529227068374915)
          ·
            refine ⟨10955257967293840602562373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7303505311529227068374915 10955257967293840602562373)
            ·
              refine ⟨2054110868867595112980445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10955257967293840602562373 2054110868867595112980445)
              ·
                refine ⟨770291575825348167367667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2054110868867595112980445 770291575825348167367667)
                ·
                  refine ⟨1155437363738022251051501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770291575825348167367667 1155437363738022251051501)
                  ·
                    refine ⟨433289011401758344144313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155437363738022251051501 433289011401758344144313)
                    ·
                      rfl

theorem cell22_1265741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1265741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265741 prefixEnd_1265741 := by exact prefixLift 1265741
  have htrace : WordTrace (prefixWord ++ tailWord_1265741) baseStart_1265741 baseEnd_1265741 := by
    simpa [prefixWord, tailWord_1265741, baseEnd_1265741] using wordTrace_append hprefix tailTrace_1265741
  have hstable : (prefixWord ++ tailWord_1265741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265741).length < 2 ^ (prefixWord ++ tailWord_1265741).sum := by decide
  have hdescent : baseEnd_1265741 < baseStart_1265741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265758 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1265758 : Nat := 118140960795 + 1265758 * 2 ^ 59
def prefixEnd_1265758 : Nat := 4983230072969 + 3 ^ 40 * 1265758 * 2
def baseEnd_1265758 : Nat := 433294830849175966469261

theorem tailTrace_1265758 : CollatzResearch.WordTrace tailWord_1265758 prefixEnd_1265758 433294830849175966469261 := by
  unfold tailWord_1265758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770748368547801887624741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30777324632254943400665285 5770748368547801887624741)
  ·
    refine ⟨1082015319102712853929639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5770748368547801887624741 1082015319102712853929639)
    ·
      refine ⟨1623022978654069280894459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082015319102712853929639 1623022978654069280894459)
      ·
        refine ⟨2434534467981103921341689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623022978654069280894459 2434534467981103921341689)
        ·
          refine ⟨1825900850985827941006267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2434534467981103921341689 1825900850985827941006267)
          ·
            refine ⟨2738851276478741911509401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825900850985827941006267 2738851276478741911509401)
            ·
              refine ⟨2054138457359056433632051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2738851276478741911509401 2054138457359056433632051)
              ·
                refine ⟨3081207686038584650448077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054138457359056433632051 3081207686038584650448077)
                ·
                  refine ⟨1155452882264469243918029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3081207686038584650448077 1155452882264469243918029)
                  ·
                    refine ⟨433294830849175966469261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155452882264469243918029 433294830849175966469261)
                    ·
                      rfl

theorem cell22_1265758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1265758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265758 prefixEnd_1265758 := by exact prefixLift 1265758
  have htrace : WordTrace (prefixWord ++ tailWord_1265758) baseStart_1265758 baseEnd_1265758 := by
    simpa [prefixWord, tailWord_1265758, baseEnd_1265758] using wordTrace_append hprefix tailTrace_1265758
  have hstable : (prefixWord ++ tailWord_1265758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265758).length < 2 ^ (prefixWord ++ tailWord_1265758).sum := by decide
  have hdescent : baseEnd_1265758 < baseStart_1265758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265765 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 6]
def baseStart_1265765 : Nat := 118140960795 + 1265765 * 2 ^ 59
def prefixEnd_1265765 : Nat := 4983230072969 + 3 ^ 40 * 1265765 * 2
def baseEnd_1265765 : Nat := 144432409030743427181413

theorem tailTrace_1265765 : CollatzResearch.WordTrace tailWord_1265765 prefixEnd_1265765 144432409030743427181413 := by
  unfold tailWord_1265765
  simp only [CollatzResearch.WordTrace]
  refine ⟨46166242259357055296502749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30777494839571370197668499 46166242259357055296502749)
  ·
    refine ⟨17312340847258895736188531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46166242259357055296502749 17312340847258895736188531)
    ·
      refine ⟨25968511270888343604282797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17312340847258895736188531 25968511270888343604282797)
      ·
        refine ⟨9738191726583128851606049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25968511270888343604282797 9738191726583128851606049)
        ·
          refine ⟨7303643794937346638704537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9738191726583128851606049 7303643794937346638704537)
          ·
            refine ⟨5477732846203009979028403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7303643794937346638704537 5477732846203009979028403)
            ·
              refine ⟨8216599269304514968542605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477732846203009979028403 8216599269304514968542605)
              ·
                refine ⟨3081224725989193113203477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8216599269304514968542605 3081224725989193113203477)
                ·
                  refine ⟨144432409030743427181413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3081224725989193113203477 144432409030743427181413)
                  ·
                    rfl

theorem cell22_1265765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_1265765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265765 prefixEnd_1265765 := by exact prefixLift 1265765
  have htrace : WordTrace (prefixWord ++ tailWord_1265765) baseStart_1265765 baseEnd_1265765 := by
    simpa [prefixWord, tailWord_1265765, baseEnd_1265765] using wordTrace_append hprefix tailTrace_1265765
  have hstable : (prefixWord ++ tailWord_1265765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265765).length < 2 ^ (prefixWord ++ tailWord_1265765).sum := by decide
  have hdescent : baseEnd_1265765 < baseStart_1265765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265782 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1265782 : Nat := 118140960795 + 1265782 * 2 ^ 59
def prefixEnd_1265782 : Nat := 4983230072969 + 3 ^ 40 * 1265782 * 2
def baseEnd_1265782 : Nat := 144434348846549301289729

theorem tailTrace_1265782 : CollatzResearch.WordTrace tailWord_1265782 prefixEnd_1265782 144434348846549301289729 := by
  unfold tailWord_1265782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885428893768466699991975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30777908200196978133247733 2885428893768466699991975)
  ·
    refine ⟨4328143340652700049987963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2885428893768466699991975 4328143340652700049987963)
    ·
      refine ⟨6492215010979050074981945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4328143340652700049987963 6492215010979050074981945)
      ·
        refine ⟨4869161258234287556236459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6492215010979050074981945 4869161258234287556236459)
        ·
          refine ⟨7303741887351431334354689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869161258234287556236459 7303741887351431334354689)
          ·
            refine ⟨5477806415513573500766017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7303741887351431334354689 5477806415513573500766017)
            ·
              refine ⟨4108354811635180125574513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5477806415513573500766017 4108354811635180125574513)
              ·
                refine ⟨3081266108726385094180885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4108354811635180125574513 3081266108726385094180885)
                ·
                  refine ⟨144434348846549301289729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3081266108726385094180885 144434348846549301289729)
                  ·
                    rfl

theorem cell22_1265782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1265782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265782 prefixEnd_1265782 := by exact prefixLift 1265782
  have htrace : WordTrace (prefixWord ++ tailWord_1265782) baseStart_1265782 baseEnd_1265782 := by
    simpa [prefixWord, tailWord_1265782, baseEnd_1265782] using wordTrace_append hprefix tailTrace_1265782
  have hstable : (prefixWord ++ tailWord_1265782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265782).length < 2 ^ (prefixWord ++ tailWord_1265782).sum := by decide
  have hdescent : baseEnd_1265782 < baseStart_1265782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265795 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 1, 6]
def baseStart_1265795 : Nat := 118140960795 + 1265795 * 2 ^ 59
def prefixEnd_1265795 : Nat := 4983230072969 + 3 ^ 40 * 1265795 * 2
def baseEnd_1265795 : Nat := 433307496705320203294147

theorem tailTrace_1265795 : CollatzResearch.WordTrace tailWord_1265795 prefixEnd_1265795 433307496705320203294147 := by
  unfold tailWord_1265795
  simp only [CollatzResearch.WordTrace]
  refine ⟨46167336449248370420094839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30778224299498913613396559 46167336449248370420094839)
  ·
    refine ⟨69251004673872555630142259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46167336449248370420094839 69251004673872555630142259)
    ·
      refine ⟨103876507010808833445213389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69251004673872555630142259 103876507010808833445213389)
      ·
        refine ⟨38953690129053312541955021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103876507010808833445213389 38953690129053312541955021)
        ·
          refine ⟨14607633798394992203233133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38953690129053312541955021 14607633798394992203233133)
          ·
            refine ⟨5477862674398122076212425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14607633798394992203233133 5477862674398122076212425)
            ·
              refine ⟨4108397005798591557159319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5477862674398122076212425 4108397005798591557159319)
              ·
                refine ⟨6162595508697887335738979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108397005798591557159319 6162595508697887335738979)
                ·
                  refine ⟨9243893263046831003608469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6162595508697887335738979 9243893263046831003608469)
                  ·
                    refine ⟨433307496705320203294147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9243893263046831003608469 433307496705320203294147)
                    ·
                      rfl

theorem cell22_1265795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_1265795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265795 prefixEnd_1265795 := by exact prefixLift 1265795
  have htrace : WordTrace (prefixWord ++ tailWord_1265795) baseStart_1265795 baseEnd_1265795 := by
    simpa [prefixWord, tailWord_1265795, baseEnd_1265795] using wordTrace_append hprefix tailTrace_1265795
  have hstable : (prefixWord ++ tailWord_1265795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265795).length < 2 ^ (prefixWord ++ tailWord_1265795).sum := by decide
  have hdescent : baseEnd_1265795 < baseStart_1265795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265797 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_1265797 : Nat := 118140960795 + 1265797 * 2 ^ 59
def prefixEnd_1265797 : Nat := 4983230072969 + 3 ^ 40 * 1265797 * 2
def baseEnd_1265797 : Nat := 433308181346192864744141

theorem tailTrace_1265797 : CollatzResearch.WordTrace tailWord_1265797 prefixEnd_1265797 433308181346192864744141 := by
  unfold tailWord_1265797
  simp only [CollatzResearch.WordTrace]
  refine ⟨46167409395241124761667645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30778272930160749841111763 46167409395241124761667645)
  ·
    refine ⟨17312778523215421785625367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46167409395241124761667645 17312778523215421785625367)
    ·
      refine ⟨25969167784823132678438051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17312778523215421785625367 25969167784823132678438051)
      ·
        refine ⟨38953751677234699017657077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25969167784823132678438051 38953751677234699017657077)
        ·
          refine ⟨3651914219740753032905351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38953751677234699017657077 3651914219740753032905351)
          ·
            refine ⟨5477871329611129549358027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651914219740753032905351 5477871329611129549358027)
            ·
              refine ⟨8216806994416694324037041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477871329611129549358027 8216806994416694324037041)
              ·
                refine ⟨6162605245812520743027781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8216806994416694324037041 6162605245812520743027781)
                ·
                  refine ⟨1155488483589847639317709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6162605245812520743027781 1155488483589847639317709)
                  ·
                    refine ⟨433308181346192864744141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155488483589847639317709 433308181346192864744141)
                    ·
                      rfl

theorem cell22_1265797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_1265797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265797 prefixEnd_1265797 := by exact prefixLift 1265797
  have htrace : WordTrace (prefixWord ++ tailWord_1265797) baseStart_1265797 baseEnd_1265797 := by
    simpa [prefixWord, tailWord_1265797, baseEnd_1265797] using wordTrace_append hprefix tailTrace_1265797
  have hstable : (prefixWord ++ tailWord_1265797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265797).length < 2 ^ (prefixWord ++ tailWord_1265797).sum := by decide
  have hdescent : baseEnd_1265797 < baseStart_1265797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265816 : List Nat := [2, 1, 2, 4, 3, 1, 3, 2, 4]
def baseStart_1265816 : Nat := 118140960795 + 1265816 * 2 ^ 59
def prefixEnd_1265816 : Nat := 4983230072969 + 3 ^ 40 * 1265816 * 2
def baseEnd_1265816 : Nat := 144438228478161049506361

theorem tailTrace_1265816 : CollatzResearch.WordTrace tailWord_1265816 prefixEnd_1265816 144438228478161049506361 := by
  unfold tailWord_1265816
  simp only [CollatzResearch.WordTrace]
  refine ⟨23084051191086145503304651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30778734921448194004406201 23084051191086145503304651)
  ·
    refine ⟨34626076786629218254956977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23084051191086145503304651 34626076786629218254956977)
    ·
      refine ⟨25969557589971913691217733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34626076786629218254956977 25969557589971913691217733)
      ·
        refine ⟨4869292048119733817103325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25969557589971913691217733 4869292048119733817103325)
        ·
          refine ⟨1825984518044900181413747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4869292048119733817103325 1825984518044900181413747)
          ·
            refine ⟨2738976777067350272120621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825984518044900181413747 2738976777067350272120621)
            ·
              refine ⟨1027116291400256352045233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2738976777067350272120621 1027116291400256352045233)
              ·
                refine ⟨770337218550192264033925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027116291400256352045233 770337218550192264033925)
                ·
                  refine ⟨144438228478161049506361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 770337218550192264033925 144438228478161049506361)
                  ·
                    rfl

theorem cell22_1265816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_1265816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265816 prefixEnd_1265816 := by exact prefixLift 1265816
  have htrace : WordTrace (prefixWord ++ tailWord_1265816) baseStart_1265816 baseEnd_1265816 := by
    simpa [prefixWord, tailWord_1265816, baseEnd_1265816] using wordTrace_append hprefix tailTrace_1265816
  have hstable : (prefixWord ++ tailWord_1265816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265816).length < 2 ^ (prefixWord ++ tailWord_1265816).sum := by decide
  have hdescent : baseEnd_1265816 < baseStart_1265816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265831 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1265831 : Nat := 118140960795 + 1265831 * 2 ^ 59
def prefixEnd_1265831 : Nat := 4983230072969 + 3 ^ 40 * 1265831 * 2
def baseEnd_1265831 : Nat := 433319820241028109394037

theorem tailTrace_1265831 : CollatzResearch.WordTrace tailWord_1265831 prefixEnd_1265831 433319820241028109394037 := by
  unfold tailWord_1265831
  simp only [CollatzResearch.WordTrace]
  refine ⟨46168649477117948568405347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30779099651411965712270231 46168649477117948568405347)
  ·
    refine ⟨69252974215676922852608021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46168649477117948568405347 69252974215676922852608021)
    ·
      refine ⟨3246233166359855758716001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69252974215676922852608021 3246233166359855758716001)
      ·
        refine ⟨2434674874769891819037001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3246233166359855758716001 2434674874769891819037001)
        ·
          refine ⟨1826006156077418864277751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2434674874769891819037001 1826006156077418864277751)
          ·
            refine ⟨2739009234116128296416627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826006156077418864277751 2739009234116128296416627)
            ·
              refine ⟨4108513851174192444624941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739009234116128296416627 4108513851174192444624941)
              ·
                refine ⟨1540692694190322166734353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4108513851174192444624941 1540692694190322166734353)
                ·
                  refine ⟨1155519520642741625050765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1540692694190322166734353 1155519520642741625050765)
                  ·
                    refine ⟨433319820241028109394037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155519520642741625050765 433319820241028109394037)
                    ·
                      rfl

theorem cell22_1265831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1265831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265831 prefixEnd_1265831 := by exact prefixLift 1265831
  have htrace : WordTrace (prefixWord ++ tailWord_1265831) baseStart_1265831 baseEnd_1265831 := by
    simpa [prefixWord, tailWord_1265831, baseEnd_1265831] using wordTrace_append hprefix tailTrace_1265831
  have hstable : (prefixWord ++ tailWord_1265831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265831).length < 2 ^ (prefixWord ++ tailWord_1265831).sum := by decide
  have hdescent : baseEnd_1265831 < baseStart_1265831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265842 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_1265842 : Nat := 118140960795 + 1265842 * 2 ^ 59
def prefixEnd_1265842 : Nat := 4983230072969 + 3 ^ 40 * 1265842 * 2
def baseEnd_1265842 : Nat := 433323585765827747369003

theorem tailTrace_1265842 : CollatzResearch.WordTrace tailWord_1265842 prefixEnd_1265842 433323585765827747369003 := by
  unfold tailWord_1265842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11542262670019524361763945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30779367120052064964703853 11542262670019524361763945)
  ·
    refine ⟨8656697002514643271322959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11542262670019524361763945 8656697002514643271322959)
    ·
      refine ⟨12985045503771964906984439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656697002514643271322959 12985045503771964906984439)
      ·
        refine ⟨19477568255657947360476659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12985045503771964906984439 19477568255657947360476659)
        ·
          refine ⟨29216352383486921040714989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19477568255657947360476659 29216352383486921040714989)
          ·
            refine ⟨10956132143807595390268121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29216352383486921040714989 10956132143807595390268121)
            ·
              refine ⟨8217099107855696542701091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10956132143807595390268121 8217099107855696542701091)
              ·
                refine ⟨12325648661783544814051637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8217099107855696542701091 12325648661783544814051637)
                ·
                  refine ⟨1155529562042207326317341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12325648661783544814051637 1155529562042207326317341)
                  ·
                    refine ⟨433323585765827747369003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155529562042207326317341 433323585765827747369003)
                    ·
                      rfl

theorem cell22_1265842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_1265842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265842 prefixEnd_1265842 := by exact prefixLift 1265842
  have htrace : WordTrace (prefixWord ++ tailWord_1265842) baseStart_1265842 baseEnd_1265842 := by
    simpa [prefixWord, tailWord_1265842, baseEnd_1265842] using wordTrace_append hprefix tailTrace_1265842
  have hstable : (prefixWord ++ tailWord_1265842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265842).length < 2 ^ (prefixWord ++ tailWord_1265842).sum := by decide
  have hdescent : baseEnd_1265842 < baseStart_1265842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265934 : List Nat := [4, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_1265934 : Nat := 118140960795 + 1265934 * 2 ^ 59
def prefixEnd_1265934 : Nat := 4983230072969 + 3 ^ 40 * 1265934 * 2
def baseEnd_1265934 : Nat := 144451693081990058022907

theorem tailTrace_1265934 : CollatzResearch.WordTrace tailWord_1265934 prefixEnd_1265934 144451693081990058022907 := by
  unfold tailWord_1265934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5771550774468099644925607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30781604130496531439603237 5771550774468099644925607)
  ·
    refine ⟨8657326161702149467388411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5771550774468099644925607 8657326161702149467388411)
    ·
      refine ⟨12985989242553224201082617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8657326161702149467388411 12985989242553224201082617)
      ·
        refine ⟨9739491931914918150811963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12985989242553224201082617 9739491931914918150811963)
        ·
          refine ⟨14609237897872377226217945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9739491931914918150811963 14609237897872377226217945)
          ·
            refine ⟨10956928423404282919663459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14609237897872377226217945 10956928423404282919663459)
            ·
              refine ⟨16435392635106424379495189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10956928423404282919663459 16435392635106424379495189)
              ·
                refine ⟨770409029770613642788837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16435392635106424379495189 770409029770613642788837)
                ·
                  refine ⟨144451693081990058022907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 770409029770613642788837 144451693081990058022907)
                  ·
                    rfl

theorem cell22_1265934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_1265934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1265934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1265934 prefixEnd_1265934 := by exact prefixLift 1265934
  have htrace : WordTrace (prefixWord ++ tailWord_1265934) baseStart_1265934 baseEnd_1265934 := by
    simpa [prefixWord, tailWord_1265934, baseEnd_1265934] using wordTrace_append hprefix tailTrace_1265934
  have hstable : (prefixWord ++ tailWord_1265934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265934).length < 2 ^ (prefixWord ++ tailWord_1265934).sum := by decide
  have hdescent : baseEnd_1265934 < baseStart_1265934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266045 : List Nat := [1, 4, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_1266045 : Nat := 118140960795 + 1266045 * 2 ^ 59
def prefixEnd_1266045 : Nat := 4983230072969 + 3 ^ 40 * 1266045 * 2
def baseEnd_1266045 : Nat := 433393076814402884543381

theorem tailTrace_1266045 : CollatzResearch.WordTrace tailWord_1266045 prefixEnd_1266045 433393076814402884543381 := by
  unfold tailWord_1266045
  simp only [CollatzResearch.WordTrace]
  refine ⟨46176454698342663116695589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30784303132228442077797059 46176454698342663116695589)
  ·
    refine ⟨8658085255939249334380423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46176454698342663116695589 8658085255939249334380423)
    ·
      refine ⟨12987127883908874001570635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8658085255939249334380423 12987127883908874001570635)
      ·
        refine ⟨19480691825863311002355953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12987127883908874001570635 19480691825863311002355953)
        ·
          refine ⟨14610518869397483251766965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19480691825863311002355953 14610518869397483251766965)
          ·
            refine ⟨1369736144006014054853153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14610518869397483251766965 1369736144006014054853153)
            ·
              refine ⟨1027302108004510541139865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369736144006014054853153 1027302108004510541139865)
              ·
                refine ⟨770476581003382905854899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027302108004510541139865 770476581003382905854899)
                ·
                  refine ⟨1155714871505074358782349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770476581003382905854899 1155714871505074358782349)
                  ·
                    refine ⟨433393076814402884543381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155714871505074358782349 433393076814402884543381)
                    ·
                      rfl

theorem cell22_1266045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_1266045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266045 prefixEnd_1266045 := by exact prefixLift 1266045
  have htrace : WordTrace (prefixWord ++ tailWord_1266045) baseStart_1266045 baseEnd_1266045 := by
    simpa [prefixWord, tailWord_1266045, baseEnd_1266045] using wordTrace_append hprefix tailTrace_1266045
  have hstable : (prefixWord ++ tailWord_1266045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266045).length < 2 ^ (prefixWord ++ tailWord_1266045).sum := by decide
  have hdescent : baseEnd_1266045 < baseStart_1266045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266084 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1266084 : Nat := 118140960795 + 1266084 * 2 ^ 59
def prefixEnd_1266084 : Nat := 4983230072969 + 3 ^ 40 * 1266084 * 2
def baseEnd_1266084 : Nat := 433406427311419782818261

theorem tailTrace_1266084 : CollatzResearch.WordTrace tailWord_1266084 prefixEnd_1266084 433406427311419782818261 := by
  unfold tailWord_1266084
  simp only [CollatzResearch.WordTrace]
  refine ⟨23088938572600686388682653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30785251430134248518243537 23088938572600686388682653)
  ·
    refine ⟨8658351964725257395755995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23088938572600686388682653 8658351964725257395755995)
    ·
      refine ⟨12987527947087886093633993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8658351964725257395755995 12987527947087886093633993)
      ·
        refine ⟨9740645960315914570225495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12987527947087886093633993 9740645960315914570225495)
        ·
          refine ⟨14610968940473871855338243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9740645960315914570225495 14610968940473871855338243)
          ·
            refine ⟨21916453410710807783007365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14610968940473871855338243 21916453410710807783007365)
            ·
              refine ⟨4109335014508276459313881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21916453410710807783007365 4109335014508276459313881)
              ·
                refine ⟨3082001260881207344485411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4109335014508276459313881 3082001260881207344485411)
                ·
                  refine ⟨4623001891321811016728117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082001260881207344485411 4623001891321811016728117)
                  ·
                    refine ⟨433406427311419782818261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4623001891321811016728117 433406427311419782818261)
                    ·
                      rfl

theorem cell22_1266084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1266084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266084 prefixEnd_1266084 := by exact prefixLift 1266084
  have htrace : WordTrace (prefixWord ++ tailWord_1266084) baseStart_1266084 baseEnd_1266084 := by
    simpa [prefixWord, tailWord_1266084, baseEnd_1266084] using wordTrace_append hprefix tailTrace_1266084
  have hstable : (prefixWord ++ tailWord_1266084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266084).length < 2 ^ (prefixWord ++ tailWord_1266084).sum := by decide
  have hdescent : baseEnd_1266084 < baseStart_1266084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266088 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1266088 : Nat := 118140960795 + 1266088 * 2 ^ 59
def prefixEnd_1266088 : Nat := 4983230072969 + 3 ^ 40 * 1266088 * 2
def baseEnd_1266088 : Nat := 433407796593165105718249

theorem tailTrace_1266088 : CollatzResearch.WordTrace tailWord_1266088 prefixEnd_1266088 433407796593165105718249 := by
  unfold tailWord_1266088
  simp only [CollatzResearch.WordTrace]
  refine ⟨23089011518593440730255459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30785348691457920973673945 23089011518593440730255459)
  ·
    refine ⟨34633517277890161095383189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23089011518593440730255459 34633517277890161095383189)
    ·
      refine ⟨1623446122401101301346087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34633517277890161095383189 1623446122401101301346087)
      ·
        refine ⟨2435169183601651952019131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623446122401101301346087 2435169183601651952019131)
        ·
          refine ⟨3652753775402477928028697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435169183601651952019131 3652753775402477928028697)
          ·
            refine ⟨2739565331551858446021523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3652753775402477928028697 2739565331551858446021523)
            ·
              refine ⟨4109347997327787669032285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739565331551858446021523 4109347997327787669032285)
              ·
                refine ⟨1541005498997920375887107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4109347997327787669032285 1541005498997920375887107)
                ·
                  refine ⟨2311508248496880563830661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541005498997920375887107 2311508248496880563830661)
                  ·
                    refine ⟨433407796593165105718249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2311508248496880563830661 433407796593165105718249)
                    ·
                      rfl

theorem cell22_1266088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1266088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266088 prefixEnd_1266088 := by exact prefixLift 1266088
  have htrace : WordTrace (prefixWord ++ tailWord_1266088) baseStart_1266088 baseEnd_1266088 := by
    simpa [prefixWord, tailWord_1266088, baseEnd_1266088] using wordTrace_append hprefix tailTrace_1266088
  have hstable : (prefixWord ++ tailWord_1266088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266088).length < 2 ^ (prefixWord ++ tailWord_1266088).sum := by decide
  have hdescent : baseEnd_1266088 < baseStart_1266088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266159 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 5]
def baseStart_1266159 : Nat := 118140960795 + 1266159 * 2 ^ 59
def prefixEnd_1266159 : Nat := 4983230072969 + 3 ^ 40 * 1266159 * 2
def baseEnd_1266159 : Nat := 144477367114714862397677

theorem tailTrace_1266159 : CollatzResearch.WordTrace tailWord_1266159 prefixEnd_1266159 144477367114714862397677 := by
  unfold tailWord_1266159
  simp only [CollatzResearch.WordTrace]
  refine ⟨46180612619929660586345531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30787075079953107057563687 46180612619929660586345531)
  ·
    refine ⟨69270918929894490879518297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46180612619929660586345531 69270918929894490879518297)
    ·
      refine ⟨51953189197420868159638723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69270918929894490879518297 51953189197420868159638723)
      ·
        refine ⟨77929783796131302239458085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51953189197420868159638723 77929783796131302239458085)
        ·
          refine ⟨14611834461774619169898391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77929783796131302239458085 14611834461774619169898391)
          ·
            refine ⟨21917751692661928754847587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14611834461774619169898391 21917751692661928754847587)
            ·
              refine ⟨32876627538992893132271381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21917751692661928754847587 32876627538992893132271381)
              ·
                refine ⟨1541091915890291865575221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32876627538992893132271381 1541091915890291865575221)
                ·
                  refine ⟨144477367114714862397677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1541091915890291865575221 144477367114714862397677)
                  ·
                    rfl

theorem cell22_1266159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 5].length) (baseStart_1266159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266159 prefixEnd_1266159 := by exact prefixLift 1266159
  have htrace : WordTrace (prefixWord ++ tailWord_1266159) baseStart_1266159 baseEnd_1266159 := by
    simpa [prefixWord, tailWord_1266159, baseEnd_1266159] using wordTrace_append hprefix tailTrace_1266159
  have hstable : (prefixWord ++ tailWord_1266159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266159).length < 2 ^ (prefixWord ++ tailWord_1266159).sum := by decide
  have hdescent : baseEnd_1266159 < baseStart_1266159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266236 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1266236 : Nat := 118140960795 + 1266236 * 2 ^ 59
def prefixEnd_1266236 : Nat := 4983230072969 + 3 ^ 40 * 1266236 * 2
def baseEnd_1266236 : Nat := 433458460017742053017795

theorem tailTrace_1266236 : CollatzResearch.WordTrace tailWord_1266236 prefixEnd_1266236 433458460017742053017795 := by
  unfold tailWord_1266236
  simp only [CollatzResearch.WordTrace]
  refine ⟨23091710520325351368449281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30788947360433801824599041 23091710520325351368449281)
  ·
    refine ⟨17318782890244013526336961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23091710520325351368449281 17318782890244013526336961)
    ·
      refine ⟨12989087167683010144752721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17318782890244013526336961 12989087167683010144752721)
      ·
        refine ⟨9741815375762257608564541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12989087167683010144752721 9741815375762257608564541)
        ·
          refine ⟨3653180765910846603211703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9741815375762257608564541 3653180765910846603211703)
          ·
            refine ⟨5479771148866269904817555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653180765910846603211703 5479771148866269904817555)
            ·
              refine ⟨8219656723299404857226333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479771148866269904817555 8219656723299404857226333)
              ·
                refine ⟨3082371271237276821459875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8219656723299404857226333 3082371271237276821459875)
                ·
                  refine ⟨4623556906855915232189813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082371271237276821459875 4623556906855915232189813)
                  ·
                    refine ⟨433458460017742053017795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4623556906855915232189813 433458460017742053017795)
                    ·
                      rfl

theorem cell22_1266236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1266236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266236 prefixEnd_1266236 := by exact prefixLift 1266236
  have htrace : WordTrace (prefixWord ++ tailWord_1266236) baseStart_1266236 baseEnd_1266236 := by
    simpa [prefixWord, tailWord_1266236, baseEnd_1266236] using wordTrace_append hprefix tailTrace_1266236
  have hstable : (prefixWord ++ tailWord_1266236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266236).length < 2 ^ (prefixWord ++ tailWord_1266236).sum := by decide
  have hdescent : baseEnd_1266236 < baseStart_1266236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266251 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 2, 4]
def baseStart_1266251 : Nat := 118140960795 + 1266251 * 2 ^ 59
def prefixEnd_1266251 : Nat := 4983230072969 + 3 ^ 40 * 1266251 * 2
def baseEnd_1266251 : Nat := 433463594824287013892749

theorem tailTrace_1266251 : CollatzResearch.WordTrace tailWord_1266251 prefixEnd_1266251 433463594824287013892749 := by
  unfold tailWord_1266251
  simp only [CollatzResearch.WordTrace]
  refine ⟨46183968135596360298694607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30789312090397573532463071 46183968135596360298694607)
  ·
    refine ⟨69275952203394540448041911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46183968135596360298694607 69275952203394540448041911)
    ·
      refine ⟨103913928305091810672062867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69275952203394540448041911 103913928305091810672062867)
      ·
        refine ⟨155870892457637716008094301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103913928305091810672062867 155870892457637716008094301)
        ·
          refine ⟨58451584671614143503035363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155870892457637716008094301 58451584671614143503035363)
          ·
            refine ⟨87677377007421215254553045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58451584671614143503035363 87677377007421215254553045)
            ·
              refine ⟨2054938523611434732528587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87677377007421215254553045 2054938523611434732528587)
              ·
                refine ⟨3082407785417152098792881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054938523611434732528587 3082407785417152098792881)
                ·
                  refine ⟨2311805839062864074094661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3082407785417152098792881 2311805839062864074094661)
                  ·
                    refine ⟨433463594824287013892749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2311805839062864074094661 433463594824287013892749)
                    ·
                      rfl

theorem cell22_1266251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4].length) (baseStart_1266251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266251 prefixEnd_1266251 := by exact prefixLift 1266251
  have htrace : WordTrace (prefixWord ++ tailWord_1266251) baseStart_1266251 baseEnd_1266251 := by
    simpa [prefixWord, tailWord_1266251, baseEnd_1266251] using wordTrace_append hprefix tailTrace_1266251
  have hstable : (prefixWord ++ tailWord_1266251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266251).length < 2 ^ (prefixWord ++ tailWord_1266251).sum := by decide
  have hdescent : baseEnd_1266251 < baseStart_1266251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266253 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1266253 : Nat := 118140960795 + 1266253 * 2 ^ 59
def prefixEnd_1266253 : Nat := 4983230072969 + 3 ^ 40 * 1266253 * 2
def baseEnd_1266253 : Nat := 433464279465159675342743

theorem tailTrace_1266253 : CollatzResearch.WordTrace tailWord_1266253 prefixEnd_1266253 433464279465159675342743 := by
  unfold tailWord_1266253
  simp only [CollatzResearch.WordTrace]
  refine ⟨46184041081589114640267413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30789360721059409760178275 46184041081589114640267413)
  ·
    refine ⟨2164876925699489748762535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46184041081589114640267413 2164876925699489748762535)
    ·
      refine ⟨3247315388549234623143803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164876925699489748762535 3247315388549234623143803)
      ·
        refine ⟨4870973082823851934715705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247315388549234623143803 4870973082823851934715705)
        ·
          refine ⟨3653229812117888951036779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4870973082823851934715705 3653229812117888951036779)
          ·
            refine ⟨5479844718176833426555169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653229812117888951036779 5479844718176833426555169)
            ·
              refine ⟨4109883538632625069916377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5479844718176833426555169 4109883538632625069916377)
              ·
                refine ⟨3082412653974468802437283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4109883538632625069916377 3082412653974468802437283)
                ·
                  refine ⟨4623618980961703203655925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082412653974468802437283 4623618980961703203655925)
                  ·
                    refine ⟨433464279465159675342743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4623618980961703203655925 433464279465159675342743)
                    ·
                      rfl

theorem cell22_1266253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1266253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266253 prefixEnd_1266253 := by exact prefixLift 1266253
  have htrace : WordTrace (prefixWord ++ tailWord_1266253) baseStart_1266253 baseEnd_1266253 := by
    simpa [prefixWord, tailWord_1266253, baseEnd_1266253] using wordTrace_append hprefix tailTrace_1266253
  have hstable : (prefixWord ++ tailWord_1266253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266253).length < 2 ^ (prefixWord ++ tailWord_1266253).sum := by decide
  have hdescent : baseEnd_1266253 < baseStart_1266253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266306 : List Nat := [3, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1266306 : Nat := 118140960795 + 1266306 * 2 ^ 59
def prefixEnd_1266306 : Nat := 4983230072969 + 3 ^ 40 * 1266306 * 2
def baseEnd_1266306 : Nat := 144494140816095067922527

theorem tailTrace_1266306 : CollatzResearch.WordTrace tailWord_1266306 prefixEnd_1266306 144494140816095067922527 := by
  unfold tailWord_1266306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11546493537599276172986693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30790649433598069794631181 11546493537599276172986693)
  ·
    refine ⟨2164967538299864282435005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11546493537599276172986693 2164967538299864282435005)
    ·
      refine ⟨811862826862449105913127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2164967538299864282435005 811862826862449105913127)
      ·
        refine ⟨1217794240293673658869691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811862826862449105913127 1217794240293673658869691)
        ·
          refine ⟨1826691360440510488304537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217794240293673658869691 1826691360440510488304537)
          ·
            refine ⟨1370018520330382866228403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826691360440510488304537 1370018520330382866228403)
            ·
              refine ⟨2055027780495574299342605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370018520330382866228403 2055027780495574299342605)
              ·
                refine ⟨770635417685840362253477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2055027780495574299342605 770635417685840362253477)
                ·
                  refine ⟨144494140816095067922527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 770635417685840362253477 144494140816095067922527)
                  ·
                    rfl

theorem cell22_1266306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1266306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266306 prefixEnd_1266306 := by exact prefixLift 1266306
  have htrace : WordTrace (prefixWord ++ tailWord_1266306) baseStart_1266306 baseEnd_1266306 := by
    simpa [prefixWord, tailWord_1266306, baseEnd_1266306] using wordTrace_append hprefix tailTrace_1266306
  have hstable : (prefixWord ++ tailWord_1266306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266306).length < 2 ^ (prefixWord ++ tailWord_1266306).sum := by decide
  have hdescent : baseEnd_1266306 < baseStart_1266306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266341 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_1266341 : Nat := 118140960795 + 1266341 * 2 ^ 59
def prefixEnd_1266341 : Nat := 4983230072969 + 3 ^ 40 * 1266341 * 2
def baseEnd_1266341 : Nat := 433494403663556779142473

theorem tailTrace_1266341 : CollatzResearch.WordTrace tailWord_1266341 prefixEnd_1266341 433494403663556779142473 := by
  unfold tailWord_1266341
  simp only [CollatzResearch.WordTrace]
  refine ⟨46187250705270305669470877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30791500470180203779647251 46187250705270305669470877)
  ·
    refine ⟨17320219014476364626051579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46187250705270305669470877 17320219014476364626051579)
    ·
      refine ⟨25980328521714546939077369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17320219014476364626051579 25980328521714546939077369)
      ·
        refine ⟨19485246391285910204308027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25980328521714546939077369 19485246391285910204308027)
        ·
          refine ⟨29227869586928865306462041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19485246391285910204308027 29227869586928865306462041)
          ·
            refine ⟨21920902190196648979846531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29227869586928865306462041 21920902190196648979846531)
            ·
              refine ⟨32881353285294973469769797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21920902190196648979846531 32881353285294973469769797)
              ·
                refine ⟨6165253740992807525581837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32881353285294973469769797 6165253740992807525581837)
                ·
                  refine ⟨2311970152872302822093189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6165253740992807525581837 2311970152872302822093189)
                  ·
                    refine ⟨433494403663556779142473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2311970152872302822093189 433494403663556779142473)
                    ·
                      rfl

theorem cell22_1266341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_1266341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266341 prefixEnd_1266341 := by exact prefixLift 1266341
  have htrace : WordTrace (prefixWord ++ tailWord_1266341) baseStart_1266341 baseEnd_1266341 := by
    simpa [prefixWord, tailWord_1266341, baseEnd_1266341] using wordTrace_append hprefix tailTrace_1266341
  have hstable : (prefixWord ++ tailWord_1266341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266341).length < 2 ^ (prefixWord ++ tailWord_1266341).sum := by decide
  have hdescent : baseEnd_1266341 < baseStart_1266341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266405 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_1266405 : Nat := 118140960795 + 1266405 * 2 ^ 59
def prefixEnd_1266405 : Nat := 4983230072969 + 3 ^ 40 * 1266405 * 2
def baseEnd_1266405 : Nat := 433516312171481945542277

theorem tailTrace_1266405 : CollatzResearch.WordTrace tailWord_1266405 prefixEnd_1266405 433516312171481945542277 := by
  unfold tailWord_1266405
  simp only [CollatzResearch.WordTrace]
  refine ⟨46189584977038444599800669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30793056651358963066533779 46189584977038444599800669)
  ·
    refine ⟨17321094366389416724925251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46189584977038444599800669 17321094366389416724925251)
    ·
      refine ⟨25981641549584125087387877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17321094366389416724925251 25981641549584125087387877)
      ·
        refine ⟨4871557790547023453885227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25981641549584125087387877 4871557790547023453885227)
        ·
          refine ⟨7307336685820535180827841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4871557790547023453885227 7307336685820535180827841)
          ·
            refine ⟨5480502514365401385620881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7307336685820535180827841 5480502514365401385620881)
            ·
              refine ⟨4110376885774051039215661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5480502514365401385620881 4110376885774051039215661)
              ·
                refine ⟨1541391332165269139705873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4110376885774051039215661 1541391332165269139705873)
                ·
                  refine ⟨1156043499123951854779405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1541391332165269139705873 1156043499123951854779405)
                  ·
                    refine ⟨433516312171481945542277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156043499123951854779405 433516312171481945542277)
                    ·
                      rfl

theorem cell22_1266405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_1266405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266405 prefixEnd_1266405 := by exact prefixLift 1266405
  have htrace : WordTrace (prefixWord ++ tailWord_1266405) baseStart_1266405 baseEnd_1266405 := by
    simpa [prefixWord, tailWord_1266405, baseEnd_1266405] using wordTrace_append hprefix tailTrace_1266405
  have hstable : (prefixWord ++ tailWord_1266405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266405).length < 2 ^ (prefixWord ++ tailWord_1266405).sum := by decide
  have hdescent : baseEnd_1266405 < baseStart_1266405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266433 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1266433 : Nat := 118140960795 + 1266433 * 2 ^ 59
def prefixEnd_1266433 : Nat := 4983230072969 + 3 ^ 40 * 1266433 * 2
def baseEnd_1266433 : Nat := 433525897143699205842191

theorem tailTrace_1266433 : CollatzResearch.WordTrace tailWord_1266433 prefixEnd_1266433 433525897143699205842191 := by
  unfold tailWord_1266433
  simp only [CollatzResearch.WordTrace]
  refine ⟨46190606220937005381819953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30793737480624670254546635 46190606220937005381819953)
  ·
    refine ⟨34642954665702754036364965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46190606220937005381819953 34642954665702754036364965)
    ·
      refine ⟨6495553999819266381818431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34642954665702754036364965 6495553999819266381818431)
      ·
        refine ⟨9743330999728899572727647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6495553999819266381818431 9743330999728899572727647)
        ·
          refine ⟨14614996499593349359091471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9743330999728899572727647 14614996499593349359091471)
          ·
            refine ⟨21922494749390024038637207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14614996499593349359091471 21922494749390024038637207)
            ·
              refine ⟨32883742124085036057955811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21922494749390024038637207 32883742124085036057955811)
              ·
                refine ⟨49325613186127554086933717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32883742124085036057955811 49325613186127554086933717)
                ·
                  refine ⟨1156069059049864548912509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 49325613186127554086933717 1156069059049864548912509)
                  ·
                    refine ⟨433525897143699205842191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156069059049864548912509 433525897143699205842191)
                    ·
                      rfl

theorem cell22_1266433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1266433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266433 prefixEnd_1266433 := by exact prefixLift 1266433
  have htrace : WordTrace (prefixWord ++ tailWord_1266433) baseStart_1266433 baseEnd_1266433 := by
    simpa [prefixWord, tailWord_1266433, baseEnd_1266433] using wordTrace_append hprefix tailTrace_1266433
  have hstable : (prefixWord ++ tailWord_1266433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266433).length < 2 ^ (prefixWord ++ tailWord_1266433).sum := by decide
  have hdescent : baseEnd_1266433 < baseStart_1266433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266570 : List Nat := [3, 1, 2, 4, 1, 1, 3, 7]
def baseStart_1266570 : Nat := 118140960795 + 1266570 * 2 ^ 59
def prefixEnd_1266570 : Nat := 4983230072969 + 3 ^ 40 * 1266570 * 2
def baseEnd_1266570 : Nat := 48174755004830723907419

theorem tailTrace_1266570 : CollatzResearch.WordTrace tailWord_1266570 prefixEnd_1266570 48174755004830723907419 := by
  unfold tailWord_1266570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11548900755360169444889291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30797068680960451853038109 11548900755360169444889291)
  ·
    refine ⟨17323351133040254167333937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11548900755360169444889291 17323351133040254167333937)
    ·
      refine ⟨12992513349780190625500453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17323351133040254167333937 12992513349780190625500453)
      ·
        refine ⟨2436096253083785742281335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12992513349780190625500453 2436096253083785742281335)
        ·
          refine ⟨3654144379625678613422003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436096253083785742281335 3654144379625678613422003)
          ·
            refine ⟨5481216569438517920133005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654144379625678613422003 5481216569438517920133005)
            ·
              refine ⟨2055456213539444220049877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5481216569438517920133005 2055456213539444220049877)
              ·
                refine ⟨48174755004830723907419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2055456213539444220049877 48174755004830723907419)
                ·
                  rfl

theorem cell22_1266570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_1266570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266570 prefixEnd_1266570 := by exact prefixLift 1266570
  have htrace : WordTrace (prefixWord ++ tailWord_1266570) baseStart_1266570 baseEnd_1266570 := by
    simpa [prefixWord, tailWord_1266570, baseEnd_1266570] using wordTrace_append hprefix tailTrace_1266570
  have hstable : (prefixWord ++ tailWord_1266570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266570).length < 2 ^ (prefixWord ++ tailWord_1266570).sum := by decide
  have hdescent : baseEnd_1266570 < baseStart_1266570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266583 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 2, 6]
def baseStart_1266583 : Nat := 118140960795 + 1266583 * 2 ^ 59
def prefixEnd_1266583 : Nat := 4983230072969 + 3 ^ 40 * 1266583 * 2
def baseEnd_1266583 : Nat := 433577245209148814591731

theorem tailTrace_1266583 : CollatzResearch.WordTrace tailWord_1266583 prefixEnd_1266583 433577245209148814591731 := by
  unfold tailWord_1266583
  simp only [CollatzResearch.WordTrace]
  refine ⟨46196077170393580999780403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30797384780262387333186935 46196077170393580999780403)
  ·
    refine ⟨69294115755590371499670605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46196077170393580999780403 69294115755590371499670605)
    ·
      refine ⟨25985293408346389312376477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69294115755590371499670605 25985293408346389312376477)
      ·
        refine ⟨9744485028129895992141179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25985293408346389312376477 9744485028129895992141179)
        ·
          refine ⟨14616727542194843988211769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9744485028129895992141179 14616727542194843988211769)
          ·
            refine ⟨10962545656646132991158827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14616727542194843988211769 10962545656646132991158827)
            ·
              refine ⟨16443818484969199486738241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10962545656646132991158827 16443818484969199486738241)
              ·
                refine ⟨12332863863726899615053681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16443818484969199486738241 12332863863726899615053681)
                ·
                  refine ⟨9249647897795174711290261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12332863863726899615053681 9249647897795174711290261)
                  ·
                    refine ⟨433577245209148814591731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9249647897795174711290261 433577245209148814591731)
                    ·
                      rfl

theorem cell22_1266583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_1266583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266583 prefixEnd_1266583 := by exact prefixLift 1266583
  have htrace : WordTrace (prefixWord ++ tailWord_1266583) baseStart_1266583 baseEnd_1266583 := by
    simpa [prefixWord, tailWord_1266583, baseEnd_1266583] using wordTrace_append hprefix tailTrace_1266583
  have hstable : (prefixWord ++ tailWord_1266583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266583).length < 2 ^ (prefixWord ++ tailWord_1266583).sum := by decide
  have hdescent : baseEnd_1266583 < baseStart_1266583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266615 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 5]
def baseStart_1266615 : Nat := 118140960795 + 1266615 * 2 ^ 59
def prefixEnd_1266615 : Nat := 4983230072969 + 3 ^ 40 * 1266615 * 2
def baseEnd_1266615 : Nat := 144529399821037132597211

theorem tailTrace_1266615 : CollatzResearch.WordTrace tailWord_1266615 prefixEnd_1266615 144529399821037132597211 := by
  unfold tailWord_1266615
  simp only [CollatzResearch.WordTrace]
  refine ⟨46197244306277650464945299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30798162870851766976630199 46197244306277650464945299)
  ·
    refine ⟨69295866459416475697417949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46197244306277650464945299 69295866459416475697417949)
    ·
      refine ⟨25985949922281178386531731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69295866459416475697417949 25985949922281178386531731)
      ·
        refine ⟨38978924883421767579797597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25985949922281178386531731 38978924883421767579797597)
        ·
          refine ⟨14617096831283162842424099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38978924883421767579797597 14617096831283162842424099)
          ·
            refine ⟨21925645246924744263636149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14617096831283162842424099 21925645246924744263636149)
            ·
              refine ⟨2055529241899194774715889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21925645246924744263636149 2055529241899194774715889)
              ·
                refine ⟨1541646931424396081036917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055529241899194774715889 1541646931424396081036917)
                ·
                  refine ⟨144529399821037132597211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1541646931424396081036917 144529399821037132597211)
                  ·
                    rfl

theorem cell22_1266615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 5].length) (baseStart_1266615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266615 prefixEnd_1266615 := by exact prefixLift 1266615
  have htrace : WordTrace (prefixWord ++ tailWord_1266615) baseStart_1266615 baseEnd_1266615 := by
    simpa [prefixWord, tailWord_1266615, baseEnd_1266615] using wordTrace_append hprefix tailTrace_1266615
  have hstable : (prefixWord ++ tailWord_1266615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266615).length < 2 ^ (prefixWord ++ tailWord_1266615).sum := by decide
  have hdescent : baseEnd_1266615 < baseStart_1266615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266737 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 3, 3]
def baseStart_1266737 : Nat := 118140960795 + 1266737 * 2 ^ 59
def prefixEnd_1266737 : Nat := 4983230072969 + 3 ^ 40 * 1266737 * 2
def baseEnd_1266737 : Nat := 433629962556343746241259

theorem tailTrace_1266737 : CollatzResearch.WordTrace tailWord_1266737 prefixEnd_1266737 433629962556343746241259 := by
  unfold tailWord_1266737
  simp only [CollatzResearch.WordTrace]
  refine ⟨46201694011835665300886465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30801129341223776867257643 46201694011835665300886465)
  ·
    refine ⟨34651270508876748975664849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46201694011835665300886465 34651270508876748975664849)
    ·
      refine ⟨25988452881657561731748637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34651270508876748975664849 25988452881657561731748637)
      ·
        refine ⟨9745669830621585649405739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25988452881657561731748637 9745669830621585649405739)
        ·
          refine ⟨14618504745932378474108609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9745669830621585649405739 14618504745932378474108609)
          ·
            refine ⟨10963878559449283855581457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14618504745932378474108609 10963878559449283855581457)
            ·
              refine ⟨8222908919586962891686093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10963878559449283855581457 8222908919586962891686093)
              ·
                refine ⟨3083590844845111084382285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8222908919586962891686093 3083590844845111084382285)
                ·
                  refine ⟨1156346566816916656643357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3083590844845111084382285 1156346566816916656643357)
                  ·
                    refine ⟨433629962556343746241259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156346566816916656643357 433629962556343746241259)
                    ·
                      rfl

theorem cell22_1266737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_1266737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266737 prefixEnd_1266737 := by exact prefixLift 1266737
  have htrace : WordTrace (prefixWord ++ tailWord_1266737) baseStart_1266737 baseEnd_1266737 := by
    simpa [prefixWord, tailWord_1266737, baseEnd_1266737] using wordTrace_append hprefix tailTrace_1266737
  have hstable : (prefixWord ++ tailWord_1266737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266737).length < 2 ^ (prefixWord ++ tailWord_1266737).sum := by decide
  have hdescent : baseEnd_1266737 < baseStart_1266737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266844 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1266844 : Nat := 118140960795 + 1266844 * 2 ^ 59
def prefixEnd_1266844 : Nat := 4983230072969 + 3 ^ 40 * 1266844 * 2
def baseEnd_1266844 : Nat := 433666590843031133815931

theorem tailTrace_1266844 : CollatzResearch.WordTrace tailWord_1266844 prefixEnd_1266844 433666590843031133815931 := by
  unfold tailWord_1266844
  simp only [CollatzResearch.WordTrace]
  refine ⟨23102798311224011287515793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30803731081632015050021057 23102798311224011287515793)
  ·
    refine ⟨17327098733418008465636845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23102798311224011287515793 17327098733418008465636845)
    ·
      refine ⟨6497662025031753174613817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17327098733418008465636845 6497662025031753174613817)
      ·
        refine ⟨4873246518773814880960363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6497662025031753174613817 4873246518773814880960363)
        ·
          refine ⟨7309869778160722321440545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873246518773814880960363 7309869778160722321440545)
          ·
            refine ⟨5482402333620541741080409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7309869778160722321440545 5482402333620541741080409)
            ·
              refine ⟨4111801750215406305810307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5482402333620541741080409 4111801750215406305810307)
              ·
                refine ⟨6167702625323109458715461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111801750215406305810307 6167702625323109458715461)
                ·
                  refine ⟨1156444242248083023509149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6167702625323109458715461 1156444242248083023509149)
                  ·
                    refine ⟨433666590843031133815931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156444242248083023509149 433666590843031133815931)
                    ·
                      rfl

theorem cell22_1266844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1266844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266844 prefixEnd_1266844 := by exact prefixLift 1266844
  have htrace : WordTrace (prefixWord ++ tailWord_1266844) baseStart_1266844 baseEnd_1266844 := by
    simpa [prefixWord, tailWord_1266844, baseEnd_1266844] using wordTrace_append hprefix tailTrace_1266844
  have hstable : (prefixWord ++ tailWord_1266844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266844).length < 2 ^ (prefixWord ++ tailWord_1266844).sum := by decide
  have hdescent : baseEnd_1266844 < baseStart_1266844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266846 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1266846 : Nat := 118140960795 + 1266846 * 2 ^ 59
def prefixEnd_1266846 : Nat := 4983230072969 + 3 ^ 40 * 1266846 * 2
def baseEnd_1266846 : Nat := 144555758494634598421975

theorem tailTrace_1266846 : CollatzResearch.WordTrace tailWord_1266846 prefixEnd_1266846 144555758494634598421975 := by
  unfold tailWord_1266846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775708696055097114575549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30803779712293851277736261 5775708696055097114575549)
  ·
    refine ⟨2165890761020661417965831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5775708696055097114575549 2165890761020661417965831)
    ·
      refine ⟨3248836141530992126948747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2165890761020661417965831 3248836141530992126948747)
      ·
        refine ⟨4873254212296488190423121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248836141530992126948747 4873254212296488190423121)
        ·
          refine ⟨3654940659222366142817341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4873254212296488190423121 3654940659222366142817341)
          ·
            refine ⟨1370602747208387303556503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3654940659222366142817341 1370602747208387303556503)
            ·
              refine ⟨2055904120812580955334755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370602747208387303556503 2055904120812580955334755)
              ·
                refine ⟨3083856181218871433002133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055904120812580955334755 3083856181218871433002133)
                ·
                  refine ⟨144555758494634598421975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3083856181218871433002133 144555758494634598421975)
                  ·
                    rfl

theorem cell22_1266846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1266846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266846 prefixEnd_1266846 := by exact prefixLift 1266846
  have htrace : WordTrace (prefixWord ++ tailWord_1266846) baseStart_1266846 baseEnd_1266846 := by
    simpa [prefixWord, tailWord_1266846, baseEnd_1266846] using wordTrace_append hprefix tailTrace_1266846
  have hstable : (prefixWord ++ tailWord_1266846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266846).length < 2 ^ (prefixWord ++ tailWord_1266846).sum := by decide
  have hdescent : baseEnd_1266846 < baseStart_1266846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266949 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_1266949 : Nat := 118140960795 + 1266949 * 2 ^ 59
def prefixEnd_1266949 : Nat := 4983230072969 + 3 ^ 40 * 1266949 * 2
def baseEnd_1266949 : Nat := 433702534488845859940609

theorem tailTrace_1266949 : CollatzResearch.WordTrace tailWord_1266949 prefixEnd_1266949 433702534488845859940609 := by
  unfold tailWord_1266949
  simp only [CollatzResearch.WordTrace]
  refine ⟨46209426287067625507603901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30806284191378417005069267 46209426287067625507603901)
  ·
    refine ⟨17328534857650359565351463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46209426287067625507603901 17328534857650359565351463)
    ·
      refine ⟨25992802286475539348027195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17328534857650359565351463 25992802286475539348027195)
      ·
        refine ⟨38989203429713309022040793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25992802286475539348027195 38989203429713309022040793)
        ·
          refine ⟨29241902572284981766530595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38989203429713309022040793 29241902572284981766530595)
          ·
            refine ⟨43862853858427472649795893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29241902572284981766530595 43862853858427472649795893)
            ·
              refine ⟨4112142549227575560918365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43862853858427472649795893 4112142549227575560918365)
              ·
                refine ⟨1542053455960340835344387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4112142549227575560918365 1542053455960340835344387)
                ·
                  refine ⟨2313080183940511253016581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542053455960340835344387 2313080183940511253016581)
                  ·
                    refine ⟨433702534488845859940609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2313080183940511253016581 433702534488845859940609)
                    ·
                      rfl

theorem cell22_1266949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_1266949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266949 prefixEnd_1266949 := by exact prefixLift 1266949
  have htrace : WordTrace (prefixWord ++ tailWord_1266949) baseStart_1266949 baseEnd_1266949 := by
    simpa [prefixWord, tailWord_1266949, baseEnd_1266949] using wordTrace_append hprefix tailTrace_1266949
  have hstable : (prefixWord ++ tailWord_1266949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266949).length < 2 ^ (prefixWord ++ tailWord_1266949).sum := by decide
  have hdescent : baseEnd_1266949 < baseStart_1266949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266979 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 1, 5]
def baseStart_1266979 : Nat := 118140960795 + 1266979 * 2 ^ 59
def prefixEnd_1266979 : Nat := 4983230072969 + 3 ^ 40 * 1266979 * 2
def baseEnd_1266979 : Nat := 433712804101935781690517

theorem tailTrace_1266979 : CollatzResearch.WordTrace tailWord_1266979 prefixEnd_1266979 433712804101935781690517 := by
  unfold tailWord_1266979
  simp only [CollatzResearch.WordTrace]
  refine ⟨46210520476958940631195991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30807013651305960420797327 46210520476958940631195991)
  ·
    refine ⟨69315780715438410946793987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46210520476958940631195991 69315780715438410946793987)
    ·
      refine ⟨103973671073157616420190981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69315780715438410946793987 103973671073157616420190981)
      ·
        refine ⟨19495063326217053078785809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103973671073157616420190981 19495063326217053078785809)
        ·
          refine ⟨14621297494662789809089357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19495063326217053078785809 14621297494662789809089357)
          ·
            refine ⟨5482986560498546178408509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14621297494662789809089357 5482986560498546178408509)
            ·
              refine ⟨2056119960186954816903191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5482986560498546178408509 2056119960186954816903191)
              ·
                refine ⟨3084179940280432225354787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056119960186954816903191 3084179940280432225354787)
                ·
                  refine ⟨4626269910420648338032181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084179940280432225354787 4626269910420648338032181)
                  ·
                    refine ⟨433712804101935781690517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4626269910420648338032181 433712804101935781690517)
                    ·
                      rfl

theorem cell22_1266979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5].length) (baseStart_1266979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266979 prefixEnd_1266979 := by exact prefixLift 1266979
  have htrace : WordTrace (prefixWord ++ tailWord_1266979) baseStart_1266979 baseEnd_1266979 := by
    simpa [prefixWord, tailWord_1266979, baseEnd_1266979] using wordTrace_append hprefix tailTrace_1266979
  have hstable : (prefixWord ++ tailWord_1266979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266979).length < 2 ^ (prefixWord ++ tailWord_1266979).sum := by decide
  have hdescent : baseEnd_1266979 < baseStart_1266979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266992 : List Nat := [2, 1, 1, 1, 2, 2, 5, 8]
def baseStart_1266992 : Nat := 118140960795 + 1266992 * 2 ^ 59
def prefixEnd_1266992 : Nat := 4983230072969 + 3 ^ 40 * 1266992 * 2
def baseEnd_1266992 : Nat := 48190806029734231235053

theorem tailTrace_1266992 : CollatzResearch.WordTrace tailWord_1266992 prefixEnd_1266992 48190806029734231235053 := by
  unfold tailWord_1266992
  simp only [CollatzResearch.WordTrace]
  refine ⟨23105497312955921925709615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30807329750607895900946153 23105497312955921925709615)
  ·
    refine ⟨34658245969433882888564423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23105497312955921925709615 34658245969433882888564423)
    ·
      refine ⟨51987368954150824332846635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34658245969433882888564423 51987368954150824332846635)
      ·
        refine ⟨77981053431226236499269953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51987368954150824332846635 77981053431226236499269953)
        ·
          refine ⟨58485790073419677374452465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77981053431226236499269953 58485790073419677374452465)
          ·
            refine ⟨43864342555064758030839349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58485790073419677374452465 43864342555064758030839349)
            ·
              refine ⟨4112282114537321065391189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43864342555064758030839349 4112282114537321065391189)
              ·
                refine ⟨48190806029734231235053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4112282114537321065391189 48190806029734231235053)
                ·
                  rfl

theorem cell22_1266992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_1266992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266992 prefixEnd_1266992 := by exact prefixLift 1266992
  have htrace : WordTrace (prefixWord ++ tailWord_1266992) baseStart_1266992 baseEnd_1266992 := by
    simpa [prefixWord, tailWord_1266992, baseEnd_1266992] using wordTrace_append hprefix tailTrace_1266992
  have hstable : (prefixWord ++ tailWord_1266992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266992).length < 2 ^ (prefixWord ++ tailWord_1266992).sum := by decide
  have hdescent : baseEnd_1266992 < baseStart_1266992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266994 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1266994 : Nat := 118140960795 + 1266994 * 2 ^ 59
def prefixEnd_1266994 : Nat := 4983230072969 + 3 ^ 40 * 1266994 * 2
def baseEnd_1266994 : Nat := 433717938908480742565471

theorem tailTrace_1266994 : CollatzResearch.WordTrace tailWord_1266994 prefixEnd_1266994 433717938908480742565471 := by
  unfold tailWord_1266994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11552766892976149548248009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30807378381269732128661357 11552766892976149548248009)
  ·
    refine ⟨8664575169732112161186007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11552766892976149548248009 8664575169732112161186007)
    ·
      refine ⟨12996862754598168241779011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8664575169732112161186007 12996862754598168241779011)
      ·
        refine ⟨19495294131897252362668517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12996862754598168241779011 19495294131897252362668517)
        ·
          refine ⟨3655367649730734818000347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19495294131897252362668517 3655367649730734818000347)
          ·
            refine ⟨5483051474596102227000521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655367649730734818000347 5483051474596102227000521)
            ·
              refine ⟨4112288605947076670250391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483051474596102227000521 4112288605947076670250391)
              ·
                refine ⟨6168432908920615005375587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112288605947076670250391 6168432908920615005375587)
                ·
                  refine ⟨9252649363380922508063381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6168432908920615005375587 9252649363380922508063381)
                  ·
                    refine ⟨433717938908480742565471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9252649363380922508063381 433717938908480742565471)
                    ·
                      rfl

theorem cell22_1266994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1266994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266994 prefixEnd_1266994 := by exact prefixLift 1266994
  have htrace : WordTrace (prefixWord ++ tailWord_1266994) baseStart_1266994 baseEnd_1266994 := by
    simpa [prefixWord, tailWord_1266994, baseEnd_1266994] using wordTrace_append hprefix tailTrace_1266994
  have hstable : (prefixWord ++ tailWord_1266994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266994).length < 2 ^ (prefixWord ++ tailWord_1266994).sum := by decide
  have hdescent : baseEnd_1266994 < baseStart_1266994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266996 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1266996 : Nat := 118140960795 + 1266996 * 2 ^ 59
def prefixEnd_1266996 : Nat := 4983230072969 + 3 ^ 40 * 1266996 * 2
def baseEnd_1266996 : Nat := 433718623549353404015465

theorem tailTrace_1266996 : CollatzResearch.WordTrace tailWord_1266996 prefixEnd_1266996 433718623549353404015465 := by
  unfold tailWord_1266996
  simp only [CollatzResearch.WordTrace]
  refine ⟨23105570258948676267282421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30807427011931568356376561 23105570258948676267282421)
  ·
    refine ⟨2166147211776438400057727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23105570258948676267282421 2166147211776438400057727)
    ·
      refine ⟨3249220817664657600086591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166147211776438400057727 3249220817664657600086591)
      ·
        refine ⟨4873831226496986400129887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249220817664657600086591 4873831226496986400129887)
        ·
          refine ⟨7310746839745479600194831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873831226496986400129887 7310746839745479600194831)
          ·
            refine ⟨10966120259618219400292247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7310746839745479600194831 10966120259618219400292247)
            ·
              refine ⟨16449180389427329100438371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10966120259618219400292247 16449180389427329100438371)
              ·
                refine ⟨24673770584140993650657557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16449180389427329100438371 24673770584140993650657557)
                ·
                  refine ⟨1156582996131609077374573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24673770584140993650657557 1156582996131609077374573)
                  ·
                    refine ⟨433718623549353404015465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156582996131609077374573 433718623549353404015465)
                    ·
                      rfl

theorem cell22_1266996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1266996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1266996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1266996 prefixEnd_1266996 := by exact prefixLift 1266996
  have htrace : WordTrace (prefixWord ++ tailWord_1266996) baseStart_1266996 baseEnd_1266996 := by
    simpa [prefixWord, tailWord_1266996, baseEnd_1266996] using wordTrace_append hprefix tailTrace_1266996
  have hstable : (prefixWord ++ tailWord_1266996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266996).length < 2 ^ (prefixWord ++ tailWord_1266996).sum := by decide
  have hdescent : baseEnd_1266996 < baseStart_1266996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267009 : List Nat := [1, 2, 5, 2, 1, 1, 10]
def baseStart_1267009 : Nat := 118140960795 + 1267009 * 2 ^ 59
def prefixEnd_1267009 : Nat := 4983230072969 + 3 ^ 40 * 1267009 * 2
def baseEnd_1267009 : Nat := 16063817545000951979275

theorem tailTrace_1267009 : CollatzResearch.WordTrace tailWord_1267009 prefixEnd_1267009 16063817545000951979275 := by
  unfold tailWord_1267009
  simp only [CollatzResearch.WordTrace]
  refine ⟨46211614666850255754788081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30807743111233503836525387 46211614666850255754788081)
  ·
    refine ⟨34658711000137691816091061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46211614666850255754788081 34658711000137691816091061)
    ·
      refine ⟨3249254156262908607758537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34658711000137691816091061 3249254156262908607758537)
      ·
        refine ⟨2436940617197181455818903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249254156262908607758537 2436940617197181455818903)
        ·
          refine ⟨3655410925795772183728355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436940617197181455818903 3655410925795772183728355)
          ·
            refine ⟨5483116388693658275592533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655410925795772183728355 5483116388693658275592533)
            ·
              refine ⟨16063817545000951979275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5483116388693658275592533 16063817545000951979275)
              ·
                rfl

theorem cell22_1267009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 10].length) (baseStart_1267009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267009 prefixEnd_1267009 := by exact prefixLift 1267009
  have htrace : WordTrace (prefixWord ++ tailWord_1267009) baseStart_1267009 baseEnd_1267009 := by
    simpa [prefixWord, tailWord_1267009, baseEnd_1267009] using wordTrace_append hprefix tailTrace_1267009
  have hstable : (prefixWord ++ tailWord_1267009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267009).length < 2 ^ (prefixWord ++ tailWord_1267009).sum := by decide
  have hdescent : baseEnd_1267009 < baseStart_1267009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267058 : List Nat := [3, 2, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_1267058 : Nat := 118140960795 + 1267058 * 2 ^ 59
def prefixEnd_1267058 : Nat := 4983230072969 + 3 ^ 40 * 1267058 * 2
def baseEnd_1267058 : Nat := 433739847416405908965275

theorem tailTrace_1267058 : CollatzResearch.WordTrace tailWord_1267058 prefixEnd_1267058 433739847416405908965275 := by
  unfold tailWord_1267058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11553350460918184280830457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30808934562448491415547885 11553350460918184280830457)
  ·
    refine ⟨8665012845688638210622843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11553350460918184280830457 8665012845688638210622843)
    ·
      refine ⟨12997519268532957315934265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8665012845688638210622843 12997519268532957315934265)
      ·
        refine ⟨9748139451399717986950699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12997519268532957315934265 9748139451399717986950699)
        ·
          refine ⟨14622209177099576980426049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9748139451399717986950699 14622209177099576980426049)
          ·
            refine ⟨10966656882824682735319537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14622209177099576980426049 10966656882824682735319537)
            ·
              refine ⟨8224992662118512051489653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10966656882824682735319537 8224992662118512051489653)
              ·
                refine ⟨771093062073610504827155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8224992662118512051489653 771093062073610504827155)
                ·
                  refine ⟨1156639593110415757240733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771093062073610504827155 1156639593110415757240733)
                  ·
                    refine ⟨433739847416405908965275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156639593110415757240733 433739847416405908965275)
                    ·
                      rfl

theorem cell22_1267058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_1267058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267058 prefixEnd_1267058 := by exact prefixLift 1267058
  have htrace : WordTrace (prefixWord ++ tailWord_1267058) baseStart_1267058 baseEnd_1267058 := by
    simpa [prefixWord, tailWord_1267058, baseEnd_1267058] using wordTrace_append hprefix tailTrace_1267058
  have hstable : (prefixWord ++ tailWord_1267058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267058).length < 2 ^ (prefixWord ++ tailWord_1267058).sum := by decide
  have hdescent : baseEnd_1267058 < baseStart_1267058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267069 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_1267069 : Nat := 118140960795 + 1267069 * 2 ^ 59
def prefixEnd_1267069 : Nat := 4983230072969 + 3 ^ 40 * 1267069 * 2
def baseEnd_1267069 : Nat := 433743612941205546940241

theorem tailTrace_1267069 : CollatzResearch.WordTrace tailWord_1267069 prefixEnd_1267069 433743612941205546940241 := by
  unfold tailWord_1267069
  simp only [CollatzResearch.WordTrace]
  refine ⟨46213803046632886001972261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30809202031088590667981507 46213803046632886001972261)
  ·
    refine ⟨8665088071243666125369799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46213803046632886001972261 8665088071243666125369799)
    ·
      refine ⟨12997632106865499188054699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8665088071243666125369799 12997632106865499188054699)
      ·
        refine ⟨19496448160298248782082049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12997632106865499188054699 19496448160298248782082049)
        ·
          refine ⟨14622336120223686586561537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19496448160298248782082049 14622336120223686586561537)
          ·
            refine ⟨10966752090167764939921153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14622336120223686586561537 10966752090167764939921153)
            ·
              refine ⟨8225064067625823704940865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10966752090167764939921153 8225064067625823704940865)
              ·
                refine ⟨6168798050719367778705649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8225064067625823704940865 6168798050719367778705649)
                ·
                  refine ⟨4626598538039525834029237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6168798050719367778705649 4626598538039525834029237)
                  ·
                    refine ⟨433743612941205546940241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4626598538039525834029237 433743612941205546940241)
                    ·
                      rfl

theorem cell22_1267069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_1267069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267069 prefixEnd_1267069 := by exact prefixLift 1267069
  have htrace : WordTrace (prefixWord ++ tailWord_1267069) baseStart_1267069 baseEnd_1267069 := by
    simpa [prefixWord, tailWord_1267069, baseEnd_1267069] using wordTrace_append hprefix tailTrace_1267069
  have hstable : (prefixWord ++ tailWord_1267069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267069).length < 2 ^ (prefixWord ++ tailWord_1267069).sum := by decide
  have hdescent : baseEnd_1267069 < baseStart_1267069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267075 : List Nat := [1, 1, 1, 3, 5, 1, 4, 2, 1, 3]
def baseStart_1267075 : Nat := 118140960795 + 1267075 * 2 ^ 59
def prefixEnd_1267075 : Nat := 4983230072969 + 3 ^ 40 * 1267075 * 2
def baseEnd_1267075 : Nat := 433745666863823531290223

theorem tailTrace_1267075 : CollatzResearch.WordTrace tailWord_1267075 prefixEnd_1267075 433745666863823531290223 := by
  unfold tailWord_1267075
  simp only [CollatzResearch.WordTrace]
  refine ⟨46214021884611149026690679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30809347923074099351127119 46214021884611149026690679)
  ·
    refine ⟨69321032826916723540036019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46214021884611149026690679 69321032826916723540036019)
    ·
      refine ⟨103981549240375085310054029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69321032826916723540036019 103981549240375085310054029)
      ·
        refine ⟨38993080965140656991270261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103981549240375085310054029 38993080965140656991270261)
        ·
          refine ⟨3655601340481936592931587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38993080965140656991270261 3655601340481936592931587)
          ·
            refine ⟨5483402010722904889397381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655601340481936592931587 5483402010722904889397381)
            ·
              refine ⟨1028137877010544666762009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5483402010722904889397381 1028137877010544666762009)
              ·
                refine ⟨771103407757908500071507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1028137877010544666762009 771103407757908500071507)
                ·
                  refine ⟨1156655111636862750107261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771103407757908500071507 1156655111636862750107261)
                  ·
                    refine ⟨433745666863823531290223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156655111636862750107261 433745666863823531290223)
                    ·
                      rfl

theorem cell22_1267075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 3].length) (baseStart_1267075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267075 prefixEnd_1267075 := by exact prefixLift 1267075
  have htrace : WordTrace (prefixWord ++ tailWord_1267075) baseStart_1267075 baseEnd_1267075 := by
    simpa [prefixWord, tailWord_1267075, baseEnd_1267075] using wordTrace_append hprefix tailTrace_1267075
  have hstable : (prefixWord ++ tailWord_1267075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267075).length < 2 ^ (prefixWord ++ tailWord_1267075).sum := by decide
  have hdescent : baseEnd_1267075 < baseStart_1267075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267084 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1267084 : Nat := 118140960795 + 1267084 * 2 ^ 59
def prefixEnd_1267084 : Nat := 4983230072969 + 3 ^ 40 * 1267084 * 2
def baseEnd_1267084 : Nat := 433748747747750507815195

theorem tailTrace_1267084 : CollatzResearch.WordTrace tailWord_1267084 prefixEnd_1267084 433748747747750507815195 := by
  unfold tailWord_1267084
  simp only [CollatzResearch.WordTrace]
  refine ⟨23107175070789271781884153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30809566761052362375845537 23107175070789271781884153)
  ·
    refine ⟨17330381303091953836413115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23107175070789271781884153 17330381303091953836413115)
    ·
      refine ⟨25995571954637930754619673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17330381303091953836413115 25995571954637930754619673)
      ·
        refine ⟨19496678965978448065964755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25995571954637930754619673 19496678965978448065964755)
        ·
          refine ⟨29245018448967672098947133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19496678965978448065964755 29245018448967672098947133)
          ·
            refine ⟨10966881918362877037105175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29245018448967672098947133 10966881918362877037105175)
            ·
              refine ⟨16450322877544315555657763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10966881918362877037105175 16450322877544315555657763)
              ·
                refine ⟨24675484316316473333486645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16450322877544315555657763 24675484316316473333486645)
                ·
                  refine ⟨2313326654654669375014373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24675484316316473333486645 2313326654654669375014373)
                  ·
                    refine ⟨433748747747750507815195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2313326654654669375014373 433748747747750507815195)
                    ·
                      rfl

theorem cell22_1267084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1267084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267084 prefixEnd_1267084 := by exact prefixLift 1267084
  have htrace : WordTrace (prefixWord ++ tailWord_1267084) baseStart_1267084 baseEnd_1267084 := by
    simpa [prefixWord, tailWord_1267084, baseEnd_1267084] using wordTrace_append hprefix tailTrace_1267084
  have hstable : (prefixWord ++ tailWord_1267084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267084).length < 2 ^ (prefixWord ++ tailWord_1267084).sum := by decide
  have hdescent : baseEnd_1267084 < baseStart_1267084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267101 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1267101 : Nat := 118140960795 + 1267101 * 2 ^ 59
def prefixEnd_1267101 : Nat := 4983230072969 + 3 ^ 40 * 1267101 * 2
def baseEnd_1267101 : Nat := 433754567195168130140143

theorem tailTrace_1267101 : CollatzResearch.WordTrace tailWord_1267101 prefixEnd_1267101 433754567195168130140143 := by
  unfold tailWord_1267101
  simp only [CollatzResearch.WordTrace]
  refine ⟨46214970182516955467137157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30809980121677970311424771 46214970182516955467137157)
  ·
    refine ⟨8665306909221929150088217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46214970182516955467137157 8665306909221929150088217)
    ·
      refine ⟨6498980181916446862566163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8665306909221929150088217 6498980181916446862566163)
      ·
        refine ⟨9748470272874670293849245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6498980181916446862566163 9748470272874670293849245)
        ·
          refine ⟨3655676352328001360193467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9748470272874670293849245 3655676352328001360193467)
          ·
            refine ⟨5483514528492002040290201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655676352328001360193467 5483514528492002040290201)
            ·
              refine ⟨4112635896369001530217651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483514528492002040290201 4112635896369001530217651)
              ·
                refine ⟨6168953844553502295326477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112635896369001530217651 6168953844553502295326477)
                ·
                  refine ⟨2313357691707563360747429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6168953844553502295326477 2313357691707563360747429)
                  ·
                    refine ⟨433754567195168130140143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2313357691707563360747429 433754567195168130140143)
                    ·
                      rfl

theorem cell22_1267101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1267101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267101 prefixEnd_1267101 := by exact prefixLift 1267101
  have htrace : WordTrace (prefixWord ++ tailWord_1267101) baseStart_1267101 baseEnd_1267101 := by
    simpa [prefixWord, tailWord_1267101, baseEnd_1267101] using wordTrace_append hprefix tailTrace_1267101
  have hstable : (prefixWord ++ tailWord_1267101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267101).length < 2 ^ (prefixWord ++ tailWord_1267101).sum := by decide
  have hdescent : baseEnd_1267101 < baseStart_1267101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267116 : List Nat := [2, 2, 1, 1, 1, 1, 5, 5, 4]
def baseStart_1267116 : Nat := 118140960795 + 1267116 * 2 ^ 59
def prefixEnd_1267116 : Nat := 4983230072969 + 3 ^ 40 * 1267116 * 2
def baseEnd_1267116 : Nat := 144586567333904363671699

theorem tailTrace_1267116 : CollatzResearch.WordTrace tailWord_1267116 prefixEnd_1267116 144586567333904363671699 := by
  unfold tailWord_1267116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23107758638731306514466601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30810344851641742019288801 23107758638731306514466601)
  ·
    refine ⟨17330818979048479885849951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23107758638731306514466601 17330818979048479885849951)
    ·
      refine ⟨25996228468572719828774927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17330818979048479885849951 25996228468572719828774927)
      ·
        refine ⟨38994342702859079743162391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25996228468572719828774927 38994342702859079743162391)
        ·
          refine ⟨58491514054288619614743587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38994342702859079743162391 58491514054288619614743587)
          ·
            refine ⟨87737271081432929422115381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58491514054288619614743587 87737271081432929422115381)
            ·
              refine ⟨8225369163884337133323317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87737271081432929422115381 8225369163884337133323317)
              ·
                refine ⟨771128359114156606249061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8225369163884337133323317 771128359114156606249061)
                ·
                  refine ⟨144586567333904363671699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771128359114156606249061 144586567333904363671699)
                  ·
                    rfl

theorem cell22_1267116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_1267116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267116 prefixEnd_1267116 := by exact prefixLift 1267116
  have htrace : WordTrace (prefixWord ++ tailWord_1267116) baseStart_1267116 baseEnd_1267116 := by
    simpa [prefixWord, tailWord_1267116, baseEnd_1267116] using wordTrace_append hprefix tailTrace_1267116
  have hstable : (prefixWord ++ tailWord_1267116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267116).length < 2 ^ (prefixWord ++ tailWord_1267116).sum := by decide
  have hdescent : baseEnd_1267116 < baseStart_1267116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267144 : List Nat := [2, 1, 3, 1, 3, 1, 2, 9]
def baseStart_1267144 : Nat := 118140960795 + 1267144 * 2 ^ 59
def prefixEnd_1267144 : Nat := 4983230072969 + 3 ^ 40 * 1267144 * 2
def baseEnd_1267144 : Nat := 48196587441547816812779

theorem tailTrace_1267144 : CollatzResearch.WordTrace tailWord_1267144 prefixEnd_1267144 48196587441547816812779 := by
  unfold tailWord_1267144
  simp only [CollatzResearch.WordTrace]
  refine ⟨23108269260680586905476243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30811025680907449207301657 23108269260680586905476243)
  ·
    refine ⟨34662403891020880358214365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23108269260680586905476243 34662403891020880358214365)
    ·
      refine ⟨12998401459132830134330387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34662403891020880358214365 12998401459132830134330387)
      ·
        refine ⟨19497602188699245201495581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12998401459132830134330387 19497602188699245201495581)
        ·
          refine ⟨7311600820762216950560843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19497602188699245201495581 7311600820762216950560843)
          ·
            refine ⟨10967401231143325425841265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7311600820762216950560843 10967401231143325425841265)
            ·
              refine ⟨8225550923357494069380949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10967401231143325425841265 8225550923357494069380949)
              ·
                refine ⟨48196587441547816812779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8225550923357494069380949 48196587441547816812779)
                ·
                  rfl

theorem cell22_1267144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_1267144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267144 prefixEnd_1267144 := by exact prefixLift 1267144
  have htrace : WordTrace (prefixWord ++ tailWord_1267144) baseStart_1267144 baseEnd_1267144 := by
    simpa [prefixWord, tailWord_1267144, baseEnd_1267144] using wordTrace_append hprefix tailTrace_1267144
  have hstable : (prefixWord ++ tailWord_1267144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267144).length < 2 ^ (prefixWord ++ tailWord_1267144).sum := by decide
  have hdescent : baseEnd_1267144 < baseStart_1267144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267148 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_1267148 : Nat := 118140960795 + 1267148 * 2 ^ 59
def prefixEnd_1267148 : Nat := 4983230072969 + 3 ^ 40 * 1267148 * 2
def baseEnd_1267148 : Nat := 433770656255675674214999

theorem tailTrace_1267148 : CollatzResearch.WordTrace tailWord_1267148 prefixEnd_1267148 433770656255675674214999 := by
  unfold tailWord_1267148
  simp only [CollatzResearch.WordTrace]
  refine ⟨23108342206673341247049049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30811122942231121662732065 23108342206673341247049049)
  ·
    refine ⟨17331256655005005935286787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23108342206673341247049049 17331256655005005935286787)
    ·
      refine ⟨25996884982507508902930181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17331256655005005935286787 25996884982507508902930181)
      ·
        refine ⟨4874415934220157919299409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25996884982507508902930181 4874415934220157919299409)
        ·
          refine ⟨3655811950665118439474557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4874415934220157919299409 3655811950665118439474557)
          ·
            refine ⟨1370929481499419414802959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3655811950665118439474557 1370929481499419414802959)
            ·
              refine ⟨2056394222249129122204439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370929481499419414802959 2056394222249129122204439)
              ·
                refine ⟨3084591333373693683306659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056394222249129122204439 3084591333373693683306659)
                ·
                  refine ⟨4626887000060540524959989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084591333373693683306659 4626887000060540524959989)
                  ·
                    refine ⟨433770656255675674214999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4626887000060540524959989 433770656255675674214999)
                    ·
                      rfl

theorem cell22_1267148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_1267148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267148 prefixEnd_1267148 := by exact prefixLift 1267148
  have htrace : WordTrace (prefixWord ++ tailWord_1267148) baseStart_1267148 baseEnd_1267148 := by
    simpa [prefixWord, tailWord_1267148, baseEnd_1267148] using wordTrace_append hprefix tailTrace_1267148
  have hstable : (prefixWord ++ tailWord_1267148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267148).length < 2 ^ (prefixWord ++ tailWord_1267148).sum := by decide
  have hdescent : baseEnd_1267148 < baseStart_1267148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267161 : List Nat := [1, 2, 1, 2, 4, 2, 4, 6]
def baseStart_1267161 : Nat := 118140960795 + 1267161 * 2 ^ 59
def prefixEnd_1267161 : Nat := 4983230072969 + 3 ^ 40 * 1267161 * 2
def baseEnd_1267161 : Nat := 48197234046816441515551

theorem tailTrace_1267161 : CollatzResearch.WordTrace tailWord_1267161 prefixEnd_1267161 48197234046816441515551 := by
  unfold tailWord_1267161
  simp only [CollatzResearch.WordTrace]
  refine ⟨46217158562299585714321337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30811439041533057142880891 46217158562299585714321337)
  ·
    refine ⟨34662868921724689285741003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46217158562299585714321337 34662868921724689285741003)
    ·
      refine ⟨51994303382587033928611505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34662868921724689285741003 51994303382587033928611505)
      ·
        refine ⟨38995727536940275446458629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51994303382587033928611505 38995727536940275446458629)
        ·
          refine ⟨7311698913176301646210993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38995727536940275446458629 7311698913176301646210993)
          ·
            refine ⟨5483774184882226234658245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7311698913176301646210993 5483774184882226234658245)
            ·
              refine ⟨1028207659665417418998421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5483774184882226234658245 1028207659665417418998421)
              ·
                refine ⟨48197234046816441515551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1028207659665417418998421 48197234046816441515551)
                ·
                  rfl

theorem cell22_1267161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 6].length) (baseStart_1267161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267161 prefixEnd_1267161 := by exact prefixLift 1267161
  have htrace : WordTrace (prefixWord ++ tailWord_1267161) baseStart_1267161 baseEnd_1267161 := by
    simpa [prefixWord, tailWord_1267161, baseEnd_1267161] using wordTrace_append hprefix tailTrace_1267161
  have hstable : (prefixWord ++ tailWord_1267161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267161).length < 2 ^ (prefixWord ++ tailWord_1267161).sum := by decide
  have hdescent : baseEnd_1267161 < baseStart_1267161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267178 : List Nat := [3, 1, 3, 1, 5, 1, 8]
def baseStart_1267178 : Nat := 118140960795 + 1267178 * 2 ^ 59
def prefixEnd_1267178 : Nat := 4983230072969 + 3 ^ 40 * 1267178 * 2
def baseEnd_1267178 : Nat := 16065960217361688739441

theorem tailTrace_1267178 : CollatzResearch.WordTrace tailWord_1267178 prefixEnd_1267178 16065960217361688739441 := by
  unfold tailWord_1267178
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554444650809499404422547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30811852402158665078460125 11554444650809499404422547)
  ·
    refine ⟨17331666976214249106633821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11554444650809499404422547 17331666976214249106633821)
    ·
      refine ⟨6499375116080343414987683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17331666976214249106633821 6499375116080343414987683)
      ·
        refine ⟨9749062674120515122481525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6499375116080343414987683 9749062674120515122481525)
        ·
          refine ⟨913974625698798292732643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9749062674120515122481525 913974625698798292732643)
          ·
            refine ⟨1370961938548197439098965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913974625698798292732643 1370961938548197439098965)
            ·
              refine ⟨16065960217361688739441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1370961938548197439098965 16065960217361688739441)
              ·
                rfl

theorem cell22_1267178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 8].length) (baseStart_1267178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267178 prefixEnd_1267178 := by exact prefixLift 1267178
  have htrace : WordTrace (prefixWord ++ tailWord_1267178) baseStart_1267178 baseEnd_1267178 := by
    simpa [prefixWord, tailWord_1267178, baseEnd_1267178] using wordTrace_append hprefix tailTrace_1267178
  have hstable : (prefixWord ++ tailWord_1267178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267178).length < 2 ^ (prefixWord ++ tailWord_1267178).sum := by decide
  have hdescent : baseEnd_1267178 < baseStart_1267178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267240 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 5]
def baseStart_1267240 : Nat := 118140960795 + 1267240 * 2 ^ 59
def prefixEnd_1267240 : Nat := 4983230072969 + 3 ^ 40 * 1267240 * 2
def baseEnd_1267240 : Nat := 144600716578606033638239

theorem tailTrace_1267240 : CollatzResearch.WordTrace tailWord_1267240 prefixEnd_1267240 144600716578606033638239 := by
  unfold tailWord_1267240
  simp only [CollatzResearch.WordTrace]
  refine ⟨23110019964506691103223587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30813359952675588137631449 23110019964506691103223587)
  ·
    refine ⟨34665029946760036654835381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23110019964506691103223587 34665029946760036654835381)
    ·
      refine ⟨3249846557508753436390817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34665029946760036654835381 3249846557508753436390817)
      ·
        refine ⟨2437384918131565077293113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249846557508753436390817 2437384918131565077293113)
        ·
          refine ⟨1828038688598673807969835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2437384918131565077293113 1828038688598673807969835)
          ·
            refine ⟨2742058032898010711954753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828038688598673807969835 2742058032898010711954753)
            ·
              refine ⟨2056543524673508033966065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742058032898010711954753 2056543524673508033966065)
              ·
                refine ⟨1542407643505131025474549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2056543524673508033966065 1542407643505131025474549)
                ·
                  refine ⟨144600716578606033638239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1542407643505131025474549 144600716578606033638239)
                  ·
                    rfl

theorem cell22_1267240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_1267240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267240 prefixEnd_1267240 := by exact prefixLift 1267240
  have htrace : WordTrace (prefixWord ++ tailWord_1267240) baseStart_1267240 baseEnd_1267240 := by
    simpa [prefixWord, tailWord_1267240, baseEnd_1267240] using wordTrace_append hprefix tailTrace_1267240
  have hstable : (prefixWord ++ tailWord_1267240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267240).length < 2 ^ (prefixWord ++ tailWord_1267240).sum := by decide
  have hdescent : baseEnd_1267240 < baseStart_1267240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267281 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1267281 : Nat := 118140960795 + 1267281 * 2 ^ 59
def prefixEnd_1267281 : Nat := 4983230072969 + 3 ^ 40 * 1267281 * 2
def baseEnd_1267281 : Nat := 433816184873707660639591

theorem tailTrace_1267281 : CollatzResearch.WordTrace tailWord_1267281 prefixEnd_1267281 433816184873707660639591 := by
  unfold tailWord_1267281
  simp only [CollatzResearch.WordTrace]
  refine ⟨46221535321864846208689697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30814356881243230805793131 46221535321864846208689697)
  ·
    refine ⟨34666151491398634656517273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46221535321864846208689697 34666151491398634656517273)
    ·
      refine ⟨25999613618548975992387955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34666151491398634656517273 25999613618548975992387955)
      ·
        refine ⟨38999420427823463988581933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25999613618548975992387955 38999420427823463988581933)
        ·
          refine ⟨14624782660433798995718225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38999420427823463988581933 14624782660433798995718225)
          ·
            refine ⟨10968586995325349246788669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14624782660433798995718225 10968586995325349246788669)
            ·
              refine ⟨4113220123247005967545751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10968586995325349246788669 4113220123247005967545751)
              ·
                refine ⟨6169830184870508951318627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113220123247005967545751 6169830184870508951318627)
                ·
                  refine ⟨9254745277305763426977941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169830184870508951318627 9254745277305763426977941)
                  ·
                    refine ⟨433816184873707660639591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9254745277305763426977941 433816184873707660639591)
                    ·
                      rfl

theorem cell22_1267281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1267281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267281 prefixEnd_1267281 := by exact prefixLift 1267281
  have htrace : WordTrace (prefixWord ++ tailWord_1267281) baseStart_1267281 baseEnd_1267281 := by
    simpa [prefixWord, tailWord_1267281, baseEnd_1267281] using wordTrace_append hprefix tailTrace_1267281
  have hstable : (prefixWord ++ tailWord_1267281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267281).length < 2 ^ (prefixWord ++ tailWord_1267281).sum := by decide
  have hdescent : baseEnd_1267281 < baseStart_1267281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267300 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_1267300 : Nat := 118140960795 + 1267300 * 2 ^ 59
def prefixEnd_1267300 : Nat := 4983230072969 + 3 ^ 40 * 1267300 * 2
def baseEnd_1267300 : Nat := 433822688961997944414533

theorem tailTrace_1267300 : CollatzResearch.WordTrace tailWord_1267300 prefixEnd_1267300 433822688961997944414533 := by
  unfold tailWord_1267300
  simp only [CollatzResearch.WordTrace]
  refine ⟨23111114154398006226815677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30814818872530674969087569 23111114154398006226815677)
  ·
    refine ⟨8666667807899252335055879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23111114154398006226815677 8666667807899252335055879)
    ·
      refine ⟨13000001711848878502583819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8666667807899252335055879 13000001711848878502583819)
      ·
        refine ⟨19500002567773317753875729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13000001711848878502583819 19500002567773317753875729)
        ·
          refine ⟨14625001925829988315406797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19500002567773317753875729 14625001925829988315406797)
          ·
            refine ⟨5484375722186245618277549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14625001925829988315406797 5484375722186245618277549)
            ·
              refine ⟨2056640895819842106854081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5484375722186245618277549 2056640895819842106854081)
              ·
                refine ⟨1542480671864881580140561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2056640895819842106854081 1542480671864881580140561)
                ·
                  refine ⟨1156860503898661185105421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542480671864881580140561 1156860503898661185105421)
                  ·
                    refine ⟨433822688961997944414533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156860503898661185105421 433822688961997944414533)
                    ·
                      rfl

theorem cell22_1267300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_1267300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267300 prefixEnd_1267300 := by exact prefixLift 1267300
  have htrace : WordTrace (prefixWord ++ tailWord_1267300) baseStart_1267300 baseEnd_1267300 := by
    simpa [prefixWord, tailWord_1267300, baseEnd_1267300] using wordTrace_append hprefix tailTrace_1267300
  have hstable : (prefixWord ++ tailWord_1267300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267300).length < 2 ^ (prefixWord ++ tailWord_1267300).sum := by decide
  have hdescent : baseEnd_1267300 < baseStart_1267300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267328 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 3, 3]
def baseStart_1267328 : Nat := 118140960795 + 1267328 * 2 ^ 59
def prefixEnd_1267328 : Nat := 4983230072969 + 3 ^ 40 * 1267328 * 2
def baseEnd_1267328 : Nat := 433832273934215204714447

theorem tailTrace_1267328 : CollatzResearch.WordTrace tailWord_1267328 prefixEnd_1267328 433832273934215204714447 := by
  unfold tailWord_1267328
  simp only [CollatzResearch.WordTrace]
  refine ⟨23111624776347286617825319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30815499701796382157100425 23111624776347286617825319)
  ·
    refine ⟨34667437164520929926737979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23111624776347286617825319 34667437164520929926737979)
    ·
      refine ⟨52001155746781394890106969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34667437164520929926737979 52001155746781394890106969)
      ·
        refine ⟨39000866810086046167580227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52001155746781394890106969 39000866810086046167580227)
        ·
          refine ⟨58501300215129069251370341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39000866810086046167580227 58501300215129069251370341)
          ·
            refine ⟨10968993790336700484631939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58501300215129069251370341 10968993790336700484631939)
            ·
              refine ⟨16453490685505050726947909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10968993790336700484631939 16453490685505050726947909)
              ·
                refine ⟨3085029503532197011302733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16453490685505050726947909 3085029503532197011302733)
                ·
                  refine ⟨1156886063824573879238525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3085029503532197011302733 1156886063824573879238525)
                  ·
                    refine ⟨433832273934215204714447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156886063824573879238525 433832273934215204714447)
                    ·
                      rfl

theorem cell22_1267328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_1267328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267328 prefixEnd_1267328 := by exact prefixLift 1267328
  have htrace : WordTrace (prefixWord ++ tailWord_1267328) baseStart_1267328 baseEnd_1267328 := by
    simpa [prefixWord, tailWord_1267328, baseEnd_1267328] using wordTrace_append hprefix tailTrace_1267328
  have hstable : (prefixWord ++ tailWord_1267328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267328).length < 2 ^ (prefixWord ++ tailWord_1267328).sum := by decide
  have hdescent : baseEnd_1267328 < baseStart_1267328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267345 : List Nat := [1, 2, 2, 1, 1, 1, 1, 9, 1, 3]
def baseStart_1267345 : Nat := 118140960795 + 1267345 * 2 ^ 59
def prefixEnd_1267345 : Nat := 4983230072969 + 3 ^ 40 * 1267345 * 2
def baseEnd_1267345 : Nat := 433838093381632827039395

theorem tailTrace_1267345 : CollatzResearch.WordTrace tailWord_1267345 prefixEnd_1267345 433838093381632827039395 := by
  unfold tailWord_1267345
  simp only [CollatzResearch.WordTrace]
  refine ⟨46223869593632985139019489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30815913062421990092679659 46223869593632985139019489)
  ·
    refine ⟨34667902195224738854264617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46223869593632985139019489 34667902195224738854264617)
    ·
      refine ⟨26000926646418554140698463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34667902195224738854264617 26000926646418554140698463)
      ·
        refine ⟨39001389969627831211047695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26000926646418554140698463 39001389969627831211047695)
        ·
          refine ⟨58502084954441746816571543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39001389969627831211047695 58502084954441746816571543)
          ·
            refine ⟨87753127431662620224857315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58502084954441746816571543 87753127431662620224857315)
            ·
              refine ⟨131629691147493930337285973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87753127431662620224857315 131629691147493930337285973)
              ·
                refine ⟨771267721567347248070035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 131629691147493930337285973 771267721567347248070035)
                ·
                  refine ⟨1156901582351020872105053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771267721567347248070035 1156901582351020872105053)
                  ·
                    refine ⟨433838093381632827039395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156901582351020872105053 433838093381632827039395)
                    ·
                      rfl

theorem cell22_1267345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_1267345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267345 prefixEnd_1267345 := by exact prefixLift 1267345
  have htrace : WordTrace (prefixWord ++ tailWord_1267345) baseStart_1267345 baseEnd_1267345 := by
    simpa [prefixWord, tailWord_1267345, baseEnd_1267345] using wordTrace_append hprefix tailTrace_1267345
  have hstable : (prefixWord ++ tailWord_1267345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267345).length < 2 ^ (prefixWord ++ tailWord_1267345).sum := by decide
  have hdescent : baseEnd_1267345 < baseStart_1267345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267368 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1267368 : Nat := 118140960795 + 1267368 * 2 ^ 59
def prefixEnd_1267368 : Nat := 4983230072969 + 3 ^ 40 * 1267368 * 2
def baseEnd_1267368 : Nat := 433845966751668433714325

theorem tailTrace_1267368 : CollatzResearch.WordTrace tailWord_1267368 prefixEnd_1267368 433845966751668433714325 := by
  unfold tailWord_1267368
  simp only [CollatzResearch.WordTrace]
  refine ⟨23112354236274830033553379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30816472315033106711404505 23112354236274830033553379)
  ·
    refine ⟨34668531354412245050330069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23112354236274830033553379 34668531354412245050330069)
    ·
      refine ⟨812543703619036993367111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34668531354412245050330069 812543703619036993367111)
      ·
        refine ⟨1218815555428555490050667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812543703619036993367111 1218815555428555490050667)
        ·
          refine ⟨1828223333142833235076001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218815555428555490050667 1828223333142833235076001)
          ·
            refine ⟨1371167499857124926307001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828223333142833235076001 1371167499857124926307001)
            ·
              refine ⟨1028375624892843694730251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371167499857124926307001 1028375624892843694730251)
              ·
                refine ⟨1542563437339265542095377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028375624892843694730251 1542563437339265542095377)
                ·
                  refine ⟨1156922578004449156571533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542563437339265542095377 1156922578004449156571533)
                  ·
                    refine ⟨433845966751668433714325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156922578004449156571533 433845966751668433714325)
                    ·
                      rfl

theorem cell22_1267368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1267368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267368 prefixEnd_1267368 := by exact prefixLift 1267368
  have htrace : WordTrace (prefixWord ++ tailWord_1267368) baseStart_1267368 baseEnd_1267368 := by
    simpa [prefixWord, tailWord_1267368, baseEnd_1267368] using wordTrace_append hprefix tailTrace_1267368
  have hstable : (prefixWord ++ tailWord_1267368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267368).length < 2 ^ (prefixWord ++ tailWord_1267368).sum := by decide
  have hdescent : baseEnd_1267368 < baseStart_1267368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267373 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1267373 : Nat := 118140960795 + 1267373 * 2 ^ 59
def prefixEnd_1267373 : Nat := 4983230072969 + 3 ^ 40 * 1267373 * 2
def baseEnd_1267373 : Nat := 433847678353850087339309

theorem tailTrace_1267373 : CollatzResearch.WordTrace tailWord_1267373 prefixEnd_1267373 433847678353850087339309 := by
  unfold tailWord_1267373
  simp only [CollatzResearch.WordTrace]
  refine ⟨46224890837531545921038773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30816593891687697280692515 46224890837531545921038773)
  ·
    refine ⟨4333583516018582430097385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46224890837531545921038773 4333583516018582430097385)
    ·
      refine ⟨3250187637013936822573039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4333583516018582430097385 3250187637013936822573039)
      ·
        refine ⟨4875281455520905233859559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250187637013936822573039 4875281455520905233859559)
        ·
          refine ⟨7312922183281357850789339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4875281455520905233859559 7312922183281357850789339)
          ·
            refine ⟨10969383274922036776184009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312922183281357850789339 10969383274922036776184009)
            ·
              refine ⟨8227037456191527582138007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10969383274922036776184009 8227037456191527582138007)
              ·
                refine ⟨12340556184287291373207011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8227037456191527582138007 12340556184287291373207011)
                ·
                  refine ⟨18510834276430937059810517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12340556184287291373207011 18510834276430937059810517)
                  ·
                    refine ⟨433847678353850087339309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18510834276430937059810517 433847678353850087339309)
                    ·
                      rfl

theorem cell22_1267373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1267373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267373 prefixEnd_1267373 := by exact prefixLift 1267373
  have htrace : WordTrace (prefixWord ++ tailWord_1267373) baseStart_1267373 baseEnd_1267373 := by
    simpa [prefixWord, tailWord_1267373, baseEnd_1267373] using wordTrace_append hprefix tailTrace_1267373
  have hstable : (prefixWord ++ tailWord_1267373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267373).length < 2 ^ (prefixWord ++ tailWord_1267373).sum := by decide
  have hdescent : baseEnd_1267373 < baseStart_1267373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267435 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 2, 3]
def baseStart_1267435 : Nat := 118140960795 + 1267435 * 2 ^ 59
def prefixEnd_1267435 : Nat := 4983230072969 + 3 ^ 40 * 1267435 * 2
def baseEnd_1267435 : Nat := 433868902220902592289119

theorem tailTrace_1267435 : CollatzResearch.WordTrace tailWord_1267435 prefixEnd_1267435 433868902220902592289119 := by
  unfold tailWord_1267435
  simp only [CollatzResearch.WordTrace]
  refine ⟨46227152163306930509795759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30818101442204620339863839 46227152163306930509795759)
  ·
    refine ⟨69340728244960395764693639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46227152163306930509795759 69340728244960395764693639)
    ·
      refine ⟨104011092367440593647040459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69340728244960395764693639 104011092367440593647040459)
      ·
        refine ⟨156016638551160890470560689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104011092367440593647040459 156016638551160890470560689)
        ·
          refine ⟨117012478913370667852920517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156016638551160890470560689 117012478913370667852920517)
          ·
            refine ⟨21939839796257000222422597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117012478913370667852920517 21939839796257000222422597)
            ·
              refine ⟨4113719961798187541704237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21939839796257000222422597 4113719961798187541704237)
              ·
                refine ⟨1542644985674320328139089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4113719961798187541704237 1542644985674320328139089)
                ·
                  refine ⟨1156983739255740246104317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542644985674320328139089 1156983739255740246104317)
                  ·
                    refine ⟨433868902220902592289119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156983739255740246104317 433868902220902592289119)
                    ·
                      rfl

theorem cell22_1267435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 3].length) (baseStart_1267435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267435 prefixEnd_1267435 := by exact prefixLift 1267435
  have htrace : WordTrace (prefixWord ++ tailWord_1267435) baseStart_1267435 baseEnd_1267435 := by
    simpa [prefixWord, tailWord_1267435, baseEnd_1267435] using wordTrace_append hprefix tailTrace_1267435
  have hstable : (prefixWord ++ tailWord_1267435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267435).length < 2 ^ (prefixWord ++ tailWord_1267435).sum := by decide
  have hdescent : baseEnd_1267435 < baseStart_1267435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267454 : List Nat := [4, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1267454 : Nat := 118140960795 + 1267454 * 2 ^ 59
def prefixEnd_1267454 : Nat := 4983230072969 + 3 ^ 40 * 1267454 * 2
def baseEnd_1267454 : Nat := 144625135436397625354687

theorem tailTrace_1267454 : CollatzResearch.WordTrace tailWord_1267454 prefixEnd_1267454 144625135436397625354687 := by
  unfold tailWord_1267454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778480643779762094342177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30818563433492064503158277 5778480643779762094342177)
  ·
    refine ⟨4333860482834821570756633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5778480643779762094342177 4333860482834821570756633)
    ·
      refine ⟨3250395362126116178067475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4333860482834821570756633 3250395362126116178067475)
      ·
        refine ⟨4875593043189174267101213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250395362126116178067475 4875593043189174267101213)
        ·
          refine ⟨1828347391195940350162955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4875593043189174267101213 1828347391195940350162955)
          ·
            refine ⟨2742521086793910525244433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828347391195940350162955 2742521086793910525244433)
            ·
              refine ⟨2056890815095432893933325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742521086793910525244433 2056890815095432893933325)
              ·
                refine ⟨771334055660787335224997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2056890815095432893933325 771334055660787335224997)
                ·
                  refine ⟨144625135436397625354687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771334055660787335224997 144625135436397625354687)
                  ·
                    rfl

theorem cell22_1267454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1267454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267454 prefixEnd_1267454 := by exact prefixLift 1267454
  have htrace : WordTrace (prefixWord ++ tailWord_1267454) baseStart_1267454 baseEnd_1267454 := by
    simpa [prefixWord, tailWord_1267454, baseEnd_1267454] using wordTrace_append hprefix tailTrace_1267454
  have hstable : (prefixWord ++ tailWord_1267454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267454).length < 2 ^ (prefixWord ++ tailWord_1267454).sum := by decide
  have hdescent : baseEnd_1267454 < baseStart_1267454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267480 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 3, 3]
def baseStart_1267480 : Nat := 118140960795 + 1267480 * 2 ^ 59
def prefixEnd_1267480 : Nat := 4983230072969 + 3 ^ 40 * 1267480 * 2
def baseEnd_1267480 : Nat := 433884306640537474913981

theorem tailTrace_1267480 : CollatzResearch.WordTrace tailWord_1267480 prefixEnd_1267480 433884306640537474913981 := by
  unfold tailWord_1267480
  simp only [CollatzResearch.WordTrace]
  refine ⟨23114396724071951597591947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30819195632095935463455929 23114396724071951597591947)
  ·
    refine ⟨34671595086107927396387921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23114396724071951597591947 34671595086107927396387921)
    ·
      refine ⟨26003696314580945547290941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34671595086107927396387921 26003696314580945547290941)
      ·
        refine ⟨9751386117967854580234103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26003696314580945547290941 9751386117967854580234103)
        ·
          refine ⟨14627079176951781870351155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751386117967854580234103 14627079176951781870351155)
          ·
            refine ⟨21940618765427672805526733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14627079176951781870351155 21940618765427672805526733)
            ·
              refine ⟨8227732037035377302072525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21940618765427672805526733 8227732037035377302072525)
              ·
                refine ⟨3085399513888266488277197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8227732037035377302072525 3085399513888266488277197)
                ·
                  refine ⟨1157024817708099933103949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3085399513888266488277197 1157024817708099933103949)
                  ·
                    refine ⟨433884306640537474913981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157024817708099933103949 433884306640537474913981)
                    ·
                      rfl

theorem cell22_1267480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_1267480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267480 prefixEnd_1267480 := by exact prefixLift 1267480
  have htrace : WordTrace (prefixWord ++ tailWord_1267480) baseStart_1267480 baseEnd_1267480 := by
    simpa [prefixWord, tailWord_1267480, baseEnd_1267480] using wordTrace_append hprefix tailTrace_1267480
  have hstable : (prefixWord ++ tailWord_1267480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267480).length < 2 ^ (prefixWord ++ tailWord_1267480).sum := by decide
  have hdescent : baseEnd_1267480 < baseStart_1267480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267486 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1267486 : Nat := 118140960795 + 1267486 * 2 ^ 59
def prefixEnd_1267486 : Nat := 4983230072969 + 3 ^ 40 * 1267486 * 2
def baseEnd_1267486 : Nat := 433886360563155459263963

theorem tailTrace_1267486 : CollatzResearch.WordTrace tailWord_1267486 prefixEnd_1267486 433886360563155459263963 := by
  unfold tailWord_1267486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778626535765270777487789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30819341524081444146601541 5778626535765270777487789)
  ·
    refine ⟨2166984950911976541557921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5778626535765270777487789 2166984950911976541557921)
    ·
      refine ⟨1625238713183982406168441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2166984950911976541557921 1625238713183982406168441)
      ·
        refine ⟨1218929034887986804626331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625238713183982406168441 1218929034887986804626331)
        ·
          refine ⟨1828393552331980206939497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218929034887986804626331 1828393552331980206939497)
          ·
            refine ⟨1371295164248985155204623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828393552331980206939497 1371295164248985155204623)
            ·
              refine ⟨2056942746373477732806935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371295164248985155204623 2056942746373477732806935)
              ·
                refine ⟨3085414119560216599210403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056942746373477732806935 3085414119560216599210403)
                ·
                  refine ⟨4628121179340324898815605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085414119560216599210403 4628121179340324898815605)
                  ·
                    refine ⟨433886360563155459263963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4628121179340324898815605 433886360563155459263963)
                    ·
                      rfl

theorem cell22_1267486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1267486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267486 prefixEnd_1267486 := by exact prefixLift 1267486
  have htrace : WordTrace (prefixWord ++ tailWord_1267486) baseStart_1267486 baseEnd_1267486 := by
    simpa [prefixWord, tailWord_1267486, baseEnd_1267486] using wordTrace_append hprefix tailTrace_1267486
  have hstable : (prefixWord ++ tailWord_1267486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267486).length < 2 ^ (prefixWord ++ tailWord_1267486).sum := by decide
  have hdescent : baseEnd_1267486 < baseStart_1267486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267514 : List Nat := [3, 1, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_1267514 : Nat := 118140960795 + 1267514 * 2 ^ 59
def prefixEnd_1267514 : Nat := 4983230072969 + 3 ^ 40 * 1267514 * 2
def baseEnd_1267514 : Nat := 433895945535372719563877

theorem tailTrace_1267514 : CollatzResearch.WordTrace tailWord_1267514 prefixEnd_1267514 433895945535372719563877 := by
  unfold tailWord_1267514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11557508382505181750480399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30820022353347151334614397 11557508382505181750480399)
  ·
    refine ⟨17336262573757772625720599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11557508382505181750480399 17336262573757772625720599)
    ·
      refine ⟨26004393860636658938580899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17336262573757772625720599 26004393860636658938580899)
      ·
        refine ⟨39006590790954988407871349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26004393860636658938580899 39006590790954988407871349)
        ·
          refine ⟨3656867886652030163237939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39006590790954988407871349 3656867886652030163237939)
          ·
            refine ⟨5485301829978045244856909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656867886652030163237939 5485301829978045244856909)
            ·
              refine ⟨2056988186241766966821341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5485301829978045244856909 2056988186241766966821341)
              ·
                refine ⟨771370569840662612558003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2056988186241766966821341 771370569840662612558003)
                ·
                  refine ⟨1157055854760993918837005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771370569840662612558003 1157055854760993918837005)
                  ·
                    refine ⟨433895945535372719563877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157055854760993918837005 433895945535372719563877)
                    ·
                      rfl

theorem cell22_1267514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_1267514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267514 prefixEnd_1267514 := by exact prefixLift 1267514
  have htrace : WordTrace (prefixWord ++ tailWord_1267514) baseStart_1267514 baseEnd_1267514 := by
    simpa [prefixWord, tailWord_1267514, baseEnd_1267514] using wordTrace_append hprefix tailTrace_1267514
  have hstable : (prefixWord ++ tailWord_1267514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267514).length < 2 ^ (prefixWord ++ tailWord_1267514).sum := by decide
  have hdescent : baseEnd_1267514 < baseStart_1267514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267587 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 2, 3]
def baseStart_1267587 : Nat := 118140960795 + 1267587 * 2 ^ 59
def prefixEnd_1267587 : Nat := 4983230072969 + 3 ^ 40 * 1267587 * 2
def baseEnd_1267587 : Nat := 433920934927224862488653

theorem tailTrace_1267587 : CollatzResearch.WordTrace tailWord_1267587 prefixEnd_1267587 433920934927224862488653 := by
  unfold tailWord_1267587
  simp only [CollatzResearch.WordTrace]
  refine ⟨46232696058756260469329015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30821797372504173646219343 46232696058756260469329015)
  ·
    refine ⟨69349044088134390703993523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46232696058756260469329015 69349044088134390703993523)
    ·
      refine ⟨104023566132201586055990285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69349044088134390703993523 104023566132201586055990285)
      ·
        refine ⟨39008837299575594770996357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104023566132201586055990285 39008837299575594770996357)
        ·
          refine ⟨7314156993670424019561817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39008837299575594770996357 7314156993670424019561817)
          ·
            refine ⟨5485617745252818014671363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314156993670424019561817 5485617745252818014671363)
            ·
              refine ⟨8228426617879227022007045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5485617745252818014671363 8228426617879227022007045)
              ·
                refine ⟨1542829990852355066626321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8228426617879227022007045 1542829990852355066626321)
                ·
                  refine ⟨1157122493139266299969741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542829990852355066626321 1157122493139266299969741)
                  ·
                    refine ⟨433920934927224862488653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157122493139266299969741 433920934927224862488653)
                    ·
                      rfl

theorem cell22_1267587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 3].length) (baseStart_1267587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267587 prefixEnd_1267587 := by exact prefixLift 1267587
  have htrace : WordTrace (prefixWord ++ tailWord_1267587) baseStart_1267587 baseEnd_1267587 := by
    simpa [prefixWord, tailWord_1267587, baseEnd_1267587] using wordTrace_append hprefix tailTrace_1267587
  have hstable : (prefixWord ++ tailWord_1267587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267587).length < 2 ^ (prefixWord ++ tailWord_1267587).sum := by decide
  have hdescent : baseEnd_1267587 < baseStart_1267587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267604 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1267604 : Nat := 118140960795 + 1267604 * 2 ^ 59
def prefixEnd_1267604 : Nat := 4983230072969 + 3 ^ 40 * 1267604 * 2
def baseEnd_1267604 : Nat := 433926754374642484813601

theorem tailTrace_1267604 : CollatzResearch.WordTrace tailWord_1267604 prefixEnd_1267604 433926754374642484813601 := by
  unfold tailWord_1267604
  simp only [CollatzResearch.WordTrace]
  refine ⟨23116658049847336186348933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30822210733129781581798577 23116658049847336186348933)
  ·
    refine ⟨4334373384346375534940425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23116658049847336186348933 4334373384346375534940425)
    ·
      refine ⟨3250780038259781651205319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4334373384346375534940425 3250780038259781651205319)
      ·
        refine ⟨4876170057389672476807979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250780038259781651205319 4876170057389672476807979)
        ·
          refine ⟨7314255086084508715211969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876170057389672476807979 7314255086084508715211969)
          ·
            refine ⟨5485691314563381536408977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314255086084508715211969 5485691314563381536408977)
            ·
              refine ⟨4114268485922536152306733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485691314563381536408977 4114268485922536152306733)
              ·
                refine ⟨1542850682220951057115025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4114268485922536152306733 1542850682220951057115025)
                ·
                  refine ⟨1157138011665713292836269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542850682220951057115025 1157138011665713292836269)
                  ·
                    refine ⟨433926754374642484813601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157138011665713292836269 433926754374642484813601)
                    ·
                      rfl

theorem cell22_1267604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1267604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267604 prefixEnd_1267604 := by exact prefixLift 1267604
  have htrace : WordTrace (prefixWord ++ tailWord_1267604) baseStart_1267604 baseEnd_1267604 := by
    simpa [prefixWord, tailWord_1267604, baseEnd_1267604] using wordTrace_append hprefix tailTrace_1267604
  have hstable : (prefixWord ++ tailWord_1267604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267604).length < 2 ^ (prefixWord ++ tailWord_1267604).sum := by decide
  have hdescent : baseEnd_1267604 < baseStart_1267604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267606 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1267606 : Nat := 118140960795 + 1267606 * 2 ^ 59
def prefixEnd_1267606 : Nat := 4983230072969 + 3 ^ 40 * 1267606 * 2
def baseEnd_1267606 : Nat := 144642479671838382087865

theorem tailTrace_1267606 : CollatzResearch.WordTrace tailWord_1267606 prefixEnd_1267606 144642479671838382087865 := by
  unfold tailWord_1267606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889586815355464169641917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30822259363791617809513781 2889586815355464169641917)
  ·
    refine ⟨1083595055758299063615719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2889586815355464169641917 1083595055758299063615719)
    ·
      refine ⟨1625392583637448595423579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083595055758299063615719 1625392583637448595423579)
      ·
        refine ⟨2438088875456172893135369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625392583637448595423579 2438088875456172893135369)
        ·
          refine ⟨1828566656592129669851527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2438088875456172893135369 1828566656592129669851527)
          ·
            refine ⟨2742849984888194504777291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828566656592129669851527 2742849984888194504777291)
            ·
              refine ⟨4114274977332291757165937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742849984888194504777291 4114274977332291757165937)
              ·
                refine ⟨3085706232999218817874453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114274977332291757165937 3085706232999218817874453)
                ·
                  refine ⟨144642479671838382087865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3085706232999218817874453 144642479671838382087865)
                  ·
                    rfl

theorem cell22_1267606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1267606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267606 prefixEnd_1267606 := by exact prefixLift 1267606
  have htrace : WordTrace (prefixWord ++ tailWord_1267606) baseStart_1267606 baseEnd_1267606 := by
    simpa [prefixWord, tailWord_1267606, baseEnd_1267606] using wordTrace_append hprefix tailTrace_1267606
  have hstable : (prefixWord ++ tailWord_1267606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267606).length < 2 ^ (prefixWord ++ tailWord_1267606).sum := by decide
  have hdescent : baseEnd_1267606 < baseStart_1267606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267707 : List Nat := [1, 1, 1, 1, 1, 3, 4, 6, 4]
def baseStart_1267707 : Nat := 118140960795 + 1267707 * 2 ^ 59
def prefixEnd_1267707 : Nat := 4983230072969 + 3 ^ 40 * 1267707 * 2
def baseEnd_1267707 : Nat := 144654004459861516496095

theorem tailTrace_1267707 : CollatzResearch.WordTrace tailWord_1267707 prefixEnd_1267707 144654004459861516496095 := by
  unfold tailWord_1267707
  simp only [CollatzResearch.WordTrace]
  refine ⟨46237072818321520963697375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30824715212214347309131583 46237072818321520963697375)
  ·
    refine ⟨69355609227482281445546063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46237072818321520963697375 69355609227482281445546063)
    ·
      refine ⟨104033413841223422168319095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69355609227482281445546063 104033413841223422168319095)
      ·
        refine ⟨156050120761835133252478643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104033413841223422168319095 156050120761835133252478643)
        ·
          refine ⟨234075181142752699878717965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156050120761835133252478643 234075181142752699878717965)
          ·
            refine ⟨87778192928532262454519237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234075181142752699878717965 87778192928532262454519237)
            ·
              refine ⟨16458411174099799210222357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87778192928532262454519237 16458411174099799210222357)
              ·
                refine ⟨771488023785928087979173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16458411174099799210222357 771488023785928087979173)
                ·
                  refine ⟨144654004459861516496095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771488023785928087979173 144654004459861516496095)
                  ·
                    rfl

theorem cell22_1267707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 4].length) (baseStart_1267707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267707 prefixEnd_1267707 := by exact prefixLift 1267707
  have htrace : WordTrace (prefixWord ++ tailWord_1267707) baseStart_1267707 baseEnd_1267707 := by
    simpa [prefixWord, tailWord_1267707, baseEnd_1267707] using wordTrace_append hprefix tailTrace_1267707
  have hstable : (prefixWord ++ tailWord_1267707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267707).length < 2 ^ (prefixWord ++ tailWord_1267707).sum := by decide
  have hdescent : baseEnd_1267707 < baseStart_1267707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267752 : List Nat := [2, 1, 5, 3, 11]
def baseStart_1267752 : Nat := 118140960795 + 1267752 * 2 ^ 59
def prefixEnd_1267752 : Nat := 4983230072969 + 3 ^ 40 * 1267752 * 2
def baseEnd_1267752 : Nat := 1785915299585265152729

theorem tailTrace_1267752 : CollatzResearch.WordTrace tailWord_1267752 prefixEnd_1267752 1785915299585265152729 := by
  unfold tailWord_1267752
  simp only [CollatzResearch.WordTrace]
  refine ⟨23119357051579246824542755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30825809402105662432723673 23119357051579246824542755)
  ·
    refine ⟨34679035577368870236814133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23119357051579246824542755 34679035577368870236814133)
    ·
      refine ⟨3251159585378331584701325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34679035577368870236814133 3251159585378331584701325)
      ·
        refine ⟨1219184844516874344262997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3251159585378331584701325 1219184844516874344262997)
        ·
          refine ⟨1785915299585265152729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1219184844516874344262997 1785915299585265152729)
          ·
            rfl

theorem cell22_1267752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 11].length) (baseStart_1267752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267752 prefixEnd_1267752 := by exact prefixLift 1267752
  have htrace : WordTrace (prefixWord ++ tailWord_1267752) baseStart_1267752 baseEnd_1267752 := by
    simpa [prefixWord, tailWord_1267752, baseEnd_1267752] using wordTrace_append hprefix tailTrace_1267752
  have hstable : (prefixWord ++ tailWord_1267752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267752).length < 2 ^ (prefixWord ++ tailWord_1267752).sum := by decide
  have hdescent : baseEnd_1267752 < baseStart_1267752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267754 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1267754 : Nat := 118140960795 + 1267754 * 2 ^ 59
def prefixEnd_1267754 : Nat := 4983230072969 + 3 ^ 40 * 1267754 * 2
def baseEnd_1267754 : Nat := 433978102440092093563141

theorem tailTrace_1267754 : CollatzResearch.WordTrace tailWord_1267754 prefixEnd_1267754 433978102440092093563141 := by
  unfold tailWord_1267754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11559696762287811997664579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30825858032767498660438877 11559696762287811997664579)
  ·
    refine ⟨17339545143431717996496869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11559696762287811997664579 17339545143431717996496869)
    ·
      refine ⟨3251164714393447124343163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17339545143431717996496869 3251164714393447124343163)
      ·
        refine ⟨4876747071590170686514745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251164714393447124343163 4876747071590170686514745)
        ·
          refine ⟨3657560303692628014886059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4876747071590170686514745 3657560303692628014886059)
          ·
            refine ⟨5486340455538942022329089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657560303692628014886059 5486340455538942022329089)
            ·
              refine ⟨4114755341654206516746817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5486340455538942022329089 4114755341654206516746817)
              ·
                refine ⟨3086066506240654887560113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114755341654206516746817 3086066506240654887560113)
                ·
                  refine ⟨2314549879680491165670085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3086066506240654887560113 2314549879680491165670085)
                  ·
                    refine ⟨433978102440092093563141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2314549879680491165670085 433978102440092093563141)
                    ·
                      rfl

theorem cell22_1267754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1267754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267754 prefixEnd_1267754 := by exact prefixLift 1267754
  have htrace : WordTrace (prefixWord ++ tailWord_1267754) baseStart_1267754 baseEnd_1267754 := by
    simpa [prefixWord, tailWord_1267754, baseEnd_1267754] using wordTrace_append hprefix tailTrace_1267754
  have hstable : (prefixWord ++ tailWord_1267754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267754).length < 2 ^ (prefixWord ++ tailWord_1267754).sum := by decide
  have hdescent : baseEnd_1267754 < baseStart_1267754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267758 : List Nat := [4, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_1267758 : Nat := 118140960795 + 1267758 * 2 ^ 59
def prefixEnd_1267758 : Nat := 4983230072969 + 3 ^ 40 * 1267758 * 2
def baseEnd_1267758 : Nat := 144659823907279138821043

theorem tailTrace_1267758 : CollatzResearch.WordTrace tailWord_1267758 prefixEnd_1267758 144659823907279138821043 := by
  unfold tailWord_1267758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779866617642094584225491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30825955294091171115869285 5779866617642094584225491)
  ·
    refine ⟨8669799926463141876338237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5779866617642094584225491 8669799926463141876338237)
    ·
      refine ⟨3251174972423678203626839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8669799926463141876338237 3251174972423678203626839)
      ·
        refine ⟨4876762458635517305440259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251174972423678203626839 4876762458635517305440259)
        ·
          refine ⟨7315143687953275958160389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876762458635517305440259 7315143687953275958160389)
          ·
            refine ⟨1371589441491239242155073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7315143687953275958160389 1371589441491239242155073)
            ·
              refine ⟨1028692081118429431616305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371589441491239242155073 1028692081118429431616305)
              ·
                refine ⟨771519060838822073712229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1028692081118429431616305 771519060838822073712229)
                ·
                  refine ⟨144659823907279138821043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771519060838822073712229 144659823907279138821043)
                  ·
                    rfl

theorem cell22_1267758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_1267758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267758 prefixEnd_1267758 := by exact prefixLift 1267758
  have htrace : WordTrace (prefixWord ++ tailWord_1267758) baseStart_1267758 baseEnd_1267758 := by
    simpa [prefixWord, tailWord_1267758, baseEnd_1267758] using wordTrace_append hprefix tailTrace_1267758
  have hstable : (prefixWord ++ tailWord_1267758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267758).length < 2 ^ (prefixWord ++ tailWord_1267758).sum := by decide
  have hdescent : baseEnd_1267758 < baseStart_1267758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267769 : List Nat := [1, 2, 1, 5, 3, 2, 1, 7]
def baseStart_1267769 : Nat := 118140960795 + 1267769 * 2 ^ 59
def prefixEnd_1267769 : Nat := 4983230072969 + 3 ^ 40 * 1267769 * 2
def baseEnd_1267769 : Nat := 48220359694070783826455

theorem tailTrace_1267769 : CollatzResearch.WordTrace tailWord_1267769 prefixEnd_1267769 48220359694070783826455 := by
  unfold tailWord_1267769
  simp only [CollatzResearch.WordTrace]
  refine ⟨46239334144096905552454361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30826222762731270368302907 46239334144096905552454361)
  ·
    refine ⟨34679500608072679164340771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46239334144096905552454361 34679500608072679164340771)
    ·
      refine ⟨52019250912109018746511157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34679500608072679164340771 52019250912109018746511157)
      ·
        refine ⟨4876804773010220507485421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52019250912109018746511157 4876804773010220507485421)
        ·
          refine ⟨1828801789878832690307033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4876804773010220507485421 1828801789878832690307033)
          ·
            refine ⟨1371601342409124517730275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828801789878832690307033 1371601342409124517730275)
            ·
              refine ⟨2057402013613686776595413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371601342409124517730275 2057402013613686776595413)
              ·
                refine ⟨48220359694070783826455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2057402013613686776595413 48220359694070783826455)
                ·
                  rfl

theorem cell22_1267769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 7].length) (baseStart_1267769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267769 prefixEnd_1267769 := by exact prefixLift 1267769
  have htrace : WordTrace (prefixWord ++ tailWord_1267769) baseStart_1267769 baseEnd_1267769 := by
    simpa [prefixWord, tailWord_1267769, baseEnd_1267769] using wordTrace_append hprefix tailTrace_1267769
  have hstable : (prefixWord ++ tailWord_1267769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267769).length < 2 ^ (prefixWord ++ tailWord_1267769).sum := by decide
  have hdescent : baseEnd_1267769 < baseStart_1267769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267801 : List Nat := [1, 2, 1, 2, 2, 1, 6, 3, 1, 3]
def baseStart_1267801 : Nat := 118140960795 + 1267801 * 2 ^ 59
def prefixEnd_1267801 : Nat := 4983230072969 + 3 ^ 40 * 1267801 * 2
def baseEnd_1267801 : Nat := 433994191500599637637997

theorem tailTrace_1267801 : CollatzResearch.WordTrace tailWord_1267801 prefixEnd_1267801 433994191500599637637997 := by
  unfold tailWord_1267801
  simp only [CollatzResearch.WordTrace]
  refine ⟨46240501279980975017619257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30827000853320650011746171 46240501279980975017619257)
  ·
    refine ⟨34680375959985731263214443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46240501279980975017619257 34680375959985731263214443)
    ·
      refine ⟨52020563939978596894821665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34680375959985731263214443 52020563939978596894821665)
      ·
        refine ⟨39015422954983947671116249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52020563939978596894821665 39015422954983947671116249)
        ·
          refine ⟨29261567216237960753337187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39015422954983947671116249 29261567216237960753337187)
          ·
            refine ⟨43892350824356941130005781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29261567216237960753337187 43892350824356941130005781)
            ·
              refine ⟨2057453944891731615469021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43892350824356941130005781 2057453944891731615469021)
              ·
                refine ⟨771545229334399355800883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2057453944891731615469021 771545229334399355800883)
                ·
                  refine ⟨1157317844001599033701325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771545229334399355800883 1157317844001599033701325)
                  ·
                    refine ⟨433994191500599637637997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157317844001599033701325 433994191500599637637997)
                    ·
                      rfl

theorem cell22_1267801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 3].length) (baseStart_1267801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267801 prefixEnd_1267801 := by exact prefixLift 1267801
  have htrace : WordTrace (prefixWord ++ tailWord_1267801) baseStart_1267801 baseEnd_1267801 := by
    simpa [prefixWord, tailWord_1267801, baseEnd_1267801] using wordTrace_append hprefix tailTrace_1267801
  have hstable : (prefixWord ++ tailWord_1267801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267801).length < 2 ^ (prefixWord ++ tailWord_1267801).sum := by decide
  have hdescent : baseEnd_1267801 < baseStart_1267801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267812 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1267812 : Nat := 118140960795 + 1267812 * 2 ^ 59
def prefixEnd_1267812 : Nat := 4983230072969 + 3 ^ 40 * 1267812 * 2
def baseEnd_1267812 : Nat := 433997957025399275612963

theorem tailTrace_1267812 : CollatzResearch.WordTrace tailWord_1267812 prefixEnd_1267812 433997957025399275612963 := by
  unfold tailWord_1267812
  simp only [CollatzResearch.WordTrace]
  refine ⟨23120451241470561948134845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30827268321960749264179793 23120451241470561948134845)
  ·
    refine ⟨8670169215551460730550567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23120451241470561948134845 8670169215551460730550567)
    ·
      refine ⟨13005253823327191095825851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8670169215551460730550567 13005253823327191095825851)
      ·
        refine ⟨19507880734990786643738777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13005253823327191095825851 19507880734990786643738777)
        ·
          refine ⟨14630910551243089982804083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19507880734990786643738777 14630910551243089982804083)
          ·
            refine ⟨21946365826864634974206125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14630910551243089982804083 21946365826864634974206125)
            ·
              refine ⟨8229887185074238115327297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21946365826864634974206125 8229887185074238115327297)
              ·
                refine ⟨6172415388805678586495473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8229887185074238115327297 6172415388805678586495473)
                ·
                  refine ⟨4629311541604258939871605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6172415388805678586495473 4629311541604258939871605)
                  ·
                    refine ⟨433997957025399275612963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4629311541604258939871605 433997957025399275612963)
                    ·
                      rfl

theorem cell22_1267812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1267812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267812 prefixEnd_1267812 := by exact prefixLift 1267812
  have htrace : WordTrace (prefixWord ++ tailWord_1267812) baseStart_1267812 baseEnd_1267812 := by
    simpa [prefixWord, tailWord_1267812, baseEnd_1267812] using wordTrace_append hprefix tailTrace_1267812
  have hstable : (prefixWord ++ tailWord_1267812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267812).length < 2 ^ (prefixWord ++ tailWord_1267812).sum := by decide
  have hdescent : baseEnd_1267812 < baseStart_1267812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267876 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1267876 : Nat := 118140960795 + 1267876 * 2 ^ 59
def prefixEnd_1267876 : Nat := 4983230072969 + 3 ^ 40 * 1267876 * 2
def baseEnd_1267876 : Nat := 144673288511108147337589

theorem tailTrace_1267876 : CollatzResearch.WordTrace tailWord_1267876 prefixEnd_1267876 144673288511108147337589 := by
  unfold tailWord_1267876
  simp only [CollatzResearch.WordTrace]
  refine ⟨23121618377354631413299741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30828824503139508551066321 23121618377354631413299741)
  ·
    refine ⟨8670606891507986779987403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23121618377354631413299741 8670606891507986779987403)
    ·
      refine ⟨13005910337261980169981105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8670606891507986779987403 13005910337261980169981105)
      ·
        refine ⟨9754432752946485127485829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13005910337261980169981105 9754432752946485127485829)
        ·
          refine ⟨1828956141177465961403593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9754432752946485127485829 1828956141177465961403593)
          ·
            refine ⟨1371717105883099471052695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828956141177465961403593 1371717105883099471052695)
            ·
              refine ⟨2057575658824649206579043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371717105883099471052695 2057575658824649206579043)
              ·
                refine ⟨3086363488236973809868565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057575658824649206579043 3086363488236973809868565)
                ·
                  refine ⟨144673288511108147337589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3086363488236973809868565 144673288511108147337589)
                  ·
                    rfl

theorem cell22_1267876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1267876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267876 prefixEnd_1267876 := by exact prefixLift 1267876
  have htrace : WordTrace (prefixWord ++ tailWord_1267876) baseStart_1267876 baseEnd_1267876 := by
    simpa [prefixWord, tailWord_1267876, baseEnd_1267876] using wordTrace_append hprefix tailTrace_1267876
  have hstable : (prefixWord ++ tailWord_1267876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267876).length < 2 ^ (prefixWord ++ tailWord_1267876).sum := by decide
  have hdescent : baseEnd_1267876 < baseStart_1267876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267970 : List Nat := [3, 4, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1267970 : Nat := 118140960795 + 1267970 * 2 ^ 59
def prefixEnd_1267970 : Nat := 4983230072969 + 3 ^ 40 * 1267970 * 2
def baseEnd_1267970 : Nat := 434052043654339530162479

theorem tailTrace_1267970 : CollatzResearch.WordTrace tailWord_1267970 prefixEnd_1267970 434052043654339530162479 := by
  unfold tailWord_1267970
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561666304092179220130341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30831110144245811253680909 11561666304092179220130341)
  ·
    refine ⟨2167812432017283603774439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11561666304092179220130341 2167812432017283603774439)
    ·
      refine ⟨3251718648025925405661659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167812432017283603774439 3251718648025925405661659)
      ·
        refine ⟨4877577972038888108492489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251718648025925405661659 4877577972038888108492489)
        ·
          refine ⟨3658183479029166081369367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4877577972038888108492489 3658183479029166081369367)
          ·
            refine ⟨5487275218543749122054051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658183479029166081369367 5487275218543749122054051)
            ·
              refine ⟨8230912827815623683081077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5487275218543749122054051 8230912827815623683081077)
              ·
                refine ⟨771648077607714720288851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8230912827815623683081077 771648077607714720288851)
                ·
                  refine ⟨1157472116411572080433277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771648077607714720288851 1157472116411572080433277)
                  ·
                    refine ⟨434052043654339530162479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157472116411572080433277 434052043654339530162479)
                    ·
                      rfl

theorem cell22_1267970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1267970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267970 prefixEnd_1267970 := by exact prefixLift 1267970
  have htrace : WordTrace (prefixWord ++ tailWord_1267970) baseStart_1267970 baseEnd_1267970 := by
    simpa [prefixWord, tailWord_1267970, baseEnd_1267970] using wordTrace_append hprefix tailTrace_1267970
  have hstable : (prefixWord ++ tailWord_1267970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267970).length < 2 ^ (prefixWord ++ tailWord_1267970).sum := by decide
  have hdescent : baseEnd_1267970 < baseStart_1267970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267998 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1267998 : Nat := 118140960795 + 1267998 * 2 ^ 59
def prefixEnd_1267998 : Nat := 4983230072969 + 3 ^ 40 * 1267998 * 2
def baseEnd_1267998 : Nat := 434061628626556790462393

theorem tailTrace_1267998 : CollatzResearch.WordTrace tailWord_1267998 prefixEnd_1267998 434061628626556790462393 := by
  unfold tailWord_1267998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780960807533409707817581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30831790973511518441693765 5780960807533409707817581)
  ·
    refine ⟨2167860302825028640431593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5780960807533409707817581 2167860302825028640431593)
    ·
      refine ⟨1625895227118771480323695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2167860302825028640431593 1625895227118771480323695)
      ·
        refine ⟨2438842840678157220485543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625895227118771480323695 2438842840678157220485543)
        ·
          refine ⟨3658264261017235830728315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438842840678157220485543 3658264261017235830728315)
          ·
            refine ⟨5487396391525853746092473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658264261017235830728315 5487396391525853746092473)
            ·
              refine ⟨4115547293644390309569355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5487396391525853746092473 4115547293644390309569355)
              ·
                refine ⟨6173320940466585464354033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115547293644390309569355 6173320940466585464354033)
                ·
                  refine ⟨4629990705349939098265525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6173320940466585464354033 4629990705349939098265525)
                  ·
                    refine ⟨434061628626556790462393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4629990705349939098265525 434061628626556790462393)
                    ·
                      rfl

theorem cell22_1267998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1267998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1267998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1267998 prefixEnd_1267998 := by exact prefixLift 1267998
  have htrace : WordTrace (prefixWord ++ tailWord_1267998) baseStart_1267998 baseEnd_1267998 := by
    simpa [prefixWord, tailWord_1267998, baseEnd_1267998] using wordTrace_append hprefix tailTrace_1267998
  have hstable : (prefixWord ++ tailWord_1267998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267998).length < 2 ^ (prefixWord ++ tailWord_1267998).sum := by decide
  have hdescent : baseEnd_1267998 < baseStart_1267998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268024 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1268024 : Nat := 118140960795 + 1268024 * 2 ^ 59
def prefixEnd_1268024 : Nat := 4983230072969 + 3 ^ 40 * 1268024 * 2
def baseEnd_1268024 : Nat := 434070528957901389312313

theorem tailTrace_1268024 : CollatzResearch.WordTrace tailWord_1268024 prefixEnd_1268024 434070528957901389312313 := by
  unfold tailWord_1268024
  simp only [CollatzResearch.WordTrace]
  refine ⟨23124317379086542051493563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30832423172115389401991417 23124317379086542051493563)
  ·
    refine ⟨34686476068629813077240345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23124317379086542051493563 34686476068629813077240345)
    ·
      refine ⟨26014857051472359807930259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34686476068629813077240345 26014857051472359807930259)
      ·
        refine ⟨39022285577208539711895389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26014857051472359807930259 39022285577208539711895389)
        ·
          refine ⟨14633357091453202391960771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39022285577208539711895389 14633357091453202391960771)
          ·
            refine ⟨21950035637179803587941157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14633357091453202391960771 21950035637179803587941157)
            ·
              refine ⟨4115631681971213172738967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21950035637179803587941157 4115631681971213172738967)
              ·
                refine ⟨6173447522956819759108451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115631681971213172738967 6173447522956819759108451)
                ·
                  refine ⟨9260171284435229638662677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6173447522956819759108451 9260171284435229638662677)
                  ·
                    refine ⟨434070528957901389312313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9260171284435229638662677 434070528957901389312313)
                    ·
                      rfl

theorem cell22_1268024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1268024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268024 prefixEnd_1268024 := by exact prefixLift 1268024
  have htrace : WordTrace (prefixWord ++ tailWord_1268024) baseStart_1268024 baseEnd_1268024 := by
    simpa [prefixWord, tailWord_1268024, baseEnd_1268024] using wordTrace_append hprefix tailTrace_1268024
  have hstable : (prefixWord ++ tailWord_1268024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268024).length < 2 ^ (prefixWord ++ tailWord_1268024).sum := by decide
  have hdescent : baseEnd_1268024 < baseStart_1268024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268026 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_1268026 : Nat := 118140960795 + 1268026 * 2 ^ 59
def prefixEnd_1268026 : Nat := 4983230072969 + 3 ^ 40 * 1268026 * 2
def baseEnd_1268026 : Nat := 434071213598774050762307

theorem tailTrace_1268026 : CollatzResearch.WordTrace tailWord_1268026 prefixEnd_1268026 434071213598774050762307 := by
  unfold tailWord_1268026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562176926041459611139983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30832471802777225629706621 11562176926041459611139983)
  ·
    refine ⟨17343265389062189416709975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11562176926041459611139983 17343265389062189416709975)
    ·
      refine ⟨26014898083593284125064963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17343265389062189416709975 26014898083593284125064963)
      ·
        refine ⟨39022347125389926187597445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26014898083593284125064963 39022347125389926187597445)
        ·
          refine ⟨7316690086010611160174521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39022347125389926187597445 7316690086010611160174521)
          ·
            refine ⟨5487517564507958370130891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7316690086010611160174521 5487517564507958370130891)
            ·
              refine ⟨8231276346761937555196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5487517564507958370130891 8231276346761937555196337)
              ·
                refine ⟨6173457260071453166397253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8231276346761937555196337 6173457260071453166397253)
                ·
                  refine ⟨1157523236263397468699485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6173457260071453166397253 1157523236263397468699485)
                  ·
                    refine ⟨434071213598774050762307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157523236263397468699485 434071213598774050762307)
                    ·
                      rfl

theorem cell22_1268026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_1268026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268026 prefixEnd_1268026 := by exact prefixLift 1268026
  have htrace : WordTrace (prefixWord ++ tailWord_1268026) baseStart_1268026 baseEnd_1268026 := by
    simpa [prefixWord, tailWord_1268026, baseEnd_1268026] using wordTrace_append hprefix tailTrace_1268026
  have hstable : (prefixWord ++ tailWord_1268026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268026).length < 2 ^ (prefixWord ++ tailWord_1268026).sum := by decide
  have hdescent : baseEnd_1268026 < baseStart_1268026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268105 : List Nat := [1, 2, 1, 1, 6, 2, 1, 4, 1, 3]
def baseStart_1268105 : Nat := 118140960795 + 1268105 * 2 ^ 59
def prefixEnd_1268105 : Nat := 4983230072969 + 3 ^ 40 * 1268105 * 2
def baseEnd_1268105 : Nat := 434098256913244178037065

theorem tailTrace_1268105 : CollatzResearch.WordTrace tailWord_1268105 prefixEnd_1268105 434098256913244178037065 := by
  unfold tailWord_1268105
  simp only [CollatzResearch.WordTrace]
  refine ⟨46251589070879634936685769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30834392713919756624457179 46251589070879634936685769)
  ·
    refine ⟨34688691803159726202514327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46251589070879634936685769 34688691803159726202514327)
    ·
      refine ⟨52033037704739589303771491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34688691803159726202514327 52033037704739589303771491)
      ·
        refine ⟨78049556557109383955657237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52033037704739589303771491 78049556557109383955657237)
        ·
          refine ⟨3658572963614502372921433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78049556557109383955657237 3658572963614502372921433)
          ·
            refine ⟨2743929722710876779691075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3658572963614502372921433 2743929722710876779691075)
            ·
              refine ⟨4115894584066315169536613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743929722710876779691075 4115894584066315169536613)
              ·
                refine ⟨771730234512434094288115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4115894584066315169536613 771730234512434094288115)
                ·
                  refine ⟨1157595351768651141432173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771730234512434094288115 1157595351768651141432173)
                  ·
                    refine ⟨434098256913244178037065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157595351768651141432173 434098256913244178037065)
                    ·
                      rfl

theorem cell22_1268105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 3].length) (baseStart_1268105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268105 prefixEnd_1268105 := by exact prefixLift 1268105
  have htrace : WordTrace (prefixWord ++ tailWord_1268105) baseStart_1268105 baseEnd_1268105 := by
    simpa [prefixWord, tailWord_1268105, baseEnd_1268105] using wordTrace_append hprefix tailTrace_1268105
  have hstable : (prefixWord ++ tailWord_1268105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268105).length < 2 ^ (prefixWord ++ tailWord_1268105).sum := by decide
  have hdescent : baseEnd_1268105 < baseStart_1268105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268131 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 3, 4]
def baseStart_1268131 : Nat := 118140960795 + 1268131 * 2 ^ 59
def prefixEnd_1268131 : Nat := 4983230072969 + 3 ^ 40 * 1268131 * 2
def baseEnd_1268131 : Nat := 434107157244588776886985

theorem tailTrace_1268131 : CollatzResearch.WordTrace tailWord_1268131 prefixEnd_1268131 434107157244588776886985 := by
  unfold tailWord_1268131
  simp only [CollatzResearch.WordTrace]
  refine ⟨46252537368785441377132247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30835024912523627584754831 46252537368785441377132247)
  ·
    refine ⟨69378806053178162065698371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46252537368785441377132247 69378806053178162065698371)
    ·
      refine ⟨104068209079767243098547557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69378806053178162065698371 104068209079767243098547557)
      ·
        refine ⟨19512789202456358080977667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104068209079767243098547557 19512789202456358080977667)
        ·
          refine ⟨29269183803684537121466501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19512789202456358080977667 29269183803684537121466501)
          ·
            refine ⟨5487971963190850710274969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29269183803684537121466501 5487971963190850710274969)
            ·
              refine ⟨4115978972393138032706227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5487971963190850710274969 4115978972393138032706227)
              ·
                refine ⟨6173968458589707049059341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115978972393138032706227 6173968458589707049059341)
                ·
                  refine ⟨2315238171971140143397253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6173968458589707049059341 2315238171971140143397253)
                  ·
                    refine ⟨434107157244588776886985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2315238171971140143397253 434107157244588776886985)
                    ·
                      rfl

theorem cell22_1268131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_1268131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268131 prefixEnd_1268131 := by exact prefixLift 1268131
  have htrace : WordTrace (prefixWord ++ tailWord_1268131) baseStart_1268131 baseEnd_1268131 := by
    simpa [prefixWord, tailWord_1268131, baseEnd_1268131] using wordTrace_append hprefix tailTrace_1268131
  have hstable : (prefixWord ++ tailWord_1268131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268131).length < 2 ^ (prefixWord ++ tailWord_1268131).sum := by decide
  have hdescent : baseEnd_1268131 < baseStart_1268131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268144 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_1268144 : Nat := 118140960795 + 1268144 * 2 ^ 59
def prefixEnd_1268144 : Nat := 4983230072969 + 3 ^ 40 * 1268144 * 2
def baseEnd_1268144 : Nat := 434111607410261076311945

theorem tailTrace_1268144 : CollatzResearch.WordTrace tailWord_1268144 prefixEnd_1268144 434111607410261076311945 := by
  unfold tailWord_1268144
  simp only [CollatzResearch.WordTrace]
  refine ⟨23126505758869172298677743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30835341011825563064903657 23126505758869172298677743)
  ·
    refine ⟨34689758638303758448016615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23126505758869172298677743 34689758638303758448016615)
    ·
      refine ⟨52034637957455637672024923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34689758638303758448016615 52034637957455637672024923)
      ·
        refine ⟨78051956936183456508037385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52034637957455637672024923 78051956936183456508037385)
        ·
          refine ⟨58538967702137592381028039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78051956936183456508037385 58538967702137592381028039)
          ·
            refine ⟨87808451553206388571542059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58538967702137592381028039 87808451553206388571542059)
            ·
              refine ⟨131712677329809582857313089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87808451553206388571542059 131712677329809582857313089)
              ·
                refine ⟨98784507997357187142984817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131712677329809582857313089 98784507997357187142984817)
                ·
                  refine ⟨74088380998017890357238613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98784507997357187142984817 74088380998017890357238613)
                  ·
                    refine ⟨434111607410261076311945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74088380998017890357238613 434111607410261076311945)
                    ·
                      rfl

theorem cell22_1268144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_1268144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268144 prefixEnd_1268144 := by exact prefixLift 1268144
  have htrace : WordTrace (prefixWord ++ tailWord_1268144) baseStart_1268144 baseEnd_1268144 := by
    simpa [prefixWord, tailWord_1268144, baseEnd_1268144] using wordTrace_append hprefix tailTrace_1268144
  have hstable : (prefixWord ++ tailWord_1268144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268144).length < 2 ^ (prefixWord ++ tailWord_1268144).sum := by decide
  have hdescent : baseEnd_1268144 < baseStart_1268144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268191 : List Nat := [1, 1, 2, 3, 3, 3, 1, 8]
def baseStart_1268191 : Nat := 118140960795 + 1268191 * 2 ^ 59
def prefixEnd_1268191 : Nat := 4983230072969 + 3 ^ 40 * 1268191 * 2
def baseEnd_1268191 : Nat := 48236410718974291154089

theorem tailTrace_1268191 : CollatzResearch.WordTrace tailWord_1268191 prefixEnd_1268191 48236410718974291154089 := by
  unfold tailWord_1268191
  simp only [CollatzResearch.WordTrace]
  refine ⟨46254725748568071624316427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30836483832378714416210951 46254725748568071624316427)
  ·
    refine ⟨69382088622852107436474641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46254725748568071624316427 69382088622852107436474641)
    ·
      refine ⟨52036566467139080577355981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69382088622852107436474641 52036566467139080577355981)
      ·
        refine ⟨19513712425177155216508493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52036566467139080577355981 19513712425177155216508493)
        ·
          refine ⟨7317642159441433206190685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19513712425177155216508493 7317642159441433206190685)
          ·
            refine ⟨2744115809790537452321507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7317642159441433206190685 2744115809790537452321507)
            ·
              refine ⟨4116173714685806178482261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744115809790537452321507 4116173714685806178482261)
              ·
                refine ⟨48236410718974291154089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4116173714685806178482261 48236410718974291154089)
                ·
                  rfl

theorem cell22_1268191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 8].length) (baseStart_1268191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268191 prefixEnd_1268191 := by exact prefixLift 1268191
  have htrace : WordTrace (prefixWord ++ tailWord_1268191) baseStart_1268191 baseEnd_1268191 := by
    simpa [prefixWord, tailWord_1268191, baseEnd_1268191] using wordTrace_append hprefix tailTrace_1268191
  have hstable : (prefixWord ++ tailWord_1268191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268191).length < 2 ^ (prefixWord ++ tailWord_1268191).sum := by decide
  have hdescent : baseEnd_1268191 < baseStart_1268191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268197 : List Nat := [1, 3, 1, 5, 2, 2, 1, 3, 4]
def baseStart_1268197 : Nat := 118140960795 + 1268197 * 2 ^ 59
def prefixEnd_1268197 : Nat := 4983230072969 + 3 ^ 40 * 1268197 * 2
def baseEnd_1268197 : Nat := 144709916797795534912261

theorem tailTrace_1268197 : CollatzResearch.WordTrace tailWord_1268197 prefixEnd_1268197 144709916797795534912261 := by
  unfold tailWord_1268197
  simp only [CollatzResearch.WordTrace]
  refine ⟨46254944586546334649034845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30836629724364223099356563 46254944586546334649034845)
  ·
    refine ⟨17345604219954875493388067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46254944586546334649034845 17345604219954875493388067)
    ·
      refine ⟨26018406329932313240082101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17345604219954875493388067 26018406329932313240082101)
      ·
        refine ⟨2439225593431154366257697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26018406329932313240082101 2439225593431154366257697)
        ·
          refine ⟨1829419195073365774693273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439225593431154366257697 1829419195073365774693273)
          ·
            refine ⟨1372064396305024331019955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1829419195073365774693273 1372064396305024331019955)
            ·
              refine ⟨2058096594457536496529933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372064396305024331019955 2058096594457536496529933)
              ·
                refine ⟨771786222921576186198725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2058096594457536496529933 771786222921576186198725)
                ·
                  refine ⟨144709916797795534912261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 771786222921576186198725 144709916797795534912261)
                  ·
                    rfl

theorem cell22_1268197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_1268197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268197 prefixEnd_1268197 := by exact prefixLift 1268197
  have htrace : WordTrace (prefixWord ++ tailWord_1268197) baseStart_1268197 baseEnd_1268197 := by
    simpa [prefixWord, tailWord_1268197, baseEnd_1268197] using wordTrace_append hprefix tailTrace_1268197
  have hstable : (prefixWord ++ tailWord_1268197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268197).length < 2 ^ (prefixWord ++ tailWord_1268197).sum := by decide
  have hdescent : baseEnd_1268197 < baseStart_1268197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268210 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1268210 : Nat := 118140960795 + 1268210 * 2 ^ 59
def prefixEnd_1268210 : Nat := 4983230072969 + 3 ^ 40 * 1268210 * 2
def baseEnd_1268210 : Nat := 434134200559058904161743

theorem tailTrace_1268210 : CollatzResearch.WordTrace tailWord_1268210 prefixEnd_1268210 434134200559058904161743 := by
  unfold tailWord_1268210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11563854683874809467314521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30836945823666158579505389 11563854683874809467314521)
  ·
    refine ⟨8672891012906107100485891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11563854683874809467314521 8672891012906107100485891)
    ·
      refine ⟨13009336519359160650728837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8672891012906107100485891 13009336519359160650728837)
      ·
        refine ⟨2439250597379842622011657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13009336519359160650728837 2439250597379842622011657)
        ·
          refine ⟨1829437948034881966508743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439250597379842622011657 1829437948034881966508743)
          ·
            refine ⟨2744156922052322949763115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829437948034881966508743 2744156922052322949763115)
            ·
              refine ⟨4116235383078484424644673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744156922052322949763115 4116235383078484424644673)
              ·
                refine ⟨3087176537308863318483505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116235383078484424644673 3087176537308863318483505)
                ·
                  refine ⟨2315382402981647488862629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087176537308863318483505 2315382402981647488862629)
                  ·
                    refine ⟨434134200559058904161743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2315382402981647488862629 434134200559058904161743)
                    ·
                      rfl

theorem cell22_1268210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1268210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268210 prefixEnd_1268210 := by exact prefixLift 1268210
  have htrace : WordTrace (prefixWord ++ tailWord_1268210) baseStart_1268210 baseEnd_1268210 := by
    simpa [prefixWord, tailWord_1268210, baseEnd_1268210] using wordTrace_append hprefix tailTrace_1268210
  have hstable : (prefixWord ++ tailWord_1268210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268210).length < 2 ^ (prefixWord ++ tailWord_1268210).sum := by decide
  have hdescent : baseEnd_1268210 < baseStart_1268210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268221 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_1268221 : Nat := 118140960795 + 1268221 * 2 ^ 59
def prefixEnd_1268221 : Nat := 4983230072969 + 3 ^ 40 * 1268221 * 2
def baseEnd_1268221 : Nat := 434137966083858542136709

theorem tailTrace_1268221 : CollatzResearch.WordTrace tailWord_1268221 prefixEnd_1268221 434137966083858542136709 := by
  unfold tailWord_1268221
  simp only [CollatzResearch.WordTrace]
  refine ⟨46255819938459386747908517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30837213292306257831939011 46255819938459386747908517)
  ·
    refine ⟨8672966238461135015232847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46255819938459386747908517 8672966238461135015232847)
    ·
      refine ⟨13009449357691702522849271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8672966238461135015232847 13009449357691702522849271)
      ·
        refine ⟨19514174036537553784273907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13009449357691702522849271 19514174036537553784273907)
        ·
          refine ⟨29271261054806330676410861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19514174036537553784273907 29271261054806330676410861)
          ·
            refine ⟨10976722895552374003654073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29271261054806330676410861 10976722895552374003654073)
            ·
              refine ⟨8232542171664280502740555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10976722895552374003654073 8232542171664280502740555)
              ·
                refine ⟨12348813257496420754110833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8232542171664280502740555 12348813257496420754110833)
                ·
                  refine ⟨9261609943122315565583125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12348813257496420754110833 9261609943122315565583125)
                  ·
                    refine ⟨434137966083858542136709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9261609943122315565583125 434137966083858542136709)
                    ·
                      rfl

theorem cell22_1268221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_1268221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268221 prefixEnd_1268221 := by exact prefixLift 1268221
  have htrace : WordTrace (prefixWord ++ tailWord_1268221) baseStart_1268221 baseEnd_1268221 := by
    simpa [prefixWord, tailWord_1268221, baseEnd_1268221] using wordTrace_append hprefix tailTrace_1268221
  have hstable : (prefixWord ++ tailWord_1268221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268221).length < 2 ^ (prefixWord ++ tailWord_1268221).sum := by decide
  have hdescent : baseEnd_1268221 < baseStart_1268221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268298 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_1268298 : Nat := 118140960795 + 1268298 * 2 ^ 59
def prefixEnd_1268298 : Nat := 4983230072969 + 3 ^ 40 * 1268298 * 2
def baseEnd_1268298 : Nat := 144721441585818669320491

theorem tailTrace_1268298 : CollatzResearch.WordTrace tailWord_1268298 prefixEnd_1268298 144721441585818669320491 := by
  unfold tailWord_1268298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11564657089795107224615387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30839085572786952598974365 11564657089795107224615387)
  ·
    refine ⟨17346985634692660836923081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11564657089795107224615387 17346985634692660836923081)
    ·
      refine ⟨13010239226019495627692311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17346985634692660836923081 13010239226019495627692311)
      ·
        refine ⟨19515358839029243441538467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13010239226019495627692311 19515358839029243441538467)
        ·
          refine ⟨29273038258543865162307701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19515358839029243441538467 29273038258543865162307701)
          ·
            refine ⟨2744347336738487358966347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29273038258543865162307701 2744347336738487358966347)
            ·
              refine ⟨4116521005107731038449521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744347336738487358966347 4116521005107731038449521)
              ·
                refine ⟨3087390753830798278837141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116521005107731038449521 3087390753830798278837141)
                ·
                  refine ⟨144721441585818669320491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3087390753830798278837141 144721441585818669320491)
                  ·
                    rfl

theorem cell22_1268298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_1268298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268298 prefixEnd_1268298 := by exact prefixLift 1268298
  have htrace : WordTrace (prefixWord ++ tailWord_1268298) baseStart_1268298 baseEnd_1268298 := by
    simpa [prefixWord, tailWord_1268298, baseEnd_1268298] using wordTrace_append hprefix tailTrace_1268298
  have hstable : (prefixWord ++ tailWord_1268298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268298).length < 2 ^ (prefixWord ++ tailWord_1268298).sum := by decide
  have hdescent : baseEnd_1268298 < baseStart_1268298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268330 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1268330 : Nat := 118140960795 + 1268330 * 2 ^ 59
def prefixEnd_1268330 : Nat := 4983230072969 + 3 ^ 40 * 1268330 * 2
def baseEnd_1268330 : Nat := 434175279011418591161375

theorem tailTrace_1268330 : CollatzResearch.WordTrace tailWord_1268330 prefixEnd_1268330 434175279011418591161375 := by
  unfold tailWord_1268330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11564948873766124590906611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30839863663376332242417629 11564948873766124590906611)
  ·
    refine ⟨17347423310649186886359917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11564948873766124590906611 17347423310649186886359917)
    ·
      refine ⟨6505283741493445082384969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17347423310649186886359917 6505283741493445082384969)
      ·
        refine ⟨4878962806120083811788727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6505283741493445082384969 4878962806120083811788727)
        ·
          refine ⟨7318444209180125717683091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878962806120083811788727 7318444209180125717683091)
          ·
            refine ⟨10977666313770188576524637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318444209180125717683091 10977666313770188576524637)
            ·
              refine ⟨4116624867663820716196739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10977666313770188576524637 4116624867663820716196739)
              ·
                refine ⟨6174937301495731074295109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116624867663820716196739 6174937301495731074295109)
                ·
                  refine ⟨1157800744030449576430333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6174937301495731074295109 1157800744030449576430333)
                  ·
                    refine ⟨434175279011418591161375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157800744030449576430333 434175279011418591161375)
                    ·
                      rfl

theorem cell22_1268330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1268330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268330 prefixEnd_1268330 := by exact prefixLift 1268330
  have htrace : WordTrace (prefixWord ++ tailWord_1268330) baseStart_1268330 baseEnd_1268330 := by
    simpa [prefixWord, tailWord_1268330, baseEnd_1268330] using wordTrace_append hprefix tailTrace_1268330
  have hstable : (prefixWord ++ tailWord_1268330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268330).length < 2 ^ (prefixWord ++ tailWord_1268330).sum := by decide
  have hdescent : baseEnd_1268330 < baseStart_1268330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268388 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 7]
def baseStart_1268388 : Nat := 118140960795 + 1268388 * 2 ^ 59
def prefixEnd_1268388 : Nat := 4983230072969 + 3 ^ 40 * 1268388 * 2
def baseEnd_1268388 : Nat := 144731711198908591070399

theorem tailTrace_1268388 : CollatzResearch.WordTrace tailWord_1268388 prefixEnd_1268388 144731711198908591070399 := by
  unfold tailWord_1268388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23130955464427187134618909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30841273952569582846158545 23130955464427187134618909)
  ·
    refine ⟨8674108299160195175482091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23130955464427187134618909 8674108299160195175482091)
    ·
      refine ⟨13011162448740292763223137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8674108299160195175482091 13011162448740292763223137)
      ·
        refine ⟨9758371836555219572417353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13011162448740292763223137 9758371836555219572417353)
        ·
          refine ⟨7318778877416414679313015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9758371836555219572417353 7318778877416414679313015)
          ·
            refine ⟨10978168316124622018969523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318778877416414679313015 10978168316124622018969523)
            ·
              refine ⟨16467252474186933028454285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10978168316124622018969523 16467252474186933028454285)
              ·
                refine ⟨6175219677820099885670357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16467252474186933028454285 6175219677820099885670357)
                ·
                  refine ⟨144731711198908591070399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6175219677820099885670357 144731711198908591070399)
                  ·
                    rfl

theorem cell22_1268388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_1268388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268388 prefixEnd_1268388 := by exact prefixLift 1268388
  have htrace : WordTrace (prefixWord ++ tailWord_1268388) baseStart_1268388 baseEnd_1268388 := by
    simpa [prefixWord, tailWord_1268388, baseEnd_1268388] using wordTrace_append hprefix tailTrace_1268388
  have hstable : (prefixWord ++ tailWord_1268388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268388).length < 2 ^ (prefixWord ++ tailWord_1268388).sum := by decide
  have hdescent : baseEnd_1268388 < baseStart_1268388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268448 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_1268448 : Nat := 118140960795 + 1268448 * 2 ^ 59
def prefixEnd_1268448 : Nat := 4983230072969 + 3 ^ 40 * 1268448 * 2
def baseEnd_1268448 : Nat := 434215672822905616711013

theorem tailTrace_1268448 : CollatzResearch.WordTrace tailWord_1268448 prefixEnd_1268448 434215672822905616711013 := by
  unfold tailWord_1268448
  simp only [CollatzResearch.WordTrace]
  refine ⟨23132049654318502258210999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30842732872424669677614665 23132049654318502258210999)
  ·
    refine ⟨34698074481477753387316499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23132049654318502258210999 34698074481477753387316499)
    ·
      refine ⟨52047111722216630080974749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34698074481477753387316499 52047111722216630080974749)
      ·
        refine ⟨19517666895831236280365531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52047111722216630080974749 19517666895831236280365531)
        ·
          refine ⟨29276500343746854420548297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19517666895831236280365531 29276500343746854420548297)
          ·
            refine ⟨21957375257810140815411223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29276500343746854420548297 21957375257810140815411223)
            ·
              refine ⟨32936062886715211223116835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21957375257810140815411223 32936062886715211223116835)
              ·
                refine ⟨49404094330072816834675253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32936062886715211223116835 49404094330072816834675253)
                ·
                  refine ⟨4631633843444326578250805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49404094330072816834675253 4631633843444326578250805)
                  ·
                    refine ⟨434215672822905616711013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4631633843444326578250805 434215672822905616711013)
                    ·
                      rfl

theorem cell22_1268448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_1268448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268448 prefixEnd_1268448 := by exact prefixLift 1268448
  have htrace : WordTrace (prefixWord ++ tailWord_1268448) baseStart_1268448 baseEnd_1268448 := by
    simpa [prefixWord, tailWord_1268448, baseEnd_1268448] using wordTrace_append hprefix tailTrace_1268448
  have hstable : (prefixWord ++ tailWord_1268448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268448).length < 2 ^ (prefixWord ++ tailWord_1268448).sum := by decide
  have hdescent : baseEnd_1268448 < baseStart_1268448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268465 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_1268465 : Nat := 118140960795 + 1268465 * 2 ^ 59
def prefixEnd_1268465 : Nat := 4983230072969 + 3 ^ 40 * 1268465 * 2
def baseEnd_1268465 : Nat := 434221492270323239035961

theorem tailTrace_1268465 : CollatzResearch.WordTrace tailWord_1268465 prefixEnd_1268465 434221492270323239035961 := by
  unfold tailWord_1268465
  simp only [CollatzResearch.WordTrace]
  refine ⟨46264719349575416419790849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30843146233050277613193899 46264719349575416419790849)
  ·
    refine ⟨34698539512181562314843137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46264719349575416419790849 34698539512181562314843137)
    ·
      refine ⟨26023904634136171736132353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34698539512181562314843137 26023904634136171736132353)
      ·
        refine ⟨19517928475602128802099265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26023904634136171736132353 19517928475602128802099265)
        ·
          refine ⟨14638446356701596601574449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19517928475602128802099265 14638446356701596601574449)
          ·
            refine ⟨10978834767526197451180837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14638446356701596601574449 10978834767526197451180837)
            ·
              refine ⟨2058531518911162022096407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10978834767526197451180837 2058531518911162022096407)
              ·
                refine ⟨3087797278366743033144611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058531518911162022096407 3087797278366743033144611)
                ·
                  refine ⟨4631695917550114549716917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087797278366743033144611 4631695917550114549716917)
                  ·
                    refine ⟨434221492270323239035961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4631695917550114549716917 434221492270323239035961)
                    ·
                      rfl

theorem cell22_1268465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_1268465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268465 prefixEnd_1268465 := by exact prefixLift 1268465
  have htrace : WordTrace (prefixWord ++ tailWord_1268465) baseStart_1268465 baseEnd_1268465 := by
    simpa [prefixWord, tailWord_1268465, baseEnd_1268465] using wordTrace_append hprefix tailTrace_1268465
  have hstable : (prefixWord ++ tailWord_1268465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268465).length < 2 ^ (prefixWord ++ tailWord_1268465).sum := by decide
  have hdescent : baseEnd_1268465 < baseStart_1268465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268482 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1268482 : Nat := 118140960795 + 1268482 * 2 ^ 59
def prefixEnd_1268482 : Nat := 4983230072969 + 3 ^ 40 * 1268482 * 2
def baseEnd_1268482 : Nat := 434227311717740861360909

theorem tailTrace_1268482 : CollatzResearch.WordTrace tailWord_1268482 prefixEnd_1268482 434227311717740861360909 := by
  unfold tailWord_1268482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11566334847628457080789925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30843559593675885548773133 11566334847628457080789925)
  ·
    refine ⟨2168687783930335702648111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11566334847628457080789925 2168687783930335702648111)
    ·
      refine ⟨3253031675895503553972167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168687783930335702648111 3253031675895503553972167)
      ·
        refine ⟨4879547513843255330958251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3253031675895503553972167 4879547513843255330958251)
        ·
          refine ⟨7319321270764882996437377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4879547513843255330958251 7319321270764882996437377)
          ·
            refine ⟨5489490953073662247328033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7319321270764882996437377 5489490953073662247328033)
            ·
              refine ⟨4117118214805246685496025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5489490953073662247328033 4117118214805246685496025)
              ·
                refine ⟨3087838661103935014122019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4117118214805246685496025 3087838661103935014122019)
                ·
                  refine ⟨4631757991655902521183029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087838661103935014122019 4631757991655902521183029)
                  ·
                    refine ⟨434227311717740861360909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4631757991655902521183029 434227311717740861360909)
                    ·
                      rfl

theorem cell22_1268482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1268482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268482 prefixEnd_1268482 := by exact prefixLift 1268482
  have htrace : WordTrace (prefixWord ++ tailWord_1268482) baseStart_1268482 baseEnd_1268482 := by
    simpa [prefixWord, tailWord_1268482, baseEnd_1268482] using wordTrace_append hprefix tailTrace_1268482
  have hstable : (prefixWord ++ tailWord_1268482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268482).length < 2 ^ (prefixWord ++ tailWord_1268482).sum := by decide
  have hdescent : baseEnd_1268482 < baseStart_1268482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268516 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_1268516 : Nat := 118140960795 + 1268516 * 2 ^ 59
def prefixEnd_1268516 : Nat := 4983230072969 + 3 ^ 40 * 1268516 * 2
def baseEnd_1268516 : Nat := 434238950612576106010805

theorem tailTrace_1268516 : CollatzResearch.WordTrace tailWord_1268516 prefixEnd_1268516 434238950612576106010805 := by
  unfold tailWord_1268516
  simp only [CollatzResearch.WordTrace]
  refine ⟨23133289736195326064948701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30844386314927101419931601 23133289736195326064948701)
  ·
    refine ⟨8674983651073247274355763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23133289736195326064948701 8674983651073247274355763)
    ·
      refine ⟨13012475476609870911533645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8674983651073247274355763 13012475476609870911533645)
      ·
        refine ⟨4879678303728701591825117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13012475476609870911533645 4879678303728701591825117)
        ·
          refine ⟨1829879363898263096934419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4879678303728701591825117 1829879363898263096934419)
          ·
            refine ⟨2744819045847394645401629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829879363898263096934419 2744819045847394645401629)
            ·
              refine ⟨1029307142192772992025611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2744819045847394645401629 1029307142192772992025611)
              ·
                refine ⟨1543960713289159488038417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029307142192772992025611 1543960713289159488038417)
                ·
                  refine ⟨1157970534966869616028813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1543960713289159488038417 1157970534966869616028813)
                  ·
                    refine ⟨434238950612576106010805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157970534966869616028813 434238950612576106010805)
                    ·
                      rfl

theorem cell22_1268516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_1268516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268516 prefixEnd_1268516 := by exact prefixLift 1268516
  have htrace : WordTrace (prefixWord ++ tailWord_1268516) baseStart_1268516 baseEnd_1268516 := by
    simpa [prefixWord, tailWord_1268516, baseEnd_1268516] using wordTrace_append hprefix tailTrace_1268516
  have hstable : (prefixWord ++ tailWord_1268516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268516).length < 2 ^ (prefixWord ++ tailWord_1268516).sum := by decide
  have hdescent : baseEnd_1268516 < baseStart_1268516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268523 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 9]
def baseStart_1268523 : Nat := 118140960795 + 1268523 * 2 ^ 59
def prefixEnd_1268523 : Nat := 4983230072969 + 3 ^ 40 * 1268523 * 2
def baseEnd_1268523 : Nat := 144747115618543473695261

theorem tailTrace_1268523 : CollatzResearch.WordTrace tailWord_1268523 prefixEnd_1268523 144747115618543473695261 := by
  unfold tailWord_1268523
  simp only [CollatzResearch.WordTrace]
  refine ⟨46266834783365292325402223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30844556522243528216934815 46266834783365292325402223)
  ·
    refine ⟨69400252175047938488103335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46266834783365292325402223 69400252175047938488103335)
    ·
      refine ⟨104100378262571907732155003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69400252175047938488103335 104100378262571907732155003)
      ·
        refine ⟨156150567393857861598232505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104100378262571907732155003 156150567393857861598232505)
        ·
          refine ⟨117112925545393396198674379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156150567393857861598232505 117112925545393396198674379)
          ·
            refine ⟨175669388318090094298011569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117112925545393396198674379 175669388318090094298011569)
            ·
              refine ⟨131752041238567570723508677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175669388318090094298011569 131752041238567570723508677)
              ·
                refine ⟨24703507732231419510657877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131752041238567570723508677 24703507732231419510657877)
                ·
                  refine ⟨144747115618543473695261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24703507732231419510657877 144747115618543473695261)
                  ·
                    rfl

theorem cell22_1268523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_1268523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268523 prefixEnd_1268523 := by exact prefixLift 1268523
  have htrace : WordTrace (prefixWord ++ tailWord_1268523) baseStart_1268523 baseEnd_1268523 := by
    simpa [prefixWord, tailWord_1268523, baseEnd_1268523] using wordTrace_append hprefix tailTrace_1268523
  have hstable : (prefixWord ++ tailWord_1268523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268523).length < 2 ^ (prefixWord ++ tailWord_1268523).sum := by decide
  have hdescent : baseEnd_1268523 < baseStart_1268523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268561 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 3, 3]
def baseStart_1268561 : Nat := 118140960795 + 1268561 * 2 ^ 59
def prefixEnd_1268561 : Nat := 4983230072969 + 3 ^ 40 * 1268561 * 2
def baseEnd_1268561 : Nat := 434254355032210988635667

theorem tailTrace_1268561 : CollatzResearch.WordTrace tailWord_1268561 prefixEnd_1268561 434254355032210988635667 := by
  unfold tailWord_1268561
  simp only [CollatzResearch.WordTrace]
  refine ⟨46268220757227624815285537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30845480504818416543523691 46268220757227624815285537)
  ·
    refine ⟨34701165567920718611464153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46268220757227624815285537 34701165567920718611464153)
    ·
      refine ⟨26025874175940538958598115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34701165567920718611464153 26025874175940538958598115)
      ·
        refine ⟨39038811263910808437897173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26025874175940538958598115 39038811263910808437897173)
        ·
          refine ⟨914972138997909572763215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 39038811263910808437897173 914972138997909572763215)
          ·
            refine ⟨1372458208496864359144823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914972138997909572763215 1372458208496864359144823)
            ·
              refine ⟨2058687312745296538717235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372458208496864359144823 2058687312745296538717235)
              ·
                refine ⟨3088030969117944808075853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058687312745296538717235 3088030969117944808075853)
                ·
                  refine ⟨1158011613419229303028445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3088030969117944808075853 1158011613419229303028445)
                  ·
                    refine ⟨434254355032210988635667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158011613419229303028445 434254355032210988635667)
                    ·
                      rfl

theorem cell22_1268561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_1268561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268561 prefixEnd_1268561 := by exact prefixLift 1268561
  have htrace : WordTrace (prefixWord ++ tailWord_1268561) baseStart_1268561 baseEnd_1268561 := by
    simpa [prefixWord, tailWord_1268561, baseEnd_1268561] using wordTrace_append hprefix tailTrace_1268561
  have hstable : (prefixWord ++ tailWord_1268561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268561).length < 2 ^ (prefixWord ++ tailWord_1268561).sum := by decide
  have hdescent : baseEnd_1268561 < baseStart_1268561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268587 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 1, 4]
def baseStart_1268587 : Nat := 118140960795 + 1268587 * 2 ^ 59
def prefixEnd_1268587 : Nat := 4983230072969 + 3 ^ 40 * 1268587 * 2
def baseEnd_1268587 : Nat := 434263255363555587485587

theorem tailTrace_1268587 : CollatzResearch.WordTrace tailWord_1268587 prefixEnd_1268587 434263255363555587485587 := by
  unfold tailWord_1268587
  simp only [CollatzResearch.WordTrace]
  refine ⟨46269169055133431255732015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30846112703422287503821343 46269169055133431255732015)
  ·
    refine ⟨69403753582700146883598023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46269169055133431255732015 69403753582700146883598023)
    ·
      refine ⟨104105630374050220325397035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69403753582700146883598023 104105630374050220325397035)
      ·
        refine ⟨156158445561075330488095553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104105630374050220325397035 156158445561075330488095553)
        ·
          refine ⟨117118834170806497866071665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156158445561075330488095553 117118834170806497866071665)
          ·
            refine ⟨87839125628104873399553749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117118834170806497866071665 87839125628104873399553749)
            ·
              refine ⟨2058729506908707970302041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87839125628104873399553749 2058729506908707970302041)
              ·
                refine ⟨1544047130181530977726531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058729506908707970302041 1544047130181530977726531)
                ·
                  refine ⟨2316070695272296466589797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544047130181530977726531 2316070695272296466589797)
                  ·
                    refine ⟨434263255363555587485587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2316070695272296466589797 434263255363555587485587)
                    ·
                      rfl

theorem cell22_1268587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 4].length) (baseStart_1268587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268587 prefixEnd_1268587 := by exact prefixLift 1268587
  have htrace : WordTrace (prefixWord ++ tailWord_1268587) baseStart_1268587 baseEnd_1268587 := by
    simpa [prefixWord, tailWord_1268587, baseEnd_1268587] using wordTrace_append hprefix tailTrace_1268587
  have hstable : (prefixWord ++ tailWord_1268587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268587).length < 2 ^ (prefixWord ++ tailWord_1268587).sum := by decide
  have hdescent : baseEnd_1268587 < baseStart_1268587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268602 : List Nat := [3, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_1268602 : Nat := 118140960795 + 1268602 * 2 ^ 59
def prefixEnd_1268602 : Nat := 4983230072969 + 3 ^ 40 * 1268602 * 2
def baseEnd_1268602 : Nat := 144756130056700182786847

theorem tailTrace_1268602 : CollatzResearch.WordTrace tailWord_1268602 prefixEnd_1268602 144756130056700182786847 := by
  unfold tailWord_1268602
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567429037519772204382015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30846477433386059211685373 11567429037519772204382015)
  ·
    refine ⟨17351143556279658306573023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11567429037519772204382015 17351143556279658306573023)
    ·
      refine ⟨26026715334419487459859535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17351143556279658306573023 26026715334419487459859535)
      ·
        refine ⟨39040073001629231189789303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26026715334419487459859535 39040073001629231189789303)
        ·
          refine ⟨58560109502443846784683955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39040073001629231189789303 58560109502443846784683955)
          ·
            refine ⟨87840164253665770177025933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58560109502443846784683955 87840164253665770177025933)
            ·
              refine ⟨32940061595124663816384725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87840164253665770177025933 32940061595124663816384725)
              ·
                refine ⟨772032693635734308196517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32940061595124663816384725 772032693635734308196517)
                ·
                  refine ⟨144756130056700182786847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772032693635734308196517 144756130056700182786847)
                  ·
                    rfl

theorem cell22_1268602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_1268602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268602 prefixEnd_1268602 := by exact prefixLift 1268602
  have htrace : WordTrace (prefixWord ++ tailWord_1268602) baseStart_1268602 baseEnd_1268602 := by
    simpa [prefixWord, tailWord_1268602, baseEnd_1268602] using wordTrace_append hprefix tailTrace_1268602
  have hstable : (prefixWord ++ tailWord_1268602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268602).length < 2 ^ (prefixWord ++ tailWord_1268602).sum := by decide
  have hdescent : baseEnd_1268602 < baseStart_1268602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268619 : List Nat := [1, 1, 1, 1, 4, 2, 6, 2, 4]
def baseStart_1268619 : Nat := 118140960795 + 1268619 * 2 ^ 59
def prefixEnd_1268619 : Nat := 4983230072969 + 3 ^ 40 * 1268619 * 2
def baseEnd_1268619 : Nat := 144758069872506056895163

theorem tailTrace_1268619 : CollatzResearch.WordTrace tailWord_1268619 prefixEnd_1268619 144758069872506056895163 := by
  unfold tailWord_1268619
  simp only [CollatzResearch.WordTrace]
  refine ⟨46270336191017500720896911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30846890794011667147264607 46270336191017500720896911)
  ·
    refine ⟨69405504286526251081345367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46270336191017500720896911 69405504286526251081345367)
    ·
      refine ⟨104108256429789376622018051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69405504286526251081345367 104108256429789376622018051)
      ·
        refine ⟨156162384644684064933027077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104108256429789376622018051 156162384644684064933027077)
        ·
          refine ⟨29280447120878262174942577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156162384644684064933027077 29280447120878262174942577)
          ·
            refine ⟨21960335340658696631206933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29280447120878262174942577 21960335340658696631206933)
            ·
              refine ⟨1029390719093376404587825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21960335340658696631206933 1029390719093376404587825)
              ·
                refine ⟨772043039320032303440869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029390719093376404587825 772043039320032303440869)
                ·
                  refine ⟨144758069872506056895163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772043039320032303440869 144758069872506056895163)
                  ·
                    rfl

theorem cell22_1268619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 4].length) (baseStart_1268619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268619 prefixEnd_1268619 := by exact prefixLift 1268619
  have htrace : WordTrace (prefixWord ++ tailWord_1268619) baseStart_1268619 baseEnd_1268619 := by
    simpa [prefixWord, tailWord_1268619, baseEnd_1268619] using wordTrace_append hprefix tailTrace_1268619
  have hstable : (prefixWord ++ tailWord_1268619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268619).length < 2 ^ (prefixWord ++ tailWord_1268619).sum := by decide
  have hdescent : baseEnd_1268619 < baseStart_1268619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268634 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_1268634 : Nat := 118140960795 + 1268634 * 2 ^ 59
def prefixEnd_1268634 : Nat := 4983230072969 + 3 ^ 40 * 1268634 * 2
def baseEnd_1268634 : Nat := 434279344424063131560443

theorem tailTrace_1268634 : CollatzResearch.WordTrace tailWord_1268634 prefixEnd_1268634 434279344424063131560443 := by
  unfold tailWord_1268634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567720821490789570673239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30847255523975438855128637 11567720821490789570673239)
  ·
    refine ⟨17351581232236184356009859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11567720821490789570673239 17351581232236184356009859)
    ·
      refine ⟨26027371848354276534014789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17351581232236184356009859 26027371848354276534014789)
      ·
        refine ⟨4880132221566426850127773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26027371848354276534014789 4880132221566426850127773)
        ·
          refine ⟨1830049583087410068797915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4880132221566426850127773 1830049583087410068797915)
          ·
            refine ⟨2745074374631115103196873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830049583087410068797915 2745074374631115103196873)
            ·
              refine ⟨2058805780973336327397655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745074374631115103196873 2058805780973336327397655)
              ·
                refine ⟨3088208671460004491096483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058805780973336327397655 3088208671460004491096483)
                ·
                  refine ⟨4632313007190006736644725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088208671460004491096483 4632313007190006736644725)
                  ·
                    refine ⟨434279344424063131560443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4632313007190006736644725 434279344424063131560443)
                    ·
                      rfl

theorem cell22_1268634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_1268634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268634 prefixEnd_1268634 := by exact prefixLift 1268634
  have htrace : WordTrace (prefixWord ++ tailWord_1268634) baseStart_1268634 baseEnd_1268634 := by
    simpa [prefixWord, tailWord_1268634, baseEnd_1268634] using wordTrace_append hprefix tailTrace_1268634
  have hstable : (prefixWord ++ tailWord_1268634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268634).length < 2 ^ (prefixWord ++ tailWord_1268634).sum := by decide
  have hdescent : baseEnd_1268634 < baseStart_1268634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268653 : List Nat := [1, 5, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1268653 : Nat := 118140960795 + 1268653 * 2 ^ 59
def prefixEnd_1268653 : Nat := 4983230072969 + 3 ^ 40 * 1268653 * 2
def baseEnd_1268653 : Nat := 144761949504117805111795

theorem tailTrace_1268653 : CollatzResearch.WordTrace tailWord_1268653 prefixEnd_1268653 144761949504117805111795 := by
  unfold tailWord_1268653
  simp only [CollatzResearch.WordTrace]
  refine ⟨46271576272894324527634613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30847717515262883018423075 46271576272894324527634613)
  ·
    refine ⟨4337960275583842924465745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46271576272894324527634613 4337960275583842924465745)
    ·
      refine ⟨3253470206687882193349309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4337960275583842924465745 3253470206687882193349309)
      ·
        refine ⟨1220051327507955822505991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3253470206687882193349309 1220051327507955822505991)
        ·
          refine ⟨1830076991261933733758987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220051327507955822505991 1830076991261933733758987)
          ·
            refine ⟨2745115486892900600638481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830076991261933733758987 2745115486892900600638481)
            ·
              refine ⟨2058836615169675450478861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745115486892900600638481 2058836615169675450478861)
              ·
                refine ⟨772063730688628293929573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2058836615169675450478861 772063730688628293929573)
                ·
                  refine ⟨144761949504117805111795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772063730688628293929573 144761949504117805111795)
                  ·
                    rfl

theorem cell22_1268653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1268653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268653 prefixEnd_1268653 := by exact prefixLift 1268653
  have htrace : WordTrace (prefixWord ++ tailWord_1268653) baseStart_1268653 baseEnd_1268653 := by
    simpa [prefixWord, tailWord_1268653, baseEnd_1268653] using wordTrace_append hprefix tailTrace_1268653
  have hstable : (prefixWord ++ tailWord_1268653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268653).length < 2 ^ (prefixWord ++ tailWord_1268653).sum := by decide
  have hdescent : baseEnd_1268653 < baseStart_1268653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268675 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 7]
def baseStart_1268675 : Nat := 118140960795 + 1268675 * 2 ^ 59
def prefixEnd_1268675 : Nat := 4983230072969 + 3 ^ 40 * 1268675 * 2
def baseEnd_1268675 : Nat := 144764459853984230428439

theorem tailTrace_1268675 : CollatzResearch.WordTrace tailWord_1268675 prefixEnd_1268675 144764459853984230428439 := by
  unfold tailWord_1268675
  simp only [CollatzResearch.WordTrace]
  refine ⟨46272378678814622284935479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30848252452543081523290319 46272378678814622284935479)
  ·
    refine ⟨69408568018221933427403219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46272378678814622284935479 69408568018221933427403219)
    ·
      refine ⟨104112852027332900141104829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69408568018221933427403219 104112852027332900141104829)
      ·
        refine ⟨39042319510249837552914311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104112852027332900141104829 39042319510249837552914311)
        ·
          refine ⟨58563479265374756329371467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39042319510249837552914311 58563479265374756329371467)
          ·
            refine ⟨87845218898062134494057201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58563479265374756329371467 87845218898062134494057201)
            ·
              refine ⟨65883914173546600870542901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87845218898062134494057201 65883914173546600870542901)
              ·
                refine ⟨6176616953769993831613397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65883914173546600870542901 6176616953769993831613397)
                ·
                  refine ⟨144764459853984230428439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6176616953769993831613397 144764459853984230428439)
                  ·
                    rfl

theorem cell22_1268675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_1268675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268675 prefixEnd_1268675 := by exact prefixLift 1268675
  have htrace : WordTrace (prefixWord ++ tailWord_1268675) baseStart_1268675 baseEnd_1268675 := by
    simpa [prefixWord, tailWord_1268675, baseEnd_1268675] using wordTrace_append hprefix tailTrace_1268675
  have hstable : (prefixWord ++ tailWord_1268675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268675).length < 2 ^ (prefixWord ++ tailWord_1268675).sum := by decide
  have hdescent : baseEnd_1268675 < baseStart_1268675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268685 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1268685 : Nat := 118140960795 + 1268685 * 2 ^ 59
def prefixEnd_1268685 : Nat := 4983230072969 + 3 ^ 40 * 1268685 * 2
def baseEnd_1268685 : Nat := 434296802766315998535287

theorem tailTrace_1268685 : CollatzResearch.WordTrace tailWord_1268685 prefixEnd_1268685 434296802766315998535287 := by
  unfold tailWord_1268685
  simp only [CollatzResearch.WordTrace]
  refine ⟨46272743408778393992799509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30848495605852262661866339 46272743408778393992799509)
  ·
    refine ⟨2169034847286487218412477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46272743408778393992799509 2169034847286487218412477)
    ·
      refine ⟨813388067732432706904679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2169034847286487218412477 813388067732432706904679)
      ·
        refine ⟨1220082101598649060357019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813388067732432706904679 1220082101598649060357019)
        ·
          refine ⟨1830123152397973590535529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220082101598649060357019 1830123152397973590535529)
          ·
            refine ⟨1372592364298480192901647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830123152397973590535529 1372592364298480192901647)
            ·
              refine ⟨2058888546447720289352471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372592364298480192901647 2058888546447720289352471)
              ·
                refine ⟨3088332819671580434028707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058888546447720289352471 3088332819671580434028707)
                ·
                  refine ⟨4632499229507370651043061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088332819671580434028707 4632499229507370651043061)
                  ·
                    refine ⟨434296802766315998535287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4632499229507370651043061 434296802766315998535287)
                    ·
                      rfl

theorem cell22_1268685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1268685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268685 prefixEnd_1268685 := by exact prefixLift 1268685
  have htrace : WordTrace (prefixWord ++ tailWord_1268685) baseStart_1268685 baseEnd_1268685 := by
    simpa [prefixWord, tailWord_1268685, baseEnd_1268685] using wordTrace_append hprefix tailTrace_1268685
  have hstable : (prefixWord ++ tailWord_1268685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268685).length < 2 ^ (prefixWord ++ tailWord_1268685).sum := by decide
  have hdescent : baseEnd_1268685 < baseStart_1268685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268769 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1268769 : Nat := 118140960795 + 1268769 * 2 ^ 59
def prefixEnd_1268769 : Nat := 4983230072969 + 3 ^ 40 * 1268769 * 2
def baseEnd_1268769 : Nat := 434325557682967779435029

theorem tailTrace_1268769 : CollatzResearch.WordTrace tailWord_1268769 prefixEnd_1268769 434325557682967779435029 := by
  unfold tailWord_1268769
  simp only [CollatzResearch.WordTrace]
  refine ⟨46275807140474076338857361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30850538093649384225904907 46275807140474076338857361)
  ·
    refine ⟨34706855355355557254143021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46275807140474076338857361 34706855355355557254143021)
    ·
      refine ⟨13015070758258333970303633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34706855355355557254143021 13015070758258333970303633)
      ·
        refine ⟨9761303068693750477727725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13015070758258333970303633 9761303068693750477727725)
        ·
          refine ⟨3660488650760156429147897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9761303068693750477727725 3660488650760156429147897)
          ·
            refine ⟨2745366488070117321860923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3660488650760156429147897 2745366488070117321860923)
            ·
              refine ⟨4118049732105175982791385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2745366488070117321860923 4118049732105175982791385)
              ·
                refine ⟨3088537299078881987093539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4118049732105175982791385 3088537299078881987093539)
                ·
                  refine ⟨4632805948618322980640309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088537299078881987093539 4632805948618322980640309)
                  ·
                    refine ⟨434325557682967779435029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4632805948618322980640309 434325557682967779435029)
                    ·
                      rfl

theorem cell22_1268769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1268769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268769 prefixEnd_1268769 := by exact prefixLift 1268769
  have htrace : WordTrace (prefixWord ++ tailWord_1268769) baseStart_1268769 baseEnd_1268769 := by
    simpa [prefixWord, tailWord_1268769, baseEnd_1268769] using wordTrace_append hprefix tailTrace_1268769
  have hstable : (prefixWord ++ tailWord_1268769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268769).length < 2 ^ (prefixWord ++ tailWord_1268769).sum := by decide
  have hdescent : baseEnd_1268769 < baseStart_1268769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268786 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_1268786 : Nat := 118140960795 + 1268786 * 2 ^ 59
def prefixEnd_1268786 : Nat := 4983230072969 + 3 ^ 40 * 1268786 * 2
def baseEnd_1268786 : Nat := 434331377130385401759977

theorem tailTrace_1268786 : CollatzResearch.WordTrace tailWord_1268786 prefixEnd_1268786 434331377130385401759977 := by
  unfold tailWord_1268786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11569106795353122060556553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30850951454274992161484141 11569106795353122060556553)
  ·
    refine ⟨8676830096514841545417415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11569106795353122060556553 8676830096514841545417415)
    ·
      refine ⟨13015245144772262318126123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8676830096514841545417415 13015245144772262318126123)
      ·
        refine ⟨19522867717158393477189185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13015245144772262318126123 19522867717158393477189185)
        ·
          refine ⟨14642150787868795107891889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19522867717158393477189185 14642150787868795107891889)
          ·
            refine ⟨10981613090901596330918917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14642150787868795107891889 10981613090901596330918917)
            ·
              refine ⟨2059052454544049312047297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10981613090901596330918917 2059052454544049312047297)
              ·
                refine ⟨1544289340908036984035473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059052454544049312047297 1544289340908036984035473)
                ·
                  refine ⟨1158217005681027738026605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544289340908036984035473 1158217005681027738026605)
                  ·
                    refine ⟨434331377130385401759977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158217005681027738026605 434331377130385401759977)
                    ·
                      rfl

theorem cell22_1268786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_1268786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268786 prefixEnd_1268786 := by exact prefixLift 1268786
  have htrace : WordTrace (prefixWord ++ tailWord_1268786) baseStart_1268786 baseEnd_1268786 := by
    simpa [prefixWord, tailWord_1268786, baseEnd_1268786] using wordTrace_append hprefix tailTrace_1268786
  have hstable : (prefixWord ++ tailWord_1268786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268786).length < 2 ^ (prefixWord ++ tailWord_1268786).sum := by decide
  have hdescent : baseEnd_1268786 < baseStart_1268786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268788 : List Nat := [2, 5, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1268788 : Nat := 118140960795 + 1268788 * 2 ^ 59
def prefixEnd_1268788 : Nat := 4983230072969 + 3 ^ 40 * 1268788 * 2
def baseEnd_1268788 : Nat := 144777353923752687736657

theorem tailTrace_1268788 : CollatzResearch.WordTrace tailWord_1268788 prefixEnd_1268788 144777353923752687736657 := by
  unfold tailWord_1268788
  simp only [CollatzResearch.WordTrace]
  refine ⟨23138250063702621291899509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30851000084936828389199345 23138250063702621291899509)
  ·
    refine ⟨2169210943472120746115579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23138250063702621291899509 2169210943472120746115579)
    ·
      refine ⟨3253816415208181119173369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2169210943472120746115579 3253816415208181119173369)
      ·
        refine ⟨2440362311406135839380027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3253816415208181119173369 2440362311406135839380027)
        ·
          refine ⟨3660543467109203759070041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440362311406135839380027 3660543467109203759070041)
          ·
            refine ⟨2745407600331902819302531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3660543467109203759070041 2745407600331902819302531)
            ·
              refine ⟨4118111400497854228953797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2745407600331902819302531 4118111400497854228953797)
              ·
                refine ⟨772145887593347667928837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4118111400497854228953797 772145887593347667928837)
                ·
                  refine ⟨144777353923752687736657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772145887593347667928837 144777353923752687736657)
                  ·
                    rfl

theorem cell22_1268788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1268788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268788 prefixEnd_1268788 := by exact prefixLift 1268788
  have htrace : WordTrace (prefixWord ++ tailWord_1268788) baseStart_1268788 baseEnd_1268788 := by
    simpa [prefixWord, tailWord_1268788, baseEnd_1268788] using wordTrace_append hprefix tailTrace_1268788
  have hstable : (prefixWord ++ tailWord_1268788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268788).length < 2 ^ (prefixWord ++ tailWord_1268788).sum := by decide
  have hdescent : baseEnd_1268788 < baseStart_1268788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268812 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1268812 : Nat := 118140960795 + 1268812 * 2 ^ 59
def prefixEnd_1268812 : Nat := 4983230072969 + 3 ^ 40 * 1268812 * 2
def baseEnd_1268812 : Nat := 434340277461730000609897

theorem tailTrace_1268812 : CollatzResearch.WordTrace tailWord_1268812 prefixEnd_1268812 434340277461730000609897 := by
  unfold tailWord_1268812
  simp only [CollatzResearch.WordTrace]
  refine ⟨23138687739659147341336345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30851583652878863121781793 23138687739659147341336345)
  ·
    refine ⟨17354015804744360506002259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23138687739659147341336345 17354015804744360506002259)
    ·
      refine ⟨26031023707116540759003389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17354015804744360506002259 26031023707116540759003389)
      ·
        refine ⟨9761633890168702784626271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26031023707116540759003389 9761633890168702784626271)
        ·
          refine ⟨14642450835253054176939407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761633890168702784626271 14642450835253054176939407)
          ·
            refine ⟨21963676252879581265409111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14642450835253054176939407 21963676252879581265409111)
            ·
              refine ⟨32945514379319371898113667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21963676252879581265409111 32945514379319371898113667)
              ·
                refine ⟨49418271568979057847170501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32945514379319371898113667 49418271568979057847170501)
                ·
                  refine ⟨9265925919183573346344469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49418271568979057847170501 9265925919183573346344469)
                  ·
                    refine ⟨434340277461730000609897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9265925919183573346344469 434340277461730000609897)
                    ·
                      rfl

theorem cell22_1268812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1268812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268812 prefixEnd_1268812 := by exact prefixLift 1268812
  have htrace : WordTrace (prefixWord ++ tailWord_1268812) baseStart_1268812 baseEnd_1268812 := by
    simpa [prefixWord, tailWord_1268812, baseEnd_1268812] using wordTrace_append hprefix tailTrace_1268812
  have hstable : (prefixWord ++ tailWord_1268812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268812).length < 2 ^ (prefixWord ++ tailWord_1268812).sum := by decide
  have hdescent : baseEnd_1268812 < baseStart_1268812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268861 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 5]
def baseStart_1268861 : Nat := 118140960795 + 1268861 * 2 ^ 59
def prefixEnd_1268861 : Nat := 4983230072969 + 3 ^ 40 * 1268861 * 2
def baseEnd_1268861 : Nat := 144785683721036735378249

theorem tailTrace_1268861 : CollatzResearch.WordTrace tailWord_1268861 prefixEnd_1268861 144785683721036735378249 := by
  unfold tailWord_1268861
  simp only [CollatzResearch.WordTrace]
  refine ⟨46279162656140776051206437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30852775104093850700804291 46279162656140776051206437)
  ·
    refine ⟨8677342998026395509601207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46279162656140776051206437 8677342998026395509601207)
    ·
      refine ⟨13016014497039593264401811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8677342998026395509601207 13016014497039593264401811)
      ·
        refine ⟨19524021745559389896602717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13016014497039593264401811 19524021745559389896602717)
        ·
          refine ⟨7321508154584771211226019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19524021745559389896602717 7321508154584771211226019)
          ·
            refine ⟨10982262231877156816839029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7321508154584771211226019 10982262231877156816839029)
            ·
              refine ⟨1029587084238483451578659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10982262231877156816839029 1029587084238483451578659)
              ·
                refine ⟨1544380626357725177367989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029587084238483451578659 1544380626357725177367989)
                ·
                  refine ⟨144785683721036735378249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1544380626357725177367989 144785683721036735378249)
                  ·
                    rfl

theorem cell22_1268861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_1268861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268861 prefixEnd_1268861 := by exact prefixLift 1268861
  have htrace : WordTrace (prefixWord ++ tailWord_1268861) baseStart_1268861 baseEnd_1268861 := by
    simpa [prefixWord, tailWord_1268861, baseEnd_1268861] using wordTrace_append hprefix tailTrace_1268861
  have hstable : (prefixWord ++ tailWord_1268861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268861).length < 2 ^ (prefixWord ++ tailWord_1268861).sum := by decide
  have hdescent : baseEnd_1268861 < baseStart_1268861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268919 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 4, 4]
def baseStart_1268919 : Nat := 118140960795 + 1268919 * 2 ^ 59
def prefixEnd_1268919 : Nat := 4983230072969 + 3 ^ 40 * 1268919 * 2
def baseEnd_1268919 : Nat := 434376905748417388184569

theorem tailTrace_1268919 : CollatzResearch.WordTrace tailWord_1268919 prefixEnd_1268919 434376905748417388184569 := by
  unfold tailWord_1268919
  simp only [CollatzResearch.WordTrace]
  refine ⟨46281278089930651956817811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30854185393287101304545207 46281278089930651956817811)
  ·
    refine ⟨69421917134895977935226717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46281278089930651956817811 69421917134895977935226717)
    ·
      refine ⟨26033218925585991725710019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69421917134895977935226717 26033218925585991725710019)
      ·
        refine ⟨39049828388378987588565029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26033218925585991725710019 39049828388378987588565029)
        ·
          refine ⟨7321842822821060172855943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39049828388378987588565029 7321842822821060172855943)
          ·
            refine ⟨10982764234231590259283915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7321842822821060172855943 10982764234231590259283915)
            ·
              refine ⟨16474146351347385388925873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10982764234231590259283915 16474146351347385388925873)
              ·
                refine ⟨12355609763510539041694405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16474146351347385388925873 12355609763510539041694405)
                ·
                  refine ⟨2316676830658226070317701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12355609763510539041694405 2316676830658226070317701)
                  ·
                    refine ⟨434376905748417388184569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2316676830658226070317701 434376905748417388184569)
                    ·
                      rfl

theorem cell22_1268919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_1268919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268919 prefixEnd_1268919 := by exact prefixLift 1268919
  have htrace : WordTrace (prefixWord ++ tailWord_1268919) baseStart_1268919 baseEnd_1268919 := by
    simpa [prefixWord, tailWord_1268919, baseEnd_1268919] using wordTrace_append hprefix tailTrace_1268919
  have hstable : (prefixWord ++ tailWord_1268919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268919).length < 2 ^ (prefixWord ++ tailWord_1268919).sum := by decide
  have hdescent : baseEnd_1268919 < baseStart_1268919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268957 : List Nat := [1, 4, 3, 2, 2, 2, 2, 2, 4]
def baseStart_1268957 : Nat := 118140960795 + 1268957 * 2 ^ 59
def prefixEnd_1268957 : Nat := 4983230072969 + 3 ^ 40 * 1268957 * 2
def baseEnd_1268957 : Nat := 144796637974999318578151

theorem tailTrace_1268957 : CollatzResearch.WordTrace tailWord_1268957 prefixEnd_1268957 144796637974999318578151 := by
  unfold tailWord_1268957
  simp only [CollatzResearch.WordTrace]
  refine ⟨46282664063792984446701125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30855109375861989631134083 46282664063792984446701125)
  ·
    refine ⟨8677999511961184583756461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46282664063792984446701125 8677999511961184583756461)
    ·
      refine ⟨3254249816985444218908673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8677999511961184583756461 3254249816985444218908673)
      ·
        refine ⟨2440687362739083164181505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3254249816985444218908673 2440687362739083164181505)
        ·
          refine ⟨1830515522054312373136129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2440687362739083164181505 1830515522054312373136129)
          ·
            refine ⟨1372886641540734279852097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830515522054312373136129 1372886641540734279852097)
            ·
              refine ⟨1029664981155550709889073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1372886641540734279852097 1029664981155550709889073)
              ·
                refine ⟨772248735866663032416805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029664981155550709889073 772248735866663032416805)
                ·
                  refine ⟨144796637974999318578151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772248735866663032416805 144796637974999318578151)
                  ·
                    rfl

theorem cell22_1268957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_1268957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268957 prefixEnd_1268957 := by exact prefixLift 1268957
  have htrace : WordTrace (prefixWord ++ tailWord_1268957) baseStart_1268957 baseEnd_1268957 := by
    simpa [prefixWord, tailWord_1268957, baseEnd_1268957] using wordTrace_append hprefix tailTrace_1268957
  have hstable : (prefixWord ++ tailWord_1268957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268957).length < 2 ^ (prefixWord ++ tailWord_1268957).sum := by decide
  have hdescent : baseEnd_1268957 < baseStart_1268957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268964 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1268964 : Nat := 118140960795 + 1268964 * 2 ^ 59
def prefixEnd_1268964 : Nat := 4983230072969 + 3 ^ 40 * 1268964 * 2
def baseEnd_1268964 : Nat := 434392310168052270809431

theorem tailTrace_1268964 : CollatzResearch.WordTrace tailWord_1268964 prefixEnd_1268964 434392310168052270809431 := by
  unfold tailWord_1268964
  simp only [CollatzResearch.WordTrace]
  refine ⟨23141459687383812321102973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30855279583178416428137297 23141459687383812321102973)
  ·
    refine ⟨8678047382768929620413615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23141459687383812321102973 8678047382768929620413615)
    ·
      refine ⟨13017071074153394430620423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8678047382768929620413615 13017071074153394430620423)
      ·
        refine ⟨19525606611230091645930635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13017071074153394430620423 19525606611230091645930635)
        ·
          refine ⟨29288409916845137468895953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19525606611230091645930635 29288409916845137468895953)
          ·
            refine ⟨21966307437633853101671965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29288409916845137468895953 21966307437633853101671965)
            ·
              refine ⟨8237365289112694913126987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21966307437633853101671965 8237365289112694913126987)
              ·
                refine ⟨12356047933669042369690481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8237365289112694913126987 12356047933669042369690481)
                ·
                  refine ⟨9267035950251781777267861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12356047933669042369690481 9267035950251781777267861)
                  ·
                    refine ⟨434392310168052270809431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9267035950251781777267861 434392310168052270809431)
                    ·
                      rfl

theorem cell22_1268964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1268964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1268964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1268964 prefixEnd_1268964 := by exact prefixLift 1268964
  have htrace : WordTrace (prefixWord ++ tailWord_1268964) baseStart_1268964 baseEnd_1268964 := by
    simpa [prefixWord, tailWord_1268964, baseEnd_1268964] using wordTrace_append hprefix tailTrace_1268964
  have hstable : (prefixWord ++ tailWord_1268964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268964).length < 2 ^ (prefixWord ++ tailWord_1268964).sum := by decide
  have hdescent : baseEnd_1268964 < baseStart_1268964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269041 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 6]
def baseStart_1269041 : Nat := 118140960795 + 1269041 * 2 ^ 59
def prefixEnd_1269041 : Nat := 4983230072969 + 3 ^ 40 * 1269041 * 2
def baseEnd_1269041 : Nat := 144806222947216578878065

theorem tailTrace_1269041 : CollatzResearch.WordTrace tailWord_1269041 prefixEnd_1269041 144806222947216578878065 := by
  unfold tailWord_1269041
  simp only [CollatzResearch.WordTrace]
  refine ⟨46285727795488666792758977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30857151863659111195172651 46285727795488666792758977)
  ·
    refine ⟨34714295846616500094569233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46285727795488666792758977 34714295846616500094569233)
    ·
      refine ⟨26035721884962375070926925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34714295846616500094569233 26035721884962375070926925)
      ·
        refine ⟨9763395706860890651597597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26035721884962375070926925 9763395706860890651597597)
        ·
          refine ⟨3661273390072833994349099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9763395706860890651597597 3661273390072833994349099)
          ·
            refine ⟨5491910085109250991523649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3661273390072833994349099 5491910085109250991523649)
            ·
              refine ⟨4118932563831938243642737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5491910085109250991523649 4118932563831938243642737)
              ·
                refine ⟨3089199422873953682732053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4118932563831938243642737 3089199422873953682732053)
                ·
                  refine ⟨144806222947216578878065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3089199422873953682732053 144806222947216578878065)
                  ·
                    rfl

theorem cell22_1269041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_1269041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269041 prefixEnd_1269041 := by exact prefixLift 1269041
  have htrace : WordTrace (prefixWord ++ tailWord_1269041) baseStart_1269041 baseEnd_1269041 := by
    simpa [prefixWord, tailWord_1269041, baseEnd_1269041] using wordTrace_append hprefix tailTrace_1269041
  have hstable : (prefixWord ++ tailWord_1269041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269041).length < 2 ^ (prefixWord ++ tailWord_1269041).sum := by decide
  have hdescent : baseEnd_1269041 < baseStart_1269041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269043 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 1, 4]
def baseStart_1269043 : Nat := 118140960795 + 1269043 * 2 ^ 59
def prefixEnd_1269043 : Nat := 4983230072969 + 3 ^ 40 * 1269043 * 2
def baseEnd_1269043 : Nat := 434419353482522398084189

theorem tailTrace_1269043 : CollatzResearch.WordTrace tailWord_1269043 prefixEnd_1269043 434419353482522398084189 := by
  unfold tailWord_1269043
  simp only [CollatzResearch.WordTrace]
  refine ⟨46285800741481421134331783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30857200494320947422887855 46285800741481421134331783)
  ·
    refine ⟨69428701112222131701497675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46285800741481421134331783 69428701112222131701497675)
    ·
      refine ⟨104143051668333197552246513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69428701112222131701497675 104143051668333197552246513)
      ·
        refine ⟨78107288751249898164184885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104143051668333197552246513 78107288751249898164184885)
        ·
          refine ⟨7322558320429677952892333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78107288751249898164184885 7322558320429677952892333)
          ·
            refine ⟨2745959370161129232334625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7322558320429677952892333 2745959370161129232334625)
            ·
              refine ⟨2059469527620846924250969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745959370161129232334625 2059469527620846924250969)
              ·
                refine ⟨1544602145715635193188227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059469527620846924250969 1544602145715635193188227)
                ·
                  refine ⟨2316903218573452789782341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544602145715635193188227 2316903218573452789782341)
                  ·
                    refine ⟨434419353482522398084189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2316903218573452789782341 434419353482522398084189)
                    ·
                      rfl

theorem cell22_1269043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 4].length) (baseStart_1269043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269043 prefixEnd_1269043 := by exact prefixLift 1269043
  have htrace : WordTrace (prefixWord ++ tailWord_1269043) baseStart_1269043 baseEnd_1269043 := by
    simpa [prefixWord, tailWord_1269043, baseEnd_1269043] using wordTrace_append hprefix tailTrace_1269043
  have hstable : (prefixWord ++ tailWord_1269043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269043).length < 2 ^ (prefixWord ++ tailWord_1269043).sum := by decide
  have hdescent : baseEnd_1269043 < baseStart_1269043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269056 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 6, 3]
def baseStart_1269056 : Nat := 118140960795 + 1269056 * 2 ^ 59
def prefixEnd_1269056 : Nat := 4983230072969 + 3 ^ 40 * 1269056 * 2
def baseEnd_1269056 : Nat := 434423803648194697509149

theorem tailTrace_1269056 : CollatzResearch.WordTrace tailWord_1269056 prefixEnd_1269056 434423803648194697509149 := by
  unfold tailWord_1269056
  simp only [CollatzResearch.WordTrace]
  refine ⟨23143137445217162177277511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30857516593622882903036681 23143137445217162177277511)
  ·
    refine ⟨34714706167825743265916267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23143137445217162177277511 34714706167825743265916267)
    ·
      refine ⟨52072059251738614898874401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34714706167825743265916267 52072059251738614898874401)
      ·
        refine ⟨39054044438803961174155801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52072059251738614898874401 39054044438803961174155801)
        ·
          refine ⟨29290533329102970880616851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39054044438803961174155801 29290533329102970880616851)
          ·
            refine ⟨43935799993654456320925277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29290533329102970880616851 43935799993654456320925277)
            ·
              refine ⟨16475924997620421120346979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43935799993654456320925277 16475924997620421120346979)
              ·
                refine ⟨24713887496430631680520469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16475924997620421120346979 24713887496430631680520469)
                ·
                  refine ⟨1158463476395185860024397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24713887496430631680520469 1158463476395185860024397)
                  ·
                    refine ⟨434423803648194697509149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158463476395185860024397 434423803648194697509149)
                    ·
                      rfl

theorem cell22_1269056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_1269056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269056 prefixEnd_1269056 := by exact prefixLift 1269056
  have htrace : WordTrace (prefixWord ++ tailWord_1269056) baseStart_1269056 baseEnd_1269056 := by
    simpa [prefixWord, tailWord_1269056, baseEnd_1269056] using wordTrace_append hprefix tailTrace_1269056
  have hstable : (prefixWord ++ tailWord_1269056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269056).length < 2 ^ (prefixWord ++ tailWord_1269056).sum := by decide
  have hdescent : baseEnd_1269056 < baseStart_1269056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269060 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1269060 : Nat := 118140960795 + 1269060 * 2 ^ 59
def prefixEnd_1269060 : Nat := 4983230072969 + 3 ^ 40 * 1269060 * 2
def baseEnd_1269060 : Nat := 434425172929940020409137

theorem tailTrace_1269060 : CollatzResearch.WordTrace tailWord_1269060 prefixEnd_1269060 434425172929940020409137 := by
  unfold tailWord_1269060
  simp only [CollatzResearch.WordTrace]
  refine ⟨23143210391209916518850317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30857613854946555358467089 23143210391209916518850317)
  ·
    refine ⟨8678703896703718694568869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23143210391209916518850317 8678703896703718694568869)
    ·
      refine ⟨1627256980631947255231663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8678703896703718694568869 1627256980631947255231663)
      ·
        refine ⟨2440885470947920882847495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627256980631947255231663 2440885470947920882847495)
        ·
          refine ⟨3661328206421881324271243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440885470947920882847495 3661328206421881324271243)
          ·
            refine ⟨5491992309632821986406865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3661328206421881324271243 5491992309632821986406865)
            ·
              refine ⟨4118994232224616489805149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5491992309632821986406865 4118994232224616489805149)
              ·
                refine ⟨1544622837084231183676931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4118994232224616489805149 1544622837084231183676931)
                ·
                  refine ⟨2316934255626346775515397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544622837084231183676931 2316934255626346775515397)
                  ·
                    refine ⟨434425172929940020409137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2316934255626346775515397 434425172929940020409137)
                    ·
                      rfl

theorem cell22_1269060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1269060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269060 prefixEnd_1269060 := by exact prefixLift 1269060
  have htrace : WordTrace (prefixWord ++ tailWord_1269060) baseStart_1269060 baseEnd_1269060 := by
    simpa [prefixWord, tailWord_1269060, baseEnd_1269060] using wordTrace_append hprefix tailTrace_1269060
  have hstable : (prefixWord ++ tailWord_1269060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269060).length < 2 ^ (prefixWord ++ tailWord_1269060).sum := by decide
  have hdescent : baseEnd_1269060 < baseStart_1269060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269073 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 2, 3]
def baseStart_1269073 : Nat := 118140960795 + 1269073 * 2 ^ 59
def prefixEnd_1269073 : Nat := 4983230072969 + 3 ^ 40 * 1269073 * 2
def baseEnd_1269073 : Nat := 434429623095612319834097

theorem tailTrace_1269073 : CollatzResearch.WordTrace tailWord_1269073 prefixEnd_1269073 434429623095612319834097 := by
  unfold tailWord_1269073
  simp only [CollatzResearch.WordTrace]
  refine ⟨46286894931372736257923873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30857929954248490838615915 46286894931372736257923873)
  ·
    refine ⟨34715171198529552193442905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46286894931372736257923873 34715171198529552193442905)
    ·
      refine ⟨26036378398897164145082179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34715171198529552193442905 26036378398897164145082179)
      ·
        refine ⟨39054567598345746217623269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26036378398897164145082179 39054567598345746217623269)
        ·
          refine ⟨7322731424689827415804363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39054567598345746217623269 7322731424689827415804363)
          ·
            refine ⟨10984097137034741123706545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322731424689827415804363 10984097137034741123706545)
            ·
              refine ⟨8238072852776055842779909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10984097137034741123706545 8238072852776055842779909)
              ·
                refine ⟨1544638659895510470521233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8238072852776055842779909 1544638659895510470521233)
                ·
                  refine ⟨1158478994921632852890925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544638659895510470521233 1158478994921632852890925)
                  ·
                    refine ⟨434429623095612319834097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158478994921632852890925 434429623095612319834097)
                    ·
                      rfl

theorem cell22_1269073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_1269073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269073 prefixEnd_1269073 := by exact prefixLift 1269073
  have htrace : WordTrace (prefixWord ++ tailWord_1269073) baseStart_1269073 baseEnd_1269073 := by
    simpa [prefixWord, tailWord_1269073, baseEnd_1269073] using wordTrace_append hprefix tailTrace_1269073
  have hstable : (prefixWord ++ tailWord_1269073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269073).length < 2 ^ (prefixWord ++ tailWord_1269073).sum := by decide
  have hdescent : baseEnd_1269073 < baseStart_1269073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269090 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1269090 : Nat := 118140960795 + 1269090 * 2 ^ 59
def prefixEnd_1269090 : Nat := 4983230072969 + 3 ^ 40 * 1269090 * 2
def baseEnd_1269090 : Nat := 434435442543029942159045

theorem tailTrace_1269090 : CollatzResearch.WordTrace tailWord_1269090 prefixEnd_1269090 434435442543029942159045 := by
  unfold tailWord_1269090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11571878743077787040323181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30858343314874098774195149 11571878743077787040323181)
  ·
    refine ⟨4339454528654170140121193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11571878743077787040323181 4339454528654170140121193)
    ·
      refine ⟨3254590896490627605090895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4339454528654170140121193 3254590896490627605090895)
      ·
        refine ⟨4881886344735941407636343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254590896490627605090895 4881886344735941407636343)
        ·
          refine ⟨7322829517103912111454515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881886344735941407636343 7322829517103912111454515)
          ·
            refine ⟨10984244275655868167181773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322829517103912111454515 10984244275655868167181773)
            ·
              refine ⟨4119091603370950562693165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10984244275655868167181773 4119091603370950562693165)
              ·
                refine ⟨1544659351264106461009937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4119091603370950562693165 1544659351264106461009937)
                ·
                  refine ⟨1158494513448079845757453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544659351264106461009937 1158494513448079845757453)
                  ·
                    refine ⟨434435442543029942159045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158494513448079845757453 434435442543029942159045)
                    ·
                      rfl

theorem cell22_1269090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1269090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269090 prefixEnd_1269090 := by exact prefixLift 1269090
  have htrace : WordTrace (prefixWord ++ tailWord_1269090) baseStart_1269090 baseEnd_1269090 := by
    simpa [prefixWord, tailWord_1269090, baseEnd_1269090] using wordTrace_append hprefix tailTrace_1269090
  have hstable : (prefixWord ++ tailWord_1269090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269090).length < 2 ^ (prefixWord ++ tailWord_1269090).sum := by decide
  have hdescent : baseEnd_1269090 < baseStart_1269090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269208 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_1269208 : Nat := 118140960795 + 1269208 * 2 ^ 59
def prefixEnd_1269208 : Nat := 4983230072969 + 3 ^ 40 * 1269208 * 2
def baseEnd_1269208 : Nat := 434475836354516967708683

theorem tailTrace_1269208 : CollatzResearch.WordTrace tailWord_1269208 prefixEnd_1269208 434475836354516967708683 := by
  unfold tailWord_1269208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23145909392941827157044139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30861212523922436209392185 23145909392941827157044139)
  ·
    refine ⟨34718864089412740735566209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23145909392941827157044139 34718864089412740735566209)
    ·
      refine ⟨26039148067059555551674657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34718864089412740735566209 26039148067059555551674657)
      ·
        refine ⟨19529361050294666663755993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26039148067059555551674657 19529361050294666663755993)
        ·
          refine ⟨14647020787720999997816995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19529361050294666663755993 14647020787720999997816995)
          ·
            refine ⟨21970531181581499996725493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14647020787720999997816995 21970531181581499996725493)
            ·
              refine ⟨2059737298273265624693015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21970531181581499996725493 2059737298273265624693015)
              ·
                refine ⟨3089605947409898437039523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059737298273265624693015 3089605947409898437039523)
                ·
                  refine ⟨4634408921114847655559285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089605947409898437039523 4634408921114847655559285)
                  ·
                    refine ⟨434475836354516967708683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4634408921114847655559285 434475836354516967708683)
                    ·
                      rfl

theorem cell22_1269208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_1269208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269208 prefixEnd_1269208 := by exact prefixLift 1269208
  have htrace : WordTrace (prefixWord ++ tailWord_1269208) baseStart_1269208 baseEnd_1269208 := by
    simpa [prefixWord, tailWord_1269208, baseEnd_1269208] using wordTrace_append hprefix tailTrace_1269208
  have hstable : (prefixWord ++ tailWord_1269208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269208).length < 2 ^ (prefixWord ++ tailWord_1269208).sum := by decide
  have hdescent : baseEnd_1269208 < baseStart_1269208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269223 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1269223 : Nat := 118140960795 + 1269223 * 2 ^ 59
def prefixEnd_1269223 : Nat := 4983230072969 + 3 ^ 40 * 1269223 * 2
def baseEnd_1269223 : Nat := 434480971161061928583637

theorem tailTrace_1269223 : CollatzResearch.WordTrace tailWord_1269223 prefixEnd_1269223 434480971161061928583637 := by
  unfold tailWord_1269223
  simp only [CollatzResearch.WordTrace]
  refine ⟨46292365880829311875884323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30861577253886207917256215 46292365880829311875884323)
  ·
    refine ⟨69438548821243967813826485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46292365880829311875884323 69438548821243967813826485)
    ·
      refine ⟨6509863951991621982546233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69438548821243967813826485 6509863951991621982546233)
      ·
        refine ⟨4882397963993716486909675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6509863951991621982546233 4882397963993716486909675)
        ·
          refine ⟨7323596945990574730364513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882397963993716486909675 7323596945990574730364513)
          ·
            refine ⟨5492697709492931047773385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7323596945990574730364513 5492697709492931047773385)
            ·
              refine ⟨4119523282119698285830039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5492697709492931047773385 4119523282119698285830039)
              ·
                refine ⟨6179284923179547428745059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119523282119698285830039 6179284923179547428745059)
                ·
                  refine ⟨9268927384769321143117589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179284923179547428745059 9268927384769321143117589)
                  ·
                    refine ⟨434480971161061928583637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9268927384769321143117589 434480971161061928583637)
                    ·
                      rfl

theorem cell22_1269223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1269223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269223 prefixEnd_1269223 := by exact prefixLift 1269223
  have htrace : WordTrace (prefixWord ++ tailWord_1269223) baseStart_1269223 baseEnd_1269223 := by
    simpa [prefixWord, tailWord_1269223, baseEnd_1269223] using wordTrace_append hprefix tailTrace_1269223
  have hstable : (prefixWord ++ tailWord_1269223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269223).length < 2 ^ (prefixWord ++ tailWord_1269223).sum := by decide
  have hdescent : baseEnd_1269223 < baseStart_1269223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269238 : List Nat := [5, 1, 1, 1, 2, 2, 10]
def baseStart_1269238 : Nat := 118140960795 + 1269238 * 2 ^ 59
def prefixEnd_1269238 : Nat := 4983230072969 + 3 ^ 40 * 1269238 * 2
def baseEnd_1269238 : Nat := 16092077998800255165133

theorem tailTrace_1269238 : CollatzResearch.WordTrace tailWord_1269238 prefixEnd_1269238 16092077998800255165133 := by
  unfold tailWord_1269238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893307060985935589855023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30861941983849979625120245 2893307060985935589855023)
  ·
    refine ⟨4339960591478903384782535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2893307060985935589855023 4339960591478903384782535)
    ·
      refine ⟨6509940887218355077173803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339960591478903384782535 6509940887218355077173803)
      ·
        refine ⟨9764911330827532615760705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6509940887218355077173803 9764911330827532615760705)
        ·
          refine ⟨7323683498120649461820529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9764911330827532615760705 7323683498120649461820529)
          ·
            refine ⟨5492762623590487096365397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7323683498120649461820529 5492762623590487096365397)
            ·
              refine ⟨16092077998800255165133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5492762623590487096365397 16092077998800255165133)
              ·
                rfl

theorem cell22_1269238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 10].length) (baseStart_1269238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269238 prefixEnd_1269238 := by exact prefixLift 1269238
  have htrace : WordTrace (prefixWord ++ tailWord_1269238) baseStart_1269238 baseEnd_1269238 := by
    simpa [prefixWord, tailWord_1269238, baseEnd_1269238] using wordTrace_append hprefix tailTrace_1269238
  have hstable : (prefixWord ++ tailWord_1269238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269238).length < 2 ^ (prefixWord ++ tailWord_1269238).sum := by decide
  have hdescent : baseEnd_1269238 < baseStart_1269238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269259 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 2, 3]
def baseStart_1269259 : Nat := 118140960795 + 1269259 * 2 ^ 59
def prefixEnd_1269259 : Nat := 4983230072969 + 3 ^ 40 * 1269259 * 2
def baseEnd_1269259 : Nat := 434493294696769834683527

theorem tailTrace_1269259 : CollatzResearch.WordTrace tailWord_1269259 prefixEnd_1269259 434493294696769834683527 := by
  unfold tailWord_1269259
  simp only [CollatzResearch.WordTrace]
  refine ⟨46293678908698890024194831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30862452605799260016129887 46293678908698890024194831)
  ·
    refine ⟨69440518363048335036292247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46293678908698890024194831 69440518363048335036292247)
    ·
      refine ⟨104160777544572502554438371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69440518363048335036292247 104160777544572502554438371)
      ·
        refine ⟨156241166316858753831657557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104160777544572502554438371 156241166316858753831657557)
        ·
          refine ⟨1830951167775688521464737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 156241166316858753831657557 1830951167775688521464737)
          ·
            refine ⟨1373213375831766391098553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830951167775688521464737 1373213375831766391098553)
            ·
              refine ⟨1029910031873824793323915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373213375831766391098553 1029910031873824793323915)
              ·
                refine ⟨1544865047810737189985873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029910031873824793323915 1544865047810737189985873)
                ·
                  refine ⟨1158648785858052892489405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544865047810737189985873 1158648785858052892489405)
                  ·
                    refine ⟨434493294696769834683527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158648785858052892489405 434493294696769834683527)
                    ·
                      rfl

theorem cell22_1269259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 3].length) (baseStart_1269259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269259 prefixEnd_1269259 := by exact prefixLift 1269259
  have htrace : WordTrace (prefixWord ++ tailWord_1269259) baseStart_1269259 baseEnd_1269259 := by
    simpa [prefixWord, tailWord_1269259, baseEnd_1269259] using wordTrace_append hprefix tailTrace_1269259
  have hstable : (prefixWord ++ tailWord_1269259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269259).length < 2 ^ (prefixWord ++ tailWord_1269259).sum := by decide
  have hdescent : baseEnd_1269259 < baseStart_1269259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269298 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1269298 : Nat := 118140960795 + 1269298 * 2 ^ 59
def prefixEnd_1269298 : Nat := 4983230072969 + 3 ^ 40 * 1269298 * 2
def baseEnd_1269298 : Nat := 434506645193786732958407

theorem tailTrace_1269298 : CollatzResearch.WordTrace tailWord_1269298 prefixEnd_1269298 434506645193786732958407 := by
  unfold tailWord_1269298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11573775338889399921216137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30863400903705066456576365 11573775338889399921216137)
  ·
    refine ⟨8680331504167049940912103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11573775338889399921216137 8680331504167049940912103)
    ·
      refine ⟨13020497256250574911368155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8680331504167049940912103 13020497256250574911368155)
      ·
        refine ⟨19530745884375862367052233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13020497256250574911368155 19530745884375862367052233)
        ·
          refine ⟨14648059413281896775289175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19530745884375862367052233 14648059413281896775289175)
          ·
            refine ⟨21972089119922845162933763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14648059413281896775289175 21972089119922845162933763)
            ·
              refine ⟨32958133679884267744400645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21972089119922845162933763 32958133679884267744400645)
              ·
                refine ⟨6179650064978300202075121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32958133679884267744400645 6179650064978300202075121)
                ·
                  refine ⟨4634737548733725151556341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6179650064978300202075121 4634737548733725151556341)
                  ·
                    refine ⟨434506645193786732958407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4634737548733725151556341 434506645193786732958407)
                    ·
                      rfl

theorem cell22_1269298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1269298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269298 prefixEnd_1269298 := by exact prefixLift 1269298
  have htrace : WordTrace (prefixWord ++ tailWord_1269298) baseStart_1269298 baseEnd_1269298 := by
    simpa [prefixWord, tailWord_1269298, baseEnd_1269298] using wordTrace_append hprefix tailTrace_1269298
  have hstable : (prefixWord ++ tailWord_1269298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269298).length < 2 ^ (prefixWord ++ tailWord_1269298).sum := by decide
  have hdescent : baseEnd_1269298 < baseStart_1269298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269304 : List Nat := [2, 1, 2, 1, 4, 2, 4, 2, 1, 3]
def baseStart_1269304 : Nat := 118140960795 + 1269304 * 2 ^ 59
def prefixEnd_1269304 : Nat := 4983230072969 + 3 ^ 40 * 1269304 * 2
def baseEnd_1269304 : Nat := 434508699116404717308389

theorem tailTrace_1269304 : CollatzResearch.WordTrace tailWord_1269304 prefixEnd_1269304 434508699116404717308389 := by
  unfold tailWord_1269304
  simp only [CollatzResearch.WordTrace]
  refine ⟨23147660096767931354791483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30863546795690575139721977 23147660096767931354791483)
  ·
    refine ⟨34721490145151897032187225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23147660096767931354791483 34721490145151897032187225)
    ·
      refine ⟨26041117608863922774140419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34721490145151897032187225 26041117608863922774140419)
      ·
        refine ⟨39061676413295884161210629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26041117608863922774140419 39061676413295884161210629)
        ·
          refine ⟨7324064327492978280226993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39061676413295884161210629 7324064327492978280226993)
          ·
            refine ⟨5493048245619733710170245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7324064327492978280226993 5493048245619733710170245)
            ·
              refine ⟨1029946546053700070656921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5493048245619733710170245 1029946546053700070656921)
              ·
                refine ⟨772459909540275052992691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029946546053700070656921 772459909540275052992691)
                ·
                  refine ⟨1158689864310412579489037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772459909540275052992691 1158689864310412579489037)
                  ·
                    refine ⟨434508699116404717308389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158689864310412579489037 434508699116404717308389)
                    ·
                      rfl

theorem cell22_1269304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_1269304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269304 prefixEnd_1269304 := by exact prefixLift 1269304
  have htrace : WordTrace (prefixWord ++ tailWord_1269304) baseStart_1269304 baseEnd_1269304 := by
    simpa [prefixWord, tailWord_1269304, baseEnd_1269304] using wordTrace_append hprefix tailTrace_1269304
  have hstable : (prefixWord ++ tailWord_1269304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269304).length < 2 ^ (prefixWord ++ tailWord_1269304).sum := by decide
  have hdescent : baseEnd_1269304 < baseStart_1269304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269328 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 6]
def baseStart_1269328 : Nat := 118140960795 + 1269328 * 2 ^ 59
def prefixEnd_1269328 : Nat := 4983230072969 + 3 ^ 40 * 1269328 * 2
def baseEnd_1269328 : Nat := 144838971602292218236105

theorem tailTrace_1269328 : CollatzResearch.WordTrace tailWord_1269328 prefixEnd_1269328 144838971602292218236105 := by
  unfold tailWord_1269328
  simp only [CollatzResearch.WordTrace]
  refine ⟨23148097772724457404228319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30864130363632609872304425 23148097772724457404228319)
  ·
    refine ⟨34722146659086686106342479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23148097772724457404228319 34722146659086686106342479)
    ·
      refine ⟨52083219988630029159513719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34722146659086686106342479 52083219988630029159513719)
      ·
        refine ⟨78124829982945043739270579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52083219988630029159513719 78124829982945043739270579)
        ·
          refine ⟨117187244974417565608905869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78124829982945043739270579 117187244974417565608905869)
          ·
            refine ⟨43945216865406587103339701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117187244974417565608905869 43945216865406587103339701)
            ·
              refine ⟨4119864081131867540938097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43945216865406587103339701 4119864081131867540938097)
              ·
                refine ⟨3089898060848900655703573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4119864081131867540938097 3089898060848900655703573)
                ·
                  refine ⟨144838971602292218236105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3089898060848900655703573 144838971602292218236105)
                  ·
                    rfl

theorem cell22_1269328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_1269328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269328 prefixEnd_1269328 := by exact prefixLift 1269328
  have htrace : WordTrace (prefixWord ++ tailWord_1269328) baseStart_1269328 baseEnd_1269328 := by
    simpa [prefixWord, tailWord_1269328, baseEnd_1269328] using wordTrace_append hprefix tailTrace_1269328
  have hstable : (prefixWord ++ tailWord_1269328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269328).length < 2 ^ (prefixWord ++ tailWord_1269328).sum := by decide
  have hdescent : baseEnd_1269328 < baseStart_1269328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269330 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1269330 : Nat := 118140960795 + 1269330 * 2 ^ 59
def prefixEnd_1269330 : Nat := 4983230072969 + 3 ^ 40 * 1269330 * 2
def baseEnd_1269330 : Nat := 434517599447749316158309

theorem tailTrace_1269330 : CollatzResearch.WordTrace tailWord_1269330 prefixEnd_1269330 434517599447749316158309 := by
  unfold tailWord_1269330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11574067122860417287507361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30864178994294446100019629 11574067122860417287507361)
  ·
    refine ⟨8680550342145312965630521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11574067122860417287507361 8680550342145312965630521)
    ·
      refine ⟨6510412756608984724222891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8680550342145312965630521 6510412756608984724222891)
      ·
        refine ⟨9765619134913477086334337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510412756608984724222891 9765619134913477086334337)
        ·
          refine ⟨7324214351185107814750753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9765619134913477086334337 7324214351185107814750753)
          ·
            refine ⟨5493160763388830861063065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7324214351185107814750753 5493160763388830861063065)
            ·
              refine ⟨4119870572541623145797299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5493160763388830861063065 4119870572541623145797299)
              ·
                refine ⟨6179805858812434718695949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119870572541623145797299 6179805858812434718695949)
                ·
                  refine ⟨2317427197054663019510981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6179805858812434718695949 2317427197054663019510981)
                  ·
                    refine ⟨434517599447749316158309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317427197054663019510981 434517599447749316158309)
                    ·
                      rfl

theorem cell22_1269330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1269330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269330 prefixEnd_1269330 := by exact prefixLift 1269330
  have htrace : WordTrace (prefixWord ++ tailWord_1269330) baseStart_1269330 baseEnd_1269330 := by
    simpa [prefixWord, tailWord_1269330, baseEnd_1269330] using wordTrace_append hprefix tailTrace_1269330
  have hstable : (prefixWord ++ tailWord_1269330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269330).length < 2 ^ (prefixWord ++ tailWord_1269330).sum := by decide
  have hdescent : baseEnd_1269330 < baseStart_1269330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269347 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 1, 4]
def baseStart_1269347 : Nat := 118140960795 + 1269347 * 2 ^ 59
def prefixEnd_1269347 : Nat := 4983230072969 + 3 ^ 40 * 1269347 * 2
def baseEnd_1269347 : Nat := 434523418895166938483257

theorem tailTrace_1269347 : CollatzResearch.WordTrace tailWord_1269347 prefixEnd_1269347 434523418895166938483257 := by
  unfold tailWord_1269347
  simp only [CollatzResearch.WordTrace]
  refine ⟨46296888532380081053398295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30864592354920054035598863 46296888532380081053398295)
  ·
    refine ⟨69445332798570121580097443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46296888532380081053398295 69445332798570121580097443)
    ·
      refine ⟨104167999197855182370146165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69445332798570121580097443 104167999197855182370146165)
      ·
        refine ⟨9765749924798923347201203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104167999197855182370146165 9765749924798923347201203)
        ·
          refine ⟨14648624887198385020801805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9765749924798923347201203 14648624887198385020801805)
          ·
            refine ⟨5493234332699394382800677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14648624887198385020801805 5493234332699394382800677)
            ·
              refine ⟨1029981437381136446775127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5493234332699394382800677 1029981437381136446775127)
              ·
                refine ⟨1544972156071704670162691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029981437381136446775127 1544972156071704670162691)
                ·
                  refine ⟨2317458234107557005244037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544972156071704670162691 2317458234107557005244037)
                  ·
                    refine ⟨434523418895166938483257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317458234107557005244037 434523418895166938483257)
                    ·
                      rfl

theorem cell22_1269347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 4].length) (baseStart_1269347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269347 prefixEnd_1269347 := by exact prefixLift 1269347
  have htrace : WordTrace (prefixWord ++ tailWord_1269347) baseStart_1269347 baseEnd_1269347 := by
    simpa [prefixWord, tailWord_1269347, baseEnd_1269347] using wordTrace_append hprefix tailTrace_1269347
  have hstable : (prefixWord ++ tailWord_1269347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269347).length < 2 ^ (prefixWord ++ tailWord_1269347).sum := by decide
  have hdescent : baseEnd_1269347 < baseStart_1269347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269362 : List Nat := [3, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_1269362 : Nat := 118140960795 + 1269362 * 2 ^ 59
def prefixEnd_1269362 : Nat := 4983230072969 + 3 ^ 40 * 1269362 * 2
def baseEnd_1269362 : Nat := 144842851233903966452737

theorem tailTrace_1269362 : CollatzResearch.WordTrace tailWord_1269362 prefixEnd_1269362 144842851233903966452737 := by
  unfold tailWord_1269362
  simp only [CollatzResearch.WordTrace]
  refine ⟨11574358906831434653798585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30864957084883825743462893 11574358906831434653798585)
  ·
    refine ⟨8680769180123575990348939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11574358906831434653798585 8680769180123575990348939)
    ·
      refine ⟨13021153770185363985523409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8680769180123575990348939 13021153770185363985523409)
      ·
        refine ⟨9765865327639022989142557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13021153770185363985523409 9765865327639022989142557)
        ·
          refine ⟨3662199497864633620928459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9765865327639022989142557 3662199497864633620928459)
          ·
            refine ⟨5493299246796950431392689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662199497864633620928459 5493299246796950431392689)
            ·
              refine ⟨4119974435097712823544517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5493299246796950431392689 4119974435097712823544517)
              ·
                refine ⟨772495206580821154414597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4119974435097712823544517 772495206580821154414597)
                ·
                  refine ⟨144842851233903966452737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772495206580821154414597 144842851233903966452737)
                  ·
                    rfl

theorem cell22_1269362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_1269362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269362 prefixEnd_1269362 := by exact prefixLift 1269362
  have htrace : WordTrace (prefixWord ++ tailWord_1269362) baseStart_1269362 baseEnd_1269362 := by
    simpa [prefixWord, tailWord_1269362, baseEnd_1269362] using wordTrace_append hprefix tailTrace_1269362
  have hstable : (prefixWord ++ tailWord_1269362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269362).length < 2 ^ (prefixWord ++ tailWord_1269362).sum := by decide
  have hdescent : baseEnd_1269362 < baseStart_1269362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269377 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 1, 5]
def baseStart_1269377 : Nat := 118140960795 + 1269377 * 2 ^ 59
def prefixEnd_1269377 : Nat := 4983230072969 + 3 ^ 40 * 1269377 * 2
def baseEnd_1269377 : Nat := 434533688508256860233165

theorem tailTrace_1269377 : CollatzResearch.WordTrace tailWord_1269377 prefixEnd_1269377 434533688508256860233165 := by
  unfold tailWord_1269377
  simp only [CollatzResearch.WordTrace]
  refine ⟨46297982722271396176990385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30865321814847597451326923 46297982722271396176990385)
  ·
    refine ⟨34723487041703547132742789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46297982722271396176990385 34723487041703547132742789)
    ·
      refine ⟨6510653820319415087389273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34723487041703547132742789 6510653820319415087389273)
      ·
        refine ⟨4882990365239561315541955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6510653820319415087389273 4882990365239561315541955)
        ·
          refine ⟨7324485547859341973312933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882990365239561315541955 7324485547859341973312933)
          ·
            refine ⟨1373341040223626619996175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7324485547859341973312933 1373341040223626619996175)
            ·
              refine ⟨2060011560335439929994263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373341040223626619996175 2060011560335439929994263)
              ·
                refine ⟨3090017340503159894991395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060011560335439929994263 3090017340503159894991395)
                ·
                  refine ⟨4635026010754739842487093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090017340503159894991395 4635026010754739842487093)
                  ·
                    refine ⟨434533688508256860233165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4635026010754739842487093 434533688508256860233165)
                    ·
                      rfl

theorem cell22_1269377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_1269377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269377 prefixEnd_1269377 := by exact prefixLift 1269377
  have htrace : WordTrace (prefixWord ++ tailWord_1269377) baseStart_1269377 baseEnd_1269377 := by
    simpa [prefixWord, tailWord_1269377, baseEnd_1269377] using wordTrace_append hprefix tailTrace_1269377
  have hstable : (prefixWord ++ tailWord_1269377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269377).length < 2 ^ (prefixWord ++ tailWord_1269377).sum := by decide
  have hdescent : baseEnd_1269377 < baseStart_1269377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269388 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1269388 : Nat := 118140960795 + 1269388 * 2 ^ 59
def prefixEnd_1269388 : Nat := 4983230072969 + 3 ^ 40 * 1269388 * 2
def baseEnd_1269388 : Nat := 434537454033056498208131

theorem tailTrace_1269388 : CollatzResearch.WordTrace tailWord_1269388 prefixEnd_1269388 434537454033056498208131 := by
  unfold tailWord_1269388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23149191962615772527820409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30865589283487696703760545 23149191962615772527820409)
  ·
    refine ⟨17361893971961829395865307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23149191962615772527820409 17361893971961829395865307)
    ·
      refine ⟨26042840957942744093797961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17361893971961829395865307 26042840957942744093797961)
      ·
        refine ⟨19532130718457058070348471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26042840957942744093797961 19532130718457058070348471)
        ·
          refine ⟨29298196077685587105522707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19532130718457058070348471 29298196077685587105522707)
          ·
            refine ⟨43947294116528380658284061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29298196077685587105522707 43947294116528380658284061)
            ·
              refine ⟨16480235293698142746856523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43947294116528380658284061 16480235293698142746856523)
              ·
                refine ⟨24720352940547214120284785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16480235293698142746856523 24720352940547214120284785)
                ·
                  refine ⟨18540264705410410590213589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24720352940547214120284785 18540264705410410590213589)
                  ·
                    refine ⟨434537454033056498208131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18540264705410410590213589 434537454033056498208131)
                    ·
                      rfl

theorem cell22_1269388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1269388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269388 prefixEnd_1269388 := by exact prefixLift 1269388
  have htrace : WordTrace (prefixWord ++ tailWord_1269388) baseStart_1269388 baseEnd_1269388 := by
    simpa [prefixWord, tailWord_1269388, baseEnd_1269388] using wordTrace_append hprefix tailTrace_1269388
  have hstable : (prefixWord ++ tailWord_1269388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269388).length < 2 ^ (prefixWord ++ tailWord_1269388).sum := by decide
  have hdescent : baseEnd_1269388 < baseStart_1269388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269390 : List Nat := [4, 1, 1, 3, 1, 3, 1, 8]
def baseStart_1269390 : Nat := 118140960795 + 1269390 * 2 ^ 59
def prefixEnd_1269390 : Nat := 4983230072969 + 3 ^ 40 * 1269390 * 2
def baseEnd_1269390 : Nat := 48282015408214351073125

theorem tailTrace_1269390 : CollatzResearch.WordTrace tailWord_1269390 prefixEnd_1269390 48282015408214351073125 := by
  unfold tailWord_1269390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787307108903037424651703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30865637914149532931475749 5787307108903037424651703)
  ·
    refine ⟨8680960663354556136977555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5787307108903037424651703 8680960663354556136977555)
    ·
      refine ⟨13021440995031834205466333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8680960663354556136977555 13021440995031834205466333)
      ·
        refine ⟨4883040373136937827049875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13021440995031834205466333 4883040373136937827049875)
        ·
          refine ⟨7324560559705406740574813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883040373136937827049875 7324560559705406740574813)
          ·
            refine ⟨2746710209889527527715555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7324560559705406740574813 2746710209889527527715555)
            ·
              refine ⟨4120065314834291291573333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746710209889527527715555 4120065314834291291573333)
              ·
                refine ⟨48282015408214351073125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4120065314834291291573333 48282015408214351073125)
                ·
                  rfl

theorem cell22_1269390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_1269390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269390 prefixEnd_1269390 := by exact prefixLift 1269390
  have htrace : WordTrace (prefixWord ++ tailWord_1269390) baseStart_1269390 baseEnd_1269390 := by
    simpa [prefixWord, tailWord_1269390, baseEnd_1269390] using wordTrace_append hprefix tailTrace_1269390
  have hstable : (prefixWord ++ tailWord_1269390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269390).length < 2 ^ (prefixWord ++ tailWord_1269390).sum := by decide
  have hdescent : baseEnd_1269390 < baseStart_1269390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269396 : List Nat := [2, 4, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1269396 : Nat := 118140960795 + 1269396 * 2 ^ 59
def prefixEnd_1269396 : Nat := 4983230072969 + 3 ^ 40 * 1269396 * 2
def baseEnd_1269396 : Nat := 144846730865515714669369

theorem tailTrace_1269396 : CollatzResearch.WordTrace tailWord_1269396 prefixEnd_1269396 144846730865515714669369 := by
  unfold tailWord_1269396
  simp only [CollatzResearch.WordTrace]
  refine ⟨23149337854601281210966021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30865783806135041614621361 23149337854601281210966021)
  ·
    refine ⟨4340500847737740227056129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23149337854601281210966021 4340500847737740227056129)
    ·
      refine ⟨3255375635803305170292097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4340500847737740227056129 3255375635803305170292097)
      ·
        refine ⟨2441531726852478877719073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3255375635803305170292097 2441531726852478877719073)
        ·
          refine ⟨1831148795139359158289305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2441531726852478877719073 1831148795139359158289305)
          ·
            refine ⟨1373361596354519368716979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831148795139359158289305 1373361596354519368716979)
            ·
              refine ⟨2060042394531779053075469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373361596354519368716979 2060042394531779053075469)
              ·
                refine ⟨772515897949417144903301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060042394531779053075469 772515897949417144903301)
                ·
                  refine ⟨144846730865515714669369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772515897949417144903301 144846730865515714669369)
                  ·
                    rfl

theorem cell22_1269396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1269396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269396 prefixEnd_1269396 := by exact prefixLift 1269396
  have htrace : WordTrace (prefixWord ++ tailWord_1269396) baseStart_1269396 baseEnd_1269396 := by
    simpa [prefixWord, tailWord_1269396, baseEnd_1269396] using wordTrace_append hprefix tailTrace_1269396
  have hstable : (prefixWord ++ tailWord_1269396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269396).length < 2 ^ (prefixWord ++ tailWord_1269396).sum := by decide
  have hdescent : baseEnd_1269396 < baseStart_1269396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269407 : List Nat := [1, 1, 2, 7, 1, 2, 8]
def baseStart_1269407 : Nat := 118140960795 + 1269407 * 2 ^ 59
def prefixEnd_1269407 : Nat := 4983230072969 + 3 ^ 40 * 1269407 * 2
def baseEnd_1269407 : Nat := 16094220671160991925299

theorem tailTrace_1269407 : CollatzResearch.WordTrace tailWord_1269407 prefixEnd_1269407 16094220671160991925299 := by
  unfold tailWord_1269407
  simp only [CollatzResearch.WordTrace]
  refine ⟨46299076912162711300582475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30866051274775140867054983 46299076912162711300582475)
  ·
    refine ⟨69448615368244066950873713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46299076912162711300582475 69448615368244066950873713)
    ·
      refine ⟨52086461526183050213155285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69448615368244066950873713 52086461526183050213155285)
      ·
        refine ⟨1220776442019915239370827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 52086461526183050213155285 1220776442019915239370827)
        ·
          refine ⟨1831164663029872859056241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220776442019915239370827 1831164663029872859056241)
          ·
            refine ⟨1373373497272404644292181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831164663029872859056241 1373373497272404644292181)
            ·
              refine ⟨16094220671160991925299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1373373497272404644292181 16094220671160991925299)
              ·
                rfl

theorem cell22_1269407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 8].length) (baseStart_1269407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269407 prefixEnd_1269407 := by exact prefixLift 1269407
  have htrace : WordTrace (prefixWord ++ tailWord_1269407) baseStart_1269407 baseEnd_1269407 := by
    simpa [prefixWord, tailWord_1269407, baseEnd_1269407] using wordTrace_append hprefix tailTrace_1269407
  have hstable : (prefixWord ++ tailWord_1269407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269407).length < 2 ^ (prefixWord ++ tailWord_1269407).sum := by decide
  have hdescent : baseEnd_1269407 < baseStart_1269407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269473 : List Nat := [1, 2, 3, 1, 5, 2, 2, 2, 1, 3]
def baseStart_1269473 : Nat := 118140960795 + 1269473 * 2 ^ 59
def prefixEnd_1269473 : Nat := 4983230072969 + 3 ^ 40 * 1269473 * 2
def baseEnd_1269473 : Nat := 434566551270144609832871

theorem tailTrace_1269473 : CollatzResearch.WordTrace tailWord_1269473 prefixEnd_1269473 434566551270144609832871 := by
  unfold tailWord_1269473
  simp only [CollatzResearch.WordTrace]
  refine ⟨46301484129923604572485073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30867656086615736381656715 46301484129923604572485073)
  ·
    refine ⟨34726113097442703429363805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46301484129923604572485073 34726113097442703429363805)
    ·
      refine ⟨13022292411541013786011427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34726113097442703429363805 13022292411541013786011427)
      ·
        refine ⟨19533438617311520679017141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13022292411541013786011427 19533438617311520679017141)
        ·
          refine ⟨1831259870372955063657857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19533438617311520679017141 1831259870372955063657857)
          ·
            refine ⟨1373444902779716297743393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831259870372955063657857 1373444902779716297743393)
            ·
              refine ⟨1030083677084787223307545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373444902779716297743393 1030083677084787223307545)
              ·
                refine ⟨772562757813590417480659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030083677084787223307545 772562757813590417480659)
                ·
                  refine ⟨1158844136720385626220989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772562757813590417480659 1158844136720385626220989)
                  ·
                    refine ⟨434566551270144609832871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158844136720385626220989 434566551270144609832871)
                    ·
                      rfl

theorem cell22_1269473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_1269473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269473 prefixEnd_1269473 := by exact prefixLift 1269473
  have htrace : WordTrace (prefixWord ++ tailWord_1269473) baseStart_1269473 baseEnd_1269473 := by
    simpa [prefixWord, tailWord_1269473, baseEnd_1269473] using wordTrace_append hprefix tailTrace_1269473
  have hstable : (prefixWord ++ tailWord_1269473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269473).length < 2 ^ (prefixWord ++ tailWord_1269473).sum := by decide
  have hdescent : baseEnd_1269473 < baseStart_1269473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269495 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 1, 5]
def baseStart_1269495 : Nat := 118140960795 + 1269495 * 2 ^ 59
def prefixEnd_1269495 : Nat := 4983230072969 + 3 ^ 40 * 1269495 * 2
def baseEnd_1269495 : Nat := 434574082319743885782803

theorem tailTrace_1269495 : CollatzResearch.WordTrace tailWord_1269495 prefixEnd_1269495 434574082319743885782803 := by
  unfold tailWord_1269495
  simp only [CollatzResearch.WordTrace]
  refine ⟨46302286535843902329785939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30868191023895934886523959 46302286535843902329785939)
  ·
    refine ⟨69453429803765853494678909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46302286535843902329785939 69453429803765853494678909)
    ·
      refine ⟨26045036176412195060504591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69453429803765853494678909 26045036176412195060504591)
      ·
        refine ⟨39067554264618292590756887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26045036176412195060504591 39067554264618292590756887)
        ·
          refine ⟨58601331396927438886135331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39067554264618292590756887 58601331396927438886135331)
          ·
            refine ⟨87901997095391158329202997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58601331396927438886135331 87901997095391158329202997)
            ·
              refine ⟨8240812227692921093362781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87901997095391158329202997 8240812227692921093362781)
              ·
                refine ⟨3090304585384845410011043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8240812227692921093362781 3090304585384845410011043)
                ·
                  refine ⟨4635456878077268115016565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090304585384845410011043 4635456878077268115016565)
                  ·
                    refine ⟨434574082319743885782803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4635456878077268115016565 434574082319743885782803)
                    ·
                      rfl

theorem cell22_1269495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_1269495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269495 prefixEnd_1269495 := by exact prefixLift 1269495
  have htrace : WordTrace (prefixWord ++ tailWord_1269495) baseStart_1269495 baseEnd_1269495 := by
    simpa [prefixWord, tailWord_1269495, baseEnd_1269495] using wordTrace_append hprefix tailTrace_1269495
  have hstable : (prefixWord ++ tailWord_1269495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269495).length < 2 ^ (prefixWord ++ tailWord_1269495).sum := by decide
  have hdescent : baseEnd_1269495 < baseStart_1269495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269512 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1269512 : Nat := 118140960795 + 1269512 * 2 ^ 59
def prefixEnd_1269512 : Nat := 4983230072969 + 3 ^ 40 * 1269512 * 2
def baseEnd_1269512 : Nat := 434579901767161508107751

theorem tailTrace_1269512 : CollatzResearch.WordTrace tailWord_1269512 prefixEnd_1269512 434579901767161508107751 := by
  unfold tailWord_1269512
  simp only [CollatzResearch.WordTrace]
  refine ⟨23151453288391157116577395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30868604384521542822103193 23151453288391157116577395)
  ·
    refine ⟨34727179932586735674866093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23151453288391157116577395 34727179932586735674866093)
    ·
      refine ⟨13022692474720025878074785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34727179932586735674866093 13022692474720025878074785)
      ·
        refine ⟨9767019356040019408556089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13022692474720025878074785 9767019356040019408556089)
        ·
          refine ⟨7325264517030014556417067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9767019356040019408556089 7325264517030014556417067)
          ·
            refine ⟨10987896775545021834625601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7325264517030014556417067 10987896775545021834625601)
            ·
              refine ⟨8240922581658766375969201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10987896775545021834625601 8240922581658766375969201)
              ·
                refine ⟨6180691936244074781976901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8240922581658766375969201 6180691936244074781976901)
                ·
                  refine ⟨1158879738045764021620669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6180691936244074781976901 1158879738045764021620669)
                  ·
                    refine ⟨434579901767161508107751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158879738045764021620669 434579901767161508107751)
                    ·
                      rfl

theorem cell22_1269512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1269512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269512 prefixEnd_1269512 := by exact prefixLift 1269512
  have htrace : WordTrace (prefixWord ++ tailWord_1269512) baseStart_1269512 baseEnd_1269512 := by
    simpa [prefixWord, tailWord_1269512, baseEnd_1269512] using wordTrace_append hprefix tailTrace_1269512
  have hstable : (prefixWord ++ tailWord_1269512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269512).length < 2 ^ (prefixWord ++ tailWord_1269512).sum := by decide
  have hdescent : baseEnd_1269512 < baseStart_1269512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269514 : List Nat := [3, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_1269514 : Nat := 118140960795 + 1269514 * 2 ^ 59
def prefixEnd_1269514 : Nat := 4983230072969 + 3 ^ 40 * 1269514 * 2
def baseEnd_1269514 : Nat := 144860195469344723185915

theorem tailTrace_1269514 : CollatzResearch.WordTrace tailWord_1269514 prefixEnd_1269514 144860195469344723185915 := by
  unfold tailWord_1269514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11575744880693767143681899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30868653015183379049818397 11575744880693767143681899)
  ·
    refine ⟨17363617321040650715522849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11575744880693767143681899 17363617321040650715522849)
    ·
      refine ⟨13022712990780488036642137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17363617321040650715522849 13022712990780488036642137)
      ·
        refine ⟨9767034743085366027481603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13022712990780488036642137 9767034743085366027481603)
        ·
          refine ⟨14650552114628049041222405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767034743085366027481603 14650552114628049041222405)
          ·
            refine ⟨2746978521492759195229201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14650552114628049041222405 2746978521492759195229201)
            ·
              refine ⟨2060233891119569396421901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746978521492759195229201 2060233891119569396421901)
              ·
                refine ⟨772587709169838523658213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060233891119569396421901 772587709169838523658213)
                ·
                  refine ⟨144860195469344723185915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772587709169838523658213 144860195469344723185915)
                  ·
                    rfl

theorem cell22_1269514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_1269514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269514 prefixEnd_1269514 := by exact prefixLift 1269514
  have htrace : WordTrace (prefixWord ++ tailWord_1269514) baseStart_1269514 baseEnd_1269514 := by
    simpa [prefixWord, tailWord_1269514, baseEnd_1269514] using wordTrace_append hprefix tailTrace_1269514
  have hstable : (prefixWord ++ tailWord_1269514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269514).length < 2 ^ (prefixWord ++ tailWord_1269514).sum := by decide
  have hdescent : baseEnd_1269514 < baseStart_1269514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269525 : List Nat := [1, 3, 2, 1, 2, 4, 9]
def baseStart_1269525 : Nat := 118140960795 + 1269525 * 2 ^ 59
def prefixEnd_1269525 : Nat := 4983230072969 + 3 ^ 40 * 1269525 * 2
def baseEnd_1269525 : Nat := 16095716738253103982693

theorem tailTrace_1269525 : CollatzResearch.WordTrace tailWord_1269525 prefixEnd_1269525 16095716738253103982693 := by
  unfold tailWord_1269525
  simp only [CollatzResearch.WordTrace]
  refine ⟨46303380725735217453378029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30868920483823478302252019 46303380725735217453378029)
  ·
    refine ⟨17363767772150706545016761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46303380725735217453378029 17363767772150706545016761)
    ·
      refine ⟨13022825829113029908762571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17363767772150706545016761 13022825829113029908762571)
      ·
        refine ⟨19534238743669544863143857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13022825829113029908762571 19534238743669544863143857)
        ·
          refine ⟨14650679057752158647357893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19534238743669544863143857 14650679057752158647357893)
          ·
            refine ⟨2747002323328529746379605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14650679057752158647357893 2747002323328529746379605)
            ·
              refine ⟨16095716738253103982693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2747002323328529746379605 16095716738253103982693)
              ·
                rfl

theorem cell22_1269525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 9].length) (baseStart_1269525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269525 prefixEnd_1269525 := by exact prefixLift 1269525
  have htrace : WordTrace (prefixWord ++ tailWord_1269525) baseStart_1269525 baseEnd_1269525 := by
    simpa [prefixWord, tailWord_1269525, baseEnd_1269525] using wordTrace_append hprefix tailTrace_1269525
  have hstable : (prefixWord ++ tailWord_1269525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269525).length < 2 ^ (prefixWord ++ tailWord_1269525).sum := by decide
  have hdescent : baseEnd_1269525 < baseStart_1269525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269591 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 3, 3]
def baseStart_1269591 : Nat := 118140960795 + 1269591 * 2 ^ 59
def prefixEnd_1269591 : Nat := 4983230072969 + 3 ^ 40 * 1269591 * 2
def baseEnd_1269591 : Nat := 434606945081631635382509

theorem tailTrace_1269591 : CollatzResearch.WordTrace tailWord_1269591 prefixEnd_1269591 434606945081631635382509 := by
  unfold tailWord_1269591
  simp only [CollatzResearch.WordTrace]
  refine ⟨46305787943496110725280627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30870525295664073816853751 46305787943496110725280627)
  ·
    refine ⟨69458681915244166087920941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46305787943496110725280627 69458681915244166087920941)
    ·
      refine ⟨26047005718216562282970353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69458681915244166087920941 26047005718216562282970353)
      ·
        refine ⟨19535254288662421712227765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26047005718216562282970353 19535254288662421712227765)
        ·
          refine ⟨1831430089562102035521353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19535254288662421712227765 1831430089562102035521353)
          ·
            refine ⟨1373572567171576526641015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831430089562102035521353 1373572567171576526641015)
            ·
              refine ⟨2060358850757364789961523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373572567171576526641015 2060358850757364789961523)
              ·
                refine ⟨3090538276136047184942285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060358850757364789961523 3090538276136047184942285)
                ·
                  refine ⟨1158951853551017694353357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3090538276136047184942285 1158951853551017694353357)
                  ·
                    refine ⟨434606945081631635382509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158951853551017694353357 434606945081631635382509)
                    ·
                      rfl

theorem cell22_1269591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_1269591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269591 prefixEnd_1269591 := by exact prefixLift 1269591
  have htrace : WordTrace (prefixWord ++ tailWord_1269591) baseStart_1269591 baseEnd_1269591 := by
    simpa [prefixWord, tailWord_1269591, baseEnd_1269591] using wordTrace_append hprefix tailTrace_1269591
  have hstable : (prefixWord ++ tailWord_1269591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269591).length < 2 ^ (prefixWord ++ tailWord_1269591).sum := by decide
  have hdescent : baseEnd_1269591 < baseStart_1269591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269604 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1269604 : Nat := 118140960795 + 1269604 * 2 ^ 59
def prefixEnd_1269604 : Nat := 4983230072969 + 3 ^ 40 * 1269604 * 2
def baseEnd_1269604 : Nat := 144870465082434644935823

theorem tailTrace_1269604 : CollatzResearch.WordTrace tailWord_1269604 prefixEnd_1269604 144870465082434644935823 := by
  unfold tailWord_1269604
  simp only [CollatzResearch.WordTrace]
  refine ⟨23153131046224506972751933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30870841394966009297002577 23153131046224506972751933)
  ·
    refine ⟨8682424142334190114781975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23153131046224506972751933 8682424142334190114781975)
    ·
      refine ⟨13023636213501285172172963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8682424142334190114781975 13023636213501285172172963)
      ·
        refine ⟨19535454320251927758259445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13023636213501285172172963 19535454320251927758259445)
        ·
          refine ⟨1831448842523618227336823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19535454320251927758259445 1831448842523618227336823)
          ·
            refine ⟨2747173263785427341005235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831448842523618227336823 2747173263785427341005235)
            ·
              refine ⟨4120759895678141011507853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747173263785427341005235 4120759895678141011507853)
              ·
                refine ⟨1545284960879302879315445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4120759895678141011507853 1545284960879302879315445)
                ·
                  refine ⟨144870465082434644935823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1545284960879302879315445 144870465082434644935823)
                  ·
                    rfl

theorem cell22_1269604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1269604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269604 prefixEnd_1269604 := by exact prefixLift 1269604
  have htrace : WordTrace (prefixWord ++ tailWord_1269604) baseStart_1269604 baseEnd_1269604 := by
    simpa [prefixWord, tailWord_1269604, baseEnd_1269604] using wordTrace_append hprefix tailTrace_1269604
  have hstable : (prefixWord ++ tailWord_1269604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269604).length < 2 ^ (prefixWord ++ tailWord_1269604).sum := by decide
  have hdescent : baseEnd_1269604 < baseStart_1269604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269617 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_1269617 : Nat := 118140960795 + 1269617 * 2 ^ 59
def prefixEnd_1269617 : Nat := 4983230072969 + 3 ^ 40 * 1269617 * 2
def baseEnd_1269617 : Nat := 434615845412976234232429

theorem tailTrace_1269617 : CollatzResearch.WordTrace tailWord_1269617 prefixEnd_1269617 434615845412976234232429 := by
  unfold tailWord_1269617
  simp only [CollatzResearch.WordTrace]
  refine ⟨46306736241401917165727105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30871157494267944777151403 46306736241401917165727105)
  ·
    refine ⟨34730052181051437874295329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46306736241401917165727105 34730052181051437874295329)
    ·
      refine ⟨26047539135788578405721497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34730052181051437874295329 26047539135788578405721497)
      ·
        refine ⟨19535654351841433804291123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26047539135788578405721497 19535654351841433804291123)
        ·
          refine ⟨29303481527762150706436685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19535654351841433804291123 29303481527762150706436685)
          ·
            refine ⟨10988805572910806514913757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29303481527762150706436685 10988805572910806514913757)
            ·
              refine ⟨4120802089841552443092659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10988805572910806514913757 4120802089841552443092659)
              ·
                refine ⟨6181203134762328664638989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120802089841552443092659 6181203134762328664638989)
                ·
                  refine ⟨2317951175535873249239621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6181203134762328664638989 2317951175535873249239621)
                  ·
                    refine ⟨434615845412976234232429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317951175535873249239621 434615845412976234232429)
                    ·
                      rfl

theorem cell22_1269617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_1269617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269617 prefixEnd_1269617 := by exact prefixLift 1269617
  have htrace : WordTrace (prefixWord ++ tailWord_1269617) baseStart_1269617 baseEnd_1269617 := by
    simpa [prefixWord, tailWord_1269617, baseEnd_1269617] using wordTrace_append hprefix tailTrace_1269617
  have hstable : (prefixWord ++ tailWord_1269617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269617).length < 2 ^ (prefixWord ++ tailWord_1269617).sum := by decide
  have hdescent : baseEnd_1269617 < baseStart_1269617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269642 : List Nat := [3, 1, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_1269642 : Nat := 118140960795 + 1269642 * 2 ^ 59
def prefixEnd_1269642 : Nat := 4983230072969 + 3 ^ 40 * 1269642 * 2
def baseEnd_1269642 : Nat := 434624403423884502357353

theorem tailTrace_1269642 : CollatzResearch.WordTrace tailWord_1269642 prefixEnd_1269642 434624403423884502357353 := by
  unfold tailWord_1269642
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576912016577836608846795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30871765377540897623591453 11576912016577836608846795)
  ·
    refine ⟨17365368024866754913270193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11576912016577836608846795 17365368024866754913270193)
    ·
      refine ⟨13024026018650066184952645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17365368024866754913270193 13024026018650066184952645)
      ·
        refine ⟨2442004878496887409678621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13024026018650066184952645 2442004878496887409678621)
        ·
          refine ⟨915751829436332778629483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2442004878496887409678621 915751829436332778629483)
          ·
            refine ⟨1373627744154499167944225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915751829436332778629483 1373627744154499167944225)
            ·
              refine ⟨1030220808115874375958169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373627744154499167944225 1030220808115874375958169)
              ·
                refine ⟨772665606086905781968627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030220808115874375958169 772665606086905781968627)
                ·
                  refine ⟨1158998409130358672952941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772665606086905781968627 1158998409130358672952941)
                  ·
                    refine ⟨434624403423884502357353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158998409130358672952941 434624403423884502357353)
                    ·
                      rfl

theorem cell22_1269642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_1269642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269642 prefixEnd_1269642 := by exact prefixLift 1269642
  have htrace : WordTrace (prefixWord ++ tailWord_1269642) baseStart_1269642 baseEnd_1269642 := by
    simpa [prefixWord, tailWord_1269642, baseEnd_1269642] using wordTrace_append hprefix tailTrace_1269642
  have hstable : (prefixWord ++ tailWord_1269642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269642).length < 2 ^ (prefixWord ++ tailWord_1269642).sum := by decide
  have hdescent : baseEnd_1269642 < baseStart_1269642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269647 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 10, 3]
def baseStart_1269647 : Nat := 118140960795 + 1269647 * 2 ^ 59
def prefixEnd_1269647 : Nat := 4983230072969 + 3 ^ 40 * 1269647 * 2
def baseEnd_1269647 : Nat := 434626115026066155982337

theorem tailTrace_1269647 : CollatzResearch.WordTrace tailWord_1269647 prefixEnd_1269647 434626115026066155982337 := by
  unfold tailWord_1269647
  simp only [CollatzResearch.WordTrace]
  refine ⟨46307830431293232289319195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30871886954195488192879463 46307830431293232289319195)
  ·
    refine ⟨69461745646939848433978793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46307830431293232289319195 69461745646939848433978793)
    ·
      refine ⟨52096309235204886325484095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69461745646939848433978793 52096309235204886325484095)
      ·
        refine ⟨78144463852807329488226143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52096309235204886325484095 78144463852807329488226143)
        ·
          refine ⟨117216695779210994232339215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78144463852807329488226143 117216695779210994232339215)
          ·
            refine ⟨175825043668816491348508823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117216695779210994232339215 175825043668816491348508823)
            ·
              refine ⟨263737565503224737022763235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175825043668816491348508823 263737565503224737022763235)
              ·
                refine ⟨395606348254837105534144853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263737565503224737022763235 395606348254837105534144853)
                ·
                  refine ⟨1159002973402843082619565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 395606348254837105534144853 1159002973402843082619565)
                  ·
                    refine ⟨434626115026066155982337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159002973402843082619565 434626115026066155982337)
                    ·
                      rfl

theorem cell22_1269647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_1269647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269647 prefixEnd_1269647 := by exact prefixLift 1269647
  have htrace : WordTrace (prefixWord ++ tailWord_1269647) baseStart_1269647 baseEnd_1269647 := by
    simpa [prefixWord, tailWord_1269647, baseEnd_1269647] using wordTrace_append hprefix tailTrace_1269647
  have hstable : (prefixWord ++ tailWord_1269647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269647).length < 2 ^ (prefixWord ++ tailWord_1269647).sum := by decide
  have hdescent : baseEnd_1269647 < baseStart_1269647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269766 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1269766 : Nat := 118140960795 + 1269766 * 2 ^ 59
def prefixEnd_1269766 : Nat := 4983230072969 + 3 ^ 40 * 1269766 * 2
def baseEnd_1269766 : Nat := 434666851157989512256973

theorem tailTrace_1269766 : CollatzResearch.WordTrace tailWord_1269766 prefixEnd_1269766 434666851157989512256973 := by
  unfold tailWord_1269766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447255334933191112903161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30874780478574743741934101 1447255334933191112903161)
  ·
    refine ⟨1085441501199893334677371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1447255334933191112903161 1085441501199893334677371)
    ·
      refine ⟨1628162251799840002016057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085441501199893334677371 1628162251799840002016057)
      ·
        refine ⟨1221121688849880001512043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1628162251799840002016057 1221121688849880001512043)
        ·
          refine ⟨1831682533274820002268065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221121688849880001512043 1831682533274820002268065)
          ·
            refine ⟨1373761899956115001701049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831682533274820002268065 1373761899956115001701049)
            ·
              refine ⟨1030321424967086251275787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373761899956115001701049 1030321424967086251275787)
              ·
                refine ⟨1545482137450629376913681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030321424967086251275787 1545482137450629376913681)
                ·
                  refine ⟨1159111603087972032685261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1545482137450629376913681 1159111603087972032685261)
                  ·
                    refine ⟨434666851157989512256973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159111603087972032685261 434666851157989512256973)
                    ·
                      rfl

theorem cell22_1269766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1269766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269766 prefixEnd_1269766 := by exact prefixLift 1269766
  have htrace : WordTrace (prefixWord ++ tailWord_1269766) baseStart_1269766 baseEnd_1269766 := by
    simpa [prefixWord, tailWord_1269766, baseEnd_1269766] using wordTrace_append hprefix tailTrace_1269766
  have hstable : (prefixWord ++ tailWord_1269766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269766).length < 2 ^ (prefixWord ++ tailWord_1269766).sum := by decide
  have hdescent : baseEnd_1269766 < baseStart_1269766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269786 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_1269786 : Nat := 118140960795 + 1269786 * 2 ^ 59
def prefixEnd_1269786 : Nat := 4983230072969 + 3 ^ 40 * 1269786 * 2
def baseEnd_1269786 : Nat := 434673697566716126756911

theorem tailTrace_1269786 : CollatzResearch.WordTrace tailWord_1269786 prefixEnd_1269786 434673697566716126756911 := by
  unfold tailWord_1269786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11578225044447414757157303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30875266785193106019086141 11578225044447414757157303)
  ·
    refine ⟨17367337566671122135735955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11578225044447414757157303 17367337566671122135735955)
    ·
      refine ⟨26051006350006683203603933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17367337566671122135735955 26051006350006683203603933)
      ·
        refine ⟨9769127381252506201351475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26051006350006683203603933 9769127381252506201351475)
        ·
          refine ⟨14653691071878759302027213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9769127381252506201351475 14653691071878759302027213)
          ·
            refine ⟨5495134151954534738260205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14653691071878759302027213 5495134151954534738260205)
            ·
              refine ⟨2060675306982950526847577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5495134151954534738260205 2060675306982950526847577)
              ·
                refine ⟨1545506480237212895135683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060675306982950526847577 1545506480237212895135683)
                ·
                  refine ⟨2318259720355819342703525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545506480237212895135683 2318259720355819342703525)
                  ·
                    refine ⟨434673697566716126756911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318259720355819342703525 434673697566716126756911)
                    ·
                      rfl

theorem cell22_1269786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_1269786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269786 prefixEnd_1269786 := by exact prefixLift 1269786
  have htrace : WordTrace (prefixWord ++ tailWord_1269786) baseStart_1269786 baseEnd_1269786 := by
    simpa [prefixWord, tailWord_1269786, baseEnd_1269786] using wordTrace_append hprefix tailTrace_1269786
  have hstable : (prefixWord ++ tailWord_1269786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269786).length < 2 ^ (prefixWord ++ tailWord_1269786).sum := by decide
  have hdescent : baseEnd_1269786 < baseStart_1269786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269854 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1269854 : Nat := 118140960795 + 1269854 * 2 ^ 59
def prefixEnd_1269854 : Nat := 4983230072969 + 3 ^ 40 * 1269854 * 2
def baseEnd_1269854 : Nat := 434696975356386616056703

theorem tailTrace_1269854 : CollatzResearch.WordTrace tailWord_1269854 prefixEnd_1269854 434696975356386616056703 := by
  unfold tailWord_1269854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789422542692913330263077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30876920227695537761403077 5789422542692913330263077)
  ·
    refine ⟨1085516726754921249424327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5789422542692913330263077 1085516726754921249424327)
    ·
      refine ⟨1628275090132381874136491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085516726754921249424327 1628275090132381874136491)
      ·
        refine ⟨2442412635198572811204737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628275090132381874136491 2442412635198572811204737)
        ·
          refine ⟨1831809476398929608403553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2442412635198572811204737 1831809476398929608403553)
          ·
            refine ⟨1373857107299197206302665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831809476398929608403553 1373857107299197206302665)
            ·
              refine ⟨1030392830474397904726999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373857107299197206302665 1030392830474397904726999)
              ·
                refine ⟨1545589245711596857090499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030392830474397904726999 1545589245711596857090499)
                ·
                  refine ⟨2318383868567395285635749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545589245711596857090499 2318383868567395285635749)
                  ·
                    refine ⟨434696975356386616056703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318383868567395285635749 434696975356386616056703)
                    ·
                      rfl

theorem cell22_1269854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1269854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269854 prefixEnd_1269854 := by exact prefixLift 1269854
  have htrace : WordTrace (prefixWord ++ tailWord_1269854) baseStart_1269854 baseEnd_1269854 := by
    simpa [prefixWord, tailWord_1269854, baseEnd_1269854] using wordTrace_append hprefix tailTrace_1269854
  have hstable : (prefixWord ++ tailWord_1269854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269854).length < 2 ^ (prefixWord ++ tailWord_1269854).sum := by decide
  have hdescent : baseEnd_1269854 < baseStart_1269854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269878 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1269878 : Nat := 118140960795 + 1269878 * 2 ^ 59
def prefixEnd_1269878 : Nat := 4983230072969 + 3 ^ 40 * 1269878 * 2
def baseEnd_1269878 : Nat := 434705191046858553456629

theorem tailTrace_1269878 : CollatzResearch.WordTrace tailWord_1269878 prefixEnd_1269878 434705191046858553456629 := by
  unfold tailWord_1269878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894765980841022421311143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30877503795637572493985525 2894765980841022421311143)
  ·
    refine ⟨4342148971261533631966715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2894765980841022421311143 4342148971261533631966715)
    ·
      refine ⟨6513223456892300447950073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4342148971261533631966715 6513223456892300447950073)
      ·
        refine ⟨4884917592669225335962555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6513223456892300447950073 4884917592669225335962555)
        ·
          refine ⟨7327376389003838003943833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4884917592669225335962555 7327376389003838003943833)
          ·
            refine ⟨5495532291752878502957875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7327376389003838003943833 5495532291752878502957875)
            ·
              refine ⟨8243298437629317754436813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495532291752878502957875 8243298437629317754436813)
              ·
                refine ⟨3091236914110994157913805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8243298437629317754436813 3091236914110994157913805)
                ·
                  refine ⟨1159213842791622809217677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3091236914110994157913805 1159213842791622809217677)
                  ·
                    refine ⟨434705191046858553456629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159213842791622809217677 434705191046858553456629)
                    ·
                      rfl

theorem cell22_1269878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1269878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269878 prefixEnd_1269878 := by exact prefixLift 1269878
  have htrace : WordTrace (prefixWord ++ tailWord_1269878) baseStart_1269878 baseEnd_1269878 := by
    simpa [prefixWord, tailWord_1269878, baseEnd_1269878] using wordTrace_append hprefix tailTrace_1269878
  have hstable : (prefixWord ++ tailWord_1269878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269878).length < 2 ^ (prefixWord ++ tailWord_1269878).sum := by decide
  have hdescent : baseEnd_1269878 < baseStart_1269878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269912 : List Nat := [2, 1, 2, 4, 3, 2, 1, 3, 1, 3]
def baseStart_1269912 : Nat := 118140960795 + 1269912 * 2 ^ 59
def prefixEnd_1269912 : Nat := 4983230072969 + 3 ^ 40 * 1269912 * 2
def baseEnd_1269912 : Nat := 434716829941693798106525

theorem tailTrace_1269912 : CollatzResearch.WordTrace tailWord_1269912 prefixEnd_1269912 434716829941693798106525 := by
  unfold tailWord_1269912
  simp only [CollatzResearch.WordTrace]
  refine ⟨23158747887666591273857995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30878330516888788365143993 23158747887666591273857995)
  ·
    refine ⟨34738121831499886910786993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23158747887666591273857995 34738121831499886910786993)
    ·
      refine ⟨26053591373624915183090245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34738121831499886910786993 26053591373624915183090245)
      ·
        refine ⟨4885048382554671596829421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26053591373624915183090245 4885048382554671596829421)
        ·
          refine ⟨1831893143458001848811033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4885048382554671596829421 1831893143458001848811033)
          ·
            refine ⟨1373919857593501386608275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831893143458001848811033 1373919857593501386608275)
            ·
              refine ⟨2060879786390252079912413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373919857593501386608275 2060879786390252079912413)
              ·
                refine ⟨772829919896344529967155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060879786390252079912413 772829919896344529967155)
                ·
                  refine ⟨1159244879844516794950733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772829919896344529967155 1159244879844516794950733)
                  ·
                    refine ⟨434716829941693798106525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159244879844516794950733 434716829941693798106525)
                    ·
                      rfl

theorem cell22_1269912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_1269912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269912 prefixEnd_1269912 := by exact prefixLift 1269912
  have htrace : WordTrace (prefixWord ++ tailWord_1269912) baseStart_1269912 baseEnd_1269912 := by
    simpa [prefixWord, tailWord_1269912, baseEnd_1269912] using wordTrace_append hprefix tailTrace_1269912
  have hstable : (prefixWord ++ tailWord_1269912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269912).length < 2 ^ (prefixWord ++ tailWord_1269912).sum := by decide
  have hdescent : baseEnd_1269912 < baseStart_1269912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269981 : List Nat := [1, 4, 3, 2, 1, 11]
def baseStart_1269981 : Nat := 118140960795 + 1269981 * 2 ^ 59
def prefixEnd_1269981 : Nat := 4983230072969 + 3 ^ 40 * 1269981 * 2
def baseEnd_1269981 : Nat := 5367166050022229853473

theorem tailTrace_1269981 : CollatzResearch.WordTrace tailWord_1269981 prefixEnd_1269981 5367166050022229853473 := by
  unfold tailWord_1269981
  simp only [CollatzResearch.WordTrace]
  refine ⟨46320012412083207331977797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30880008274722138221318531 46320012412083207331977797)
  ·
    refine ⟨8685002327265601374745837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46320012412083207331977797 8685002327265601374745837)
    ·
      refine ⟨3256875872724600515529689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8685002327265601374745837 3256875872724600515529689)
      ·
        refine ⟨2442656904543450386647267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3256875872724600515529689 2442656904543450386647267)
        ·
          refine ⟨3663985356815175579970901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442656904543450386647267 3663985356815175579970901)
          ·
            refine ⟨5367166050022229853473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3663985356815175579970901 5367166050022229853473)
            ·
              rfl

theorem cell22_1269981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 11].length) (baseStart_1269981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1269981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1269981 prefixEnd_1269981 := by exact prefixLift 1269981
  have htrace : WordTrace (prefixWord ++ tailWord_1269981) baseStart_1269981 baseEnd_1269981 := by
    simpa [prefixWord, tailWord_1269981, baseEnd_1269981] using wordTrace_append hprefix tailTrace_1269981
  have hstable : (prefixWord ++ tailWord_1269981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269981).length < 2 ^ (prefixWord ++ tailWord_1269981).sum := by decide
  have hdescent : baseEnd_1269981 < baseStart_1269981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270081 : List Nat := [1, 2, 5, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1270081 : Nat := 118140960795 + 1270081 * 2 ^ 59
def prefixEnd_1270081 : Nat := 4983230072969 + 3 ^ 40 * 1270081 * 2
def baseEnd_1270081 : Nat := 434774682095433690631007

theorem tailTrace_1270081 : CollatzResearch.WordTrace tailWord_1270081 prefixEnd_1270081 434774682095433690631007 := by
  unfold tailWord_1270081
  simp only [CollatzResearch.WordTrace]
  refine ⟨46323659711720924410618097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30882439807813949607078731 46323659711720924410618097)
  ·
    refine ⟨34742744783790693307963573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46323659711720924410618097 34742744783790693307963573)
    ·
      refine ⟨3257132323480377497621585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34742744783790693307963573 3257132323480377497621585)
      ·
        refine ⟨2442849242610283123216189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3257132323480377497621585 2442849242610283123216189)
        ·
          refine ⟨916068465978856171206071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2442849242610283123216189 916068465978856171206071)
          ·
            refine ⟨1374102698968284256809107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916068465978856171206071 1374102698968284256809107)
            ·
              refine ⟨2061154048452426385213661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374102698968284256809107 2061154048452426385213661)
              ·
                refine ⟨772932768169659894455123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2061154048452426385213661 772932768169659894455123)
                ·
                  refine ⟨1159399152254489841682685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772932768169659894455123 1159399152254489841682685)
                  ·
                    refine ⟨434774682095433690631007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159399152254489841682685 434774682095433690631007)
                    ·
                      rfl

theorem cell22_1270081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1270081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270081 prefixEnd_1270081 := by exact prefixLift 1270081
  have htrace : WordTrace (prefixWord ++ tailWord_1270081) baseStart_1270081 baseEnd_1270081 := by
    simpa [prefixWord, tailWord_1270081, baseEnd_1270081] using wordTrace_append hprefix tailTrace_1270081
  have hstable : (prefixWord ++ tailWord_1270081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270081).length < 2 ^ (prefixWord ++ tailWord_1270081).sum := by decide
  have hdescent : baseEnd_1270081 < baseStart_1270081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270103 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 4, 3]
def baseStart_1270103 : Nat := 118140960795 + 1270103 * 2 ^ 59
def prefixEnd_1270103 : Nat := 4983230072969 + 3 ^ 40 * 1270103 * 2
def baseEnd_1270103 : Nat := 434782213145032966580939

theorem tailTrace_1270103 : CollatzResearch.WordTrace tailWord_1270103 prefixEnd_1270103 434782213145032966580939 := by
  unfold tailWord_1270103
  simp only [CollatzResearch.WordTrace]
  refine ⟨46324462117641222167918963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30882974745094148111945975 46324462117641222167918963)
  ·
    refine ⟨69486693176461833251878445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46324462117641222167918963 69486693176461833251878445)
    ·
      refine ⟨26057509941173187469454417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69486693176461833251878445 26057509941173187469454417)
      ·
        refine ⟨19543132455879890602090813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26057509941173187469454417 19543132455879890602090813)
        ·
          refine ⟨7328674670954958975784055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19543132455879890602090813 7328674670954958975784055)
          ·
            refine ⟨10993012006432438463676083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7328674670954958975784055 10993012006432438463676083)
            ·
              refine ⟨16489518009648657695514125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10993012006432438463676083 16489518009648657695514125)
              ·
                refine ⟨6183569253618246635817797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16489518009648657695514125 6183569253618246635817797)
                ·
                  refine ⟨1159419235053421244215837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6183569253618246635817797 1159419235053421244215837)
                  ·
                    refine ⟨434782213145032966580939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159419235053421244215837 434782213145032966580939)
                    ·
                      rfl

theorem cell22_1270103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_1270103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270103 prefixEnd_1270103 := by exact prefixLift 1270103
  have htrace : WordTrace (prefixWord ++ tailWord_1270103) baseStart_1270103 baseEnd_1270103 := by
    simpa [prefixWord, tailWord_1270103, baseEnd_1270103] using wordTrace_append hprefix tailTrace_1270103
  have hstable : (prefixWord ++ tailWord_1270103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270103).length < 2 ^ (prefixWord ++ tailWord_1270103).sum := by decide
  have hdescent : baseEnd_1270103 < baseStart_1270103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270133 : List Nat := [1, 3, 4, 1, 2, 1, 2, 8]
def baseStart_1270133 : Nat := 118140960795 + 1270133 * 2 ^ 59
def prefixEnd_1270133 : Nat := 4983230072969 + 3 ^ 40 * 1270133 * 2
def baseEnd_1270133 : Nat := 48310275862013654258983

theorem tailTrace_1270133 : CollatzResearch.WordTrace tailWord_1270133 prefixEnd_1270133 48310275862013654258983 := by
  unfold tailWord_1270133
  simp only [CollatzResearch.WordTrace]
  refine ⟨46325556307532537291511053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30883704205021691527674035 46325556307532537291511053)
  ·
    refine ⟨17372083615324701484316645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46325556307532537291511053 17372083615324701484316645)
    ·
      refine ⟨3257265677873381528309371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17372083615324701484316645 3257265677873381528309371)
      ·
        refine ⟨4885898516810072292464057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257265677873381528309371 4885898516810072292464057)
        ·
          refine ⟨3664423887607554219348043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885898516810072292464057 3664423887607554219348043)
          ·
            refine ⟨5496635831411331329022065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664423887607554219348043 5496635831411331329022065)
            ·
              refine ⟨4122476873558498496766549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496635831411331329022065 4122476873558498496766549)
              ·
                refine ⟨48310275862013654258983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4122476873558498496766549 48310275862013654258983)
                ·
                  rfl

theorem cell22_1270133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 8].length) (baseStart_1270133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270133 prefixEnd_1270133 := by exact prefixLift 1270133
  have htrace : WordTrace (prefixWord ++ tailWord_1270133) baseStart_1270133 baseEnd_1270133 := by
    simpa [prefixWord, tailWord_1270133, baseEnd_1270133] using wordTrace_append hprefix tailTrace_1270133
  have hstable : (prefixWord ++ tailWord_1270133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270133).length < 2 ^ (prefixWord ++ tailWord_1270133).sum := by decide
  have hdescent : baseEnd_1270133 < baseStart_1270133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270154 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_1270154 : Nat := 118140960795 + 1270154 * 2 ^ 59
def prefixEnd_1270154 : Nat := 4983230072969 + 3 ^ 40 * 1270154 * 2
def baseEnd_1270154 : Nat := 434799671487285833555783

theorem tailTrace_1270154 : CollatzResearch.WordTrace tailWord_1270154 prefixEnd_1270154 434799671487285833555783 := by
  unfold tailWord_1270154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11581580560114114469506379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30884214826970971918683677 11581580560114114469506379)
  ·
    refine ⟨17372370840171171704259569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11581580560114114469506379 17372370840171171704259569)
    ·
      refine ⟨13029278130128378778194677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17372370840171171704259569 13029278130128378778194677)
      ·
        refine ⟨1221494824699535510455751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13029278130128378778194677 1221494824699535510455751)
        ·
          refine ⟨1832242237049303265683627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221494824699535510455751 1832242237049303265683627)
          ·
            refine ⟨2748363355573954898525441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832242237049303265683627 2748363355573954898525441)
            ·
              refine ⟨2061272516680466173894081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748363355573954898525441 2061272516680466173894081)
              ·
                refine ⟨1545954387510349630420561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061272516680466173894081 1545954387510349630420561)
                ·
                  refine ⟨1159465790632762222815421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1545954387510349630420561 1159465790632762222815421)
                  ·
                    refine ⟨434799671487285833555783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159465790632762222815421 434799671487285833555783)
                    ·
                      rfl

theorem cell22_1270154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_1270154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270154 prefixEnd_1270154 := by exact prefixLift 1270154
  have htrace : WordTrace (prefixWord ++ tailWord_1270154) baseStart_1270154 baseEnd_1270154 := by
    simpa [prefixWord, tailWord_1270154, baseEnd_1270154] using wordTrace_append hprefix tailTrace_1270154
  have hstable : (prefixWord ++ tailWord_1270154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270154).length < 2 ^ (prefixWord ++ tailWord_1270154).sum := by decide
  have hdescent : baseEnd_1270154 < baseStart_1270154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
