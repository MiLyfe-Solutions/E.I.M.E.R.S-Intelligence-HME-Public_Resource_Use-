import V185TrunkScan20Chunk014

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_90325 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 3]
def baseStart_90325 : Nat := 118140960795 + 90325 * 2 ^ 59
def prefixEnd_90325 : Nat := 4983230072969 + 3 ^ 40 * 90325 * 2
def baseEnd_90325 : Nat := 41226791215523854864097

theorem tailTrace_90325 : CollatzResearch.WordTrace tailWord_90325 prefixEnd_90325 41226791215523854864097 := by
  unfold tailWord_90325
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294423397775426126960429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2196282265183617417973619 3294423397775426126960429)
  ·
    refine ⟨1235408774165784797610161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3294423397775426126960429 1235408774165784797610161)
    ·
      refine ⟨926556580624338598207621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235408774165784797610161 926556580624338598207621)
      ·
        refine ⟨173729358867063487163929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 926556580624338598207621 173729358867063487163929)
        ·
          refine ⟨130297019150297615372947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173729358867063487163929 130297019150297615372947)
          ·
            refine ⟨195445528725446423059421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130297019150297615372947 195445528725446423059421)
            ·
              refine ⟨73292073272042408647283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195445528725446423059421 73292073272042408647283)
              ·
                refine ⟨109938109908063612970925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73292073272042408647283 109938109908063612970925)
                ·
                  refine ⟨41226791215523854864097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109938109908063612970925 41226791215523854864097)
                  ·
                    rfl

theorem cell20_90325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_90325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90325 prefixEnd_90325 := by exact prefixLift 90325
  have htrace : WordTrace (prefixWord ++ tailWord_90325) baseStart_90325 baseEnd_90325 := by
    simpa [prefixWord, tailWord_90325, baseEnd_90325] using wordTrace_append hprefix tailTrace_90325
  have hstable : (prefixWord ++ tailWord_90325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90325).length < 2 ^ (prefixWord ++ tailWord_90325).sum := by decide
  have hdescent : baseEnd_90325 < baseStart_90325 := by decide
  rcases family_descends (prefixWord ++ tailWord_90325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90349 : List Nat := [1, 5, 1, 2, 3, 2, 1, 3, 2]
def baseStart_90349 : Nat := 118140960795 + 90349 * 2 ^ 59
def prefixEnd_90349 : Nat := 4983230072969 + 3 ^ 40 * 90349 * 2
def baseEnd_90349 : Nat := 41237745469486438063999

theorem tailTrace_90349 : CollatzResearch.WordTrace tailWord_90349 prefixEnd_90349 41237745469486438063999 := by
  unfold tailWord_90349
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295298749688478225834101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2196865833125652150556067 3295298749688478225834101)
  ·
    refine ⟨308934257783294833671947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3295298749688478225834101 308934257783294833671947)
    ·
      refine ⟨463401386674942250507921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308934257783294833671947 463401386674942250507921)
      ·
        refine ⟨347551040006206687880941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463401386674942250507921 347551040006206687880941)
        ·
          refine ⟨130331640002327507955353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347551040006206687880941 130331640002327507955353)
          ·
            refine ⟨97748730001745630966515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130331640002327507955353 97748730001745630966515)
            ·
              refine ⟨146623095002618446449773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97748730001745630966515 146623095002618446449773)
              ·
                refine ⟨54983660625981917418665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146623095002618446449773 54983660625981917418665)
                ·
                  refine ⟨41237745469486438063999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54983660625981917418665 41237745469486438063999)
                  ·
                    rfl

theorem cell20_90349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_90349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90349 prefixEnd_90349 := by exact prefixLift 90349
  have htrace : WordTrace (prefixWord ++ tailWord_90349) baseStart_90349 baseEnd_90349 := by
    simpa [prefixWord, tailWord_90349, baseEnd_90349] using wordTrace_append hprefix tailTrace_90349
  have hstable : (prefixWord ++ tailWord_90349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90349).length < 2 ^ (prefixWord ++ tailWord_90349).sum := by decide
  have hdescent : baseEnd_90349 < baseStart_90349 := by decide
  rcases family_descends (prefixWord ++ tailWord_90349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90353 : List Nat := [1, 2, 2, 2, 2, 1, 5, 3, 2]
def baseStart_90353 : Nat := 118140960795 + 90353 * 2 ^ 59
def prefixEnd_90353 : Nat := 4983230072969 + 3 ^ 40 * 90353 * 2
def baseEnd_90353 : Nat := 41239571178480201930649

theorem tailTrace_90353 : CollatzResearch.WordTrace tailWord_90353 prefixEnd_90353 41239571178480201930649 := by
  unfold tailWord_90353
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295444641673986908979713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2196963094449324605986475 3295444641673986908979713)
  ·
    refine ⟨2471583481255490181734785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3295444641673986908979713 2471583481255490181734785)
    ·
      refine ⟨1853687610941617636301089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2471583481255490181734785 1853687610941617636301089)
      ·
        refine ⟨1390265708206213227225817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1853687610941617636301089 1390265708206213227225817)
        ·
          refine ⟨1042699281154659920419363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390265708206213227225817 1042699281154659920419363)
          ·
            refine ⟨1564048921731989880629045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042699281154659920419363 1564048921731989880629045)
            ·
              refine ⟨146629586412374051308973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1564048921731989880629045 146629586412374051308973)
              ·
                refine ⟨54986094904640269240865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146629586412374051308973 54986094904640269240865)
                ·
                  refine ⟨41239571178480201930649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54986094904640269240865 41239571178480201930649)
                  ·
                    rfl

theorem cell20_90353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_90353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90353 prefixEnd_90353 := by exact prefixLift 90353
  have htrace : WordTrace (prefixWord ++ tailWord_90353) baseStart_90353 baseEnd_90353 := by
    simpa [prefixWord, tailWord_90353, baseEnd_90353] using wordTrace_append hprefix tailTrace_90353
  have hstable : (prefixWord ++ tailWord_90353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90353).length < 2 ^ (prefixWord ++ tailWord_90353).sum := by decide
  have hdescent : baseEnd_90353 < baseStart_90353 := by decide
  rcases family_descends (prefixWord ++ tailWord_90353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90370 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_90370 : Nat := 118140960795 + 90370 * 2 ^ 59
def prefixEnd_90370 : Nat := 4983230072969 + 3 ^ 40 * 90370 * 2
def baseEnd_90370 : Nat := 41247330441703698363913

theorem tailTrace_90370 : CollatzResearch.WordTrace tailWord_90370 prefixEnd_90370 41247330441703698363913 := by
  unfold tailWord_90370
  simp only [CollatzResearch.WordTrace]
  refine ⟨824016170653099703087141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2197376455074932541565709 824016170653099703087141)
  ·
    refine ⟨154503031997456194328839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 824016170653099703087141 154503031997456194328839)
    ·
      refine ⟨231754547996184291493259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154503031997456194328839 231754547996184291493259)
      ·
        refine ⟨347631821994276437239889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231754547996184291493259 347631821994276437239889)
        ·
          refine ⟨260723866495707327929917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347631821994276437239889 260723866495707327929917)
          ·
            refine ⟨97771449935890247973719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260723866495707327929917 97771449935890247973719)
            ·
              refine ⟨146657174903835371960579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97771449935890247973719 146657174903835371960579)
              ·
                refine ⟨219985762355753057940869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146657174903835371960579 219985762355753057940869)
                ·
                  refine ⟨41247330441703698363913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219985762355753057940869 41247330441703698363913)
                  ·
                    rfl

theorem cell20_90370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_90370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90370 prefixEnd_90370 := by exact prefixLift 90370
  have htrace : WordTrace (prefixWord ++ tailWord_90370) baseStart_90370 baseEnd_90370 := by
    simpa [prefixWord, tailWord_90370, baseEnd_90370] using wordTrace_append hprefix tailTrace_90370
  have hstable : (prefixWord ++ tailWord_90370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90370).length < 2 ^ (prefixWord ++ tailWord_90370).sum := by decide
  have hdescent : baseEnd_90370 < baseStart_90370 := by decide
  rcases family_descends (prefixWord ++ tailWord_90370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90395 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_90395 : Nat := 118140960795 + 90395 * 2 ^ 59
def prefixEnd_90395 : Nat := 4983230072969 + 3 ^ 40 * 90395 * 2
def baseEnd_90395 : Nat := 41258741122914722530477

theorem tailTrace_90395 : CollatzResearch.WordTrace tailWord_90395 prefixEnd_90395 41258741122914722530477 := by
  unfold tailWord_90395
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296976507521828082008639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2197984338347885388005759 3296976507521828082008639)
  ·
    refine ⟨4945464761282742123012959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3296976507521828082008639 4945464761282742123012959)
    ·
      refine ⟨7418197141924113184519439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4945464761282742123012959 7418197141924113184519439)
      ·
        refine ⟨11127295712886169776779159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7418197141924113184519439 11127295712886169776779159)
        ·
          refine ⟨16690943569329254665168739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11127295712886169776779159 16690943569329254665168739)
          ·
            refine ⟨25036415353993881997753109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16690943569329254665168739 25036415353993881997753109)
            ·
              refine ⟨1173581969718463218644677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25036415353993881997753109 1173581969718463218644677)
              ·
                refine ⟨220046619322211853495877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1173581969718463218644677 220046619322211853495877)
                ·
                  refine ⟨41258741122914722530477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220046619322211853495877 41258741122914722530477)
                  ·
                    rfl

theorem cell20_90395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_90395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90395 prefixEnd_90395 := by exact prefixLift 90395
  have htrace : WordTrace (prefixWord ++ tailWord_90395) baseStart_90395 baseEnd_90395 := by
    simpa [prefixWord, tailWord_90395, baseEnd_90395] using wordTrace_append hprefix tailTrace_90395
  have hstable : (prefixWord ++ tailWord_90395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90395).length < 2 ^ (prefixWord ++ tailWord_90395).sum := by decide
  have hdescent : baseEnd_90395 < baseStart_90395 := by decide
  rcases family_descends (prefixWord ++ tailWord_90395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90425 : List Nat := [1, 2, 1, 6, 1, 3, 2, 2, 2]
def baseStart_90425 : Nat := 118140960795 + 90425 * 2 ^ 59
def prefixEnd_90425 : Nat := 4983230072969 + 3 ^ 40 * 90425 * 2
def baseEnd_90425 : Nat := 41272433940367951530355

theorem tailTrace_90425 : CollatzResearch.WordTrace tailWord_90425 prefixEnd_90425 41272433940367951530355 := by
  unfold tailWord_90425
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298070697413143205600729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2198713798275428803733819 3298070697413143205600729)
  ·
    refine ⟨2473553023059857404200547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3298070697413143205600729 2473553023059857404200547)
    ·
      refine ⟨3710329534589786106300821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2473553023059857404200547 3710329534589786106300821)
      ·
        refine ⟨173921696933896223732851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3710329534589786106300821 173921696933896223732851)
        ·
          refine ⟨260882545400844335599277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173921696933896223732851 260882545400844335599277)
          ·
            refine ⟨97830954525316625849729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260882545400844335599277 97830954525316625849729)
            ·
              refine ⟨73373215893987469387297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97830954525316625849729 73373215893987469387297)
              ·
                refine ⟨55029911920490602040473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73373215893987469387297 55029911920490602040473)
                ·
                  refine ⟨41272433940367951530355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55029911920490602040473 41272433940367951530355)
                  ·
                    rfl

theorem cell20_90425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_90425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90425 prefixEnd_90425 := by exact prefixLift 90425
  have htrace : WordTrace (prefixWord ++ tailWord_90425) baseStart_90425 baseEnd_90425 := by
    simpa [prefixWord, tailWord_90425, baseEnd_90425] using wordTrace_append hprefix tailTrace_90425
  have hstable : (prefixWord ++ tailWord_90425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90425).length < 2 ^ (prefixWord ++ tailWord_90425).sum := by decide
  have hdescent : baseEnd_90425 < baseStart_90425 := by decide
  rcases family_descends (prefixWord ++ tailWord_90425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90467 : List Nat := [1, 1, 1, 5, 2, 1, 4, 3, 2]
def baseStart_90467 : Nat := 118140960795 + 90467 * 2 ^ 59
def prefixEnd_90467 : Nat := 4983230072969 + 3 ^ 40 * 90467 * 2
def baseEnd_90467 : Nat := 41291603884802472130183

theorem tailTrace_90467 : CollatzResearch.WordTrace tailWord_90467 prefixEnd_90467 41291603884802472130183 := by
  unfold tailWord_90467
  simp only [CollatzResearch.WordTrace]
  refine ⟨3299602563260984378629655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2199735042173989585753103 3299602563260984378629655)
  ·
    refine ⟨4949403844891476567944483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3299602563260984378629655 4949403844891476567944483)
    ·
      refine ⟨7424105767337214851916725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4949403844891476567944483 7424105767337214851916725)
      ·
        refine ⟨696009915687863892367193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7424105767337214851916725 696009915687863892367193)
        ·
          refine ⟨522007436765897919275395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696009915687863892367193 522007436765897919275395)
          ·
            refine ⟨783011155148846878913093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522007436765897919275395 783011155148846878913093)
            ·
              refine ⟨146814591590408789796205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 783011155148846878913093 146814591590408789796205)
              ·
                refine ⟨55055471846403296173577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146814591590408789796205 55055471846403296173577)
                ·
                  refine ⟨41291603884802472130183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55055471846403296173577 41291603884802472130183)
                  ·
                    rfl

theorem cell20_90467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 2].length) (baseStart_90467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90467 prefixEnd_90467 := by exact prefixLift 90467
  have htrace : WordTrace (prefixWord ++ tailWord_90467) baseStart_90467 baseEnd_90467 := by
    simpa [prefixWord, tailWord_90467, baseEnd_90467] using wordTrace_append hprefix tailTrace_90467
  have hstable : (prefixWord ++ tailWord_90467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90467).length < 2 ^ (prefixWord ++ tailWord_90467).sum := by decide
  have hdescent : baseEnd_90467 < baseStart_90467 := by decide
  rcases family_descends (prefixWord ++ tailWord_90467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90522 : List Nat := [3, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_90522 : Nat := 118140960795 + 90522 * 2 ^ 59
def prefixEnd_90522 : Nat := 4983230072969 + 3 ^ 40 * 90522 * 2
def baseEnd_90522 : Nat := 41316707383466725296625

theorem tailTrace_90522 : CollatzResearch.WordTrace tailWord_90522 prefixEnd_90522 41316707383466725296625 := by
  unfold tailWord_90522
  simp only [CollatzResearch.WordTrace]
  refine ⟨825402144515432192970455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2201072385374485847921213 825402144515432192970455)
  ·
    refine ⟨1238103216773148289455683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 825402144515432192970455 1238103216773148289455683)
    ·
      refine ⟨1857154825159722434183525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238103216773148289455683 1857154825159722434183525)
      ·
        refine ⟨348216529717447956409411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1857154825159722434183525 348216529717447956409411)
        ·
          refine ⟨522324794576171934614117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348216529717447956409411 522324794576171934614117)
          ·
            refine ⟨97935898983032237740147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 522324794576171934614117 97935898983032237740147)
            ·
              refine ⟨146903848474548356610221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97935898983032237740147 146903848474548356610221)
              ·
                refine ⟨55088943177955633728833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146903848474548356610221 55088943177955633728833)
                ·
                  refine ⟨41316707383466725296625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55088943177955633728833 41316707383466725296625)
                  ·
                    rfl

theorem cell20_90522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_90522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90522 prefixEnd_90522 := by exact prefixLift 90522
  have htrace : WordTrace (prefixWord ++ tailWord_90522) baseStart_90522 baseEnd_90522 := by
    simpa [prefixWord, tailWord_90522, baseEnd_90522] using wordTrace_append hprefix tailTrace_90522
  have hstable : (prefixWord ++ tailWord_90522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90522).length < 2 ^ (prefixWord ++ tailWord_90522).sum := by decide
  have hdescent : baseEnd_90522 < baseStart_90522 := by decide
  rcases family_descends (prefixWord ++ tailWord_90522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90529 : List Nat := [1, 2, 3, 5, 2, 1, 6]
def baseStart_90529 : Nat := 118140960795 + 90529 * 2 ^ 59
def prefixEnd_90529 : Nat := 4983230072969 + 3 ^ 40 * 90529 * 2
def baseEnd_90529 : Nat := 4591100263800645784807

theorem tailTrace_90529 : CollatzResearch.WordTrace tailWord_90529 prefixEnd_90529 4591100263800645784807 := by
  unfold tailWord_90529
  simp only [CollatzResearch.WordTrace]
  refine ⟨3301863889036368967386641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2201242592690912644924427 3301863889036368967386641)
  ·
    refine ⟨2476397916777276725539981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3301863889036368967386641 2476397916777276725539981)
    ·
      refine ⟨928649218791478772077493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2476397916777276725539981 928649218791478772077493)
      ·
        refine ⟨87060864261701134882265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 928649218791478772077493 87060864261701134882265)
        ·
          refine ⟨65295648196275851161699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87060864261701134882265 65295648196275851161699)
          ·
            refine ⟨97943472294413776742549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65295648196275851161699 97943472294413776742549)
            ·
              refine ⟨4591100263800645784807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97943472294413776742549 4591100263800645784807)
              ·
                rfl

theorem cell20_90529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 6].length) (baseStart_90529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90529 prefixEnd_90529 := by exact prefixLift 90529
  have htrace : WordTrace (prefixWord ++ tailWord_90529) baseStart_90529 baseEnd_90529 := by
    simpa [prefixWord, tailWord_90529, baseEnd_90529] using wordTrace_append hprefix tailTrace_90529
  have hstable : (prefixWord ++ tailWord_90529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90529).length < 2 ^ (prefixWord ++ tailWord_90529).sum := by decide
  have hdescent : baseEnd_90529 < baseStart_90529 := by decide
  rcases family_descends (prefixWord ++ tailWord_90529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90540 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_90540 : Nat := 118140960795 + 90540 * 2 ^ 59
def prefixEnd_90540 : Nat := 4983230072969 + 3 ^ 40 * 90540 * 2
def baseEnd_90540 : Nat := 41324923073938662696551

theorem tailTrace_90540 : CollatzResearch.WordTrace tailWord_90540 prefixEnd_90540 41324923073938662696551 := by
  unfold tailWord_90540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651132545998258923018537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2201510061331011897358049 1651132545998258923018537)
  ·
    refine ⟨1238349409498694192263903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1651132545998258923018537 1238349409498694192263903)
    ·
      refine ⟨1857524114248041288395855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238349409498694192263903 1857524114248041288395855)
      ·
        refine ⟨2786286171372061932593783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857524114248041288395855 2786286171372061932593783)
        ·
          refine ⟨4179429257058092898890675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786286171372061932593783 4179429257058092898890675)
          ·
            refine ⟨6269143885587139348336013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179429257058092898890675 6269143885587139348336013)
            ·
              refine ⟨2350928957095177255626005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6269143885587139348336013 2350928957095177255626005)
              ·
                refine ⟨110199794863836433857469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2350928957095177255626005 110199794863836433857469)
                ·
                  refine ⟨41324923073938662696551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110199794863836433857469 41324923073938662696551)
                  ·
                    rfl

theorem cell20_90540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_90540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90540 prefixEnd_90540 := by exact prefixLift 90540
  have htrace : WordTrace (prefixWord ++ tailWord_90540) baseStart_90540 baseEnd_90540 := by
    simpa [prefixWord, tailWord_90540, baseEnd_90540] using wordTrace_append hprefix tailTrace_90540
  have hstable : (prefixWord ++ tailWord_90540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90540).length < 2 ^ (prefixWord ++ tailWord_90540).sum := by decide
  have hdescent : baseEnd_90540 < baseStart_90540 := by decide
  rcases family_descends (prefixWord ++ tailWord_90540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90557 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 3]
def baseStart_90557 : Nat := 118140960795 + 90557 * 2 ^ 59
def prefixEnd_90557 : Nat := 4983230072969 + 3 ^ 40 * 90557 * 2
def baseEnd_90557 : Nat := 41332682337162159129815

theorem tailTrace_90557 : CollatzResearch.WordTrace tailWord_90557 prefixEnd_90557 41332682337162159129815 := by
  unfold tailWord_90557
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302885132934929749405925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2201923421956619832937283 3302885132934929749405925)
  ·
    refine ⟨619290962425299328013611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3302885132934929749405925 619290962425299328013611)
    ·
      refine ⟨928936443637948992020417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619290962425299328013611 928936443637948992020417)
      ·
        refine ⟨696702332728461744015313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928936443637948992020417 696702332728461744015313)
        ·
          refine ⟨522526749546346308011485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696702332728461744015313 522526749546346308011485)
          ·
            refine ⟨195947531079879865504307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522526749546346308011485 195947531079879865504307)
            ·
              refine ⟨293921296619819798256461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195947531079879865504307 293921296619819798256461)
              ·
                refine ⟨110220486232432424346173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293921296619819798256461 110220486232432424346173)
                ·
                  refine ⟨41332682337162159129815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110220486232432424346173 41332682337162159129815)
                  ·
                    rfl

theorem cell20_90557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_90557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90557 prefixEnd_90557 := by exact prefixLift 90557
  have htrace : WordTrace (prefixWord ++ tailWord_90557) baseStart_90557 baseEnd_90557 := by
    simpa [prefixWord, tailWord_90557, baseEnd_90557] using wordTrace_append hprefix tailTrace_90557
  have hstable : (prefixWord ++ tailWord_90557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90557).length < 2 ^ (prefixWord ++ tailWord_90557).sum := by decide
  have hdescent : baseEnd_90557 < baseStart_90557 := by decide
  rcases family_descends (prefixWord ++ tailWord_90557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90616 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_90616 : Nat := 118140960795 + 90616 * 2 ^ 59
def prefixEnd_90616 : Nat := 4983230072969 + 3 ^ 40 * 90616 * 2
def baseEnd_90616 : Nat := 41359611544820176162907

theorem tailTrace_90616 : CollatzResearch.WordTrace tailWord_90616 prefixEnd_90616 41359611544820176162907 := by
  unfold tailWord_90616
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652518519860591412901851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2203358026480788550535801 1652518519860591412901851)
  ·
    refine ⟨2478777779790887119352777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652518519860591412901851 2478777779790887119352777)
    ·
      refine ⟨1859083334843165339514583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2478777779790887119352777 1859083334843165339514583)
      ·
        refine ⟨2788625002264748009271875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859083334843165339514583 2788625002264748009271875)
        ·
          refine ⟨4182937503397122013907813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788625002264748009271875 4182937503397122013907813)
          ·
            refine ⟨784300781886960377607715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4182937503397122013907813 784300781886960377607715)
            ·
              refine ⟨1176451172830440566411573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784300781886960377607715 1176451172830440566411573)
              ·
                refine ⟨110292297452853803101085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1176451172830440566411573 110292297452853803101085)
                ·
                  refine ⟨41359611544820176162907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110292297452853803101085 41359611544820176162907)
                  ·
                    rfl

theorem cell20_90616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_90616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90616 prefixEnd_90616 := by exact prefixLift 90616
  have htrace : WordTrace (prefixWord ++ tailWord_90616) baseStart_90616 baseEnd_90616 := by
    simpa [prefixWord, tailWord_90616, baseEnd_90616] using wordTrace_append hprefix tailTrace_90616
  have hstable : (prefixWord ++ tailWord_90616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90616).length < 2 ^ (prefixWord ++ tailWord_90616).sum := by decide
  have hdescent : baseEnd_90616 < baseStart_90616 := by decide
  rcases family_descends (prefixWord ++ tailWord_90616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90623 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_90623 : Nat := 118140960795 + 90623 * 2 ^ 59
def prefixEnd_90623 : Nat := 4983230072969 + 3 ^ 40 * 90623 * 2
def baseEnd_90623 : Nat := 41362806535559262929545

theorem tailTrace_90623 : CollatzResearch.WordTrace tailWord_90623 prefixEnd_90623 41362806535559262929545 := by
  unfold tailWord_90623
  simp only [CollatzResearch.WordTrace]
  refine ⟨3305292350695823021308523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2203528233797215347539015 3305292350695823021308523)
  ·
    refine ⟨4957938526043734531962785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3305292350695823021308523 4957938526043734531962785)
    ·
      refine ⟨3718453894532800898972089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4957938526043734531962785 3718453894532800898972089)
      ·
        refine ⟨2788840420899600674229067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3718453894532800898972089 2788840420899600674229067)
        ·
          refine ⟨4183260631349401011343601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788840420899600674229067 4183260631349401011343601)
          ·
            refine ⟨3137445473512050758507701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4183260631349401011343601 3137445473512050758507701)
            ·
              refine ⟨294135513141754758610097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3137445473512050758507701 294135513141754758610097)
              ·
                refine ⟨220601634856316068957573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294135513141754758610097 220601634856316068957573)
                ·
                  refine ⟨41362806535559262929545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220601634856316068957573 41362806535559262929545)
                  ·
                    rfl

theorem cell20_90623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_90623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90623 prefixEnd_90623 := by exact prefixLift 90623
  have htrace : WordTrace (prefixWord ++ tailWord_90623) baseStart_90623 baseEnd_90623 := by
    simpa [prefixWord, tailWord_90623, baseEnd_90623] using wordTrace_append hprefix tailTrace_90623
  have hstable : (prefixWord ++ tailWord_90623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90623).length < 2 ^ (prefixWord ++ tailWord_90623).sum := by decide
  have hdescent : baseEnd_90623 < baseStart_90623 := by decide
  rcases family_descends (prefixWord ++ tailWord_90623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90661 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_90661 : Nat := 118140960795 + 90661 * 2 ^ 59
def prefixEnd_90661 : Nat := 4983230072969 + 3 ^ 40 * 90661 * 2
def baseEnd_90661 : Nat := 41380150771000019662723

theorem tailTrace_90661 : CollatzResearch.WordTrace tailWord_90661 prefixEnd_90661 41380150771000019662723 := by
  unfold tailWord_90661
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306678324558155511191837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2204452216372103674127891 3306678324558155511191837)
  ·
    refine ⟨1240004371709308316696939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3306678324558155511191837 1240004371709308316696939)
    ·
      refine ⟨1860006557563962475045409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1240004371709308316696939 1860006557563962475045409)
      ·
        refine ⟨1395004918172971856284057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860006557563962475045409 1395004918172971856284057)
        ·
          refine ⟨1046253688629728892213043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395004918172971856284057 1046253688629728892213043)
          ·
            refine ⟨1569380532944593338319565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046253688629728892213043 1569380532944593338319565)
            ·
              refine ⟨588517699854222501869837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569380532944593338319565 588517699854222501869837)
              ·
                refine ⟨220694137445333438201189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588517699854222501869837 220694137445333438201189)
                ·
                  refine ⟨41380150771000019662723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220694137445333438201189 41380150771000019662723)
                  ·
                    rfl

theorem cell20_90661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_90661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90661 prefixEnd_90661 := by exact prefixLift 90661
  have htrace : WordTrace (prefixWord ++ tailWord_90661) baseStart_90661 baseEnd_90661 := by
    simpa [prefixWord, tailWord_90661, baseEnd_90661] using wordTrace_append hprefix tailTrace_90661
  have hstable : (prefixWord ++ tailWord_90661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90661).length < 2 ^ (prefixWord ++ tailWord_90661).sum := by decide
  have hdescent : baseEnd_90661 < baseStart_90661 := by decide
  rcases family_descends (prefixWord ++ tailWord_90661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90685 : List Nat := [1, 4, 1, 3, 2, 2, 1, 6]
def baseStart_90685 : Nat := 118140960795 + 90685 * 2 ^ 59
def prefixEnd_90685 : Nat := 4983230072969 + 3 ^ 40 * 90685 * 2
def baseEnd_90685 : Nat := 13797035008320867620875

theorem tailTrace_90685 : CollatzResearch.WordTrace tailWord_90685 prefixEnd_90685 13797035008320867620875 := by
  unfold tailWord_90685
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307553676471207610065509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2205035784314138406710339 3307553676471207610065509)
  ·
    refine ⟨620166314338351426887283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3307553676471207610065509 620166314338351426887283)
    ·
      refine ⟨930249471507527140330925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620166314338351426887283 930249471507527140330925)
      ·
        refine ⟨348843551815322677624097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 930249471507527140330925 348843551815322677624097)
        ·
          refine ⟨261632663861492008218073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348843551815322677624097 261632663861492008218073)
          ·
            refine ⟨196224497896119006163555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261632663861492008218073 196224497896119006163555)
            ·
              refine ⟨294336746844178509245333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196224497896119006163555 294336746844178509245333)
              ·
                refine ⟨13797035008320867620875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 294336746844178509245333 13797035008320867620875)
                ·
                  rfl

theorem cell20_90685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_90685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90685 prefixEnd_90685 := by exact prefixLift 90685
  have htrace : WordTrace (prefixWord ++ tailWord_90685) baseStart_90685 baseEnd_90685 := by
    simpa [prefixWord, tailWord_90685, baseEnd_90685] using wordTrace_append hprefix tailTrace_90685
  have hstable : (prefixWord ++ tailWord_90685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90685).length < 2 ^ (prefixWord ++ tailWord_90685).sum := by decide
  have hdescent : baseEnd_90685 < baseStart_90685 := by decide
  rcases family_descends (prefixWord ++ tailWord_90685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90695 : List Nat := [1, 1, 4, 1, 4, 1, 3, 3, 2]
def baseStart_90695 : Nat := 118140960795 + 90695 * 2 ^ 59
def prefixEnd_90695 : Nat := 4983230072969 + 3 ^ 40 * 90695 * 2
def baseEnd_90695 : Nat := 41395669297447012529251

theorem tailTrace_90695 : CollatzResearch.WordTrace tailWord_90695 prefixEnd_90695 41395669297447012529251 := by
  unfold tailWord_90695
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307918406434979317929539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2205278937623319545286359 3307918406434979317929539)
  ·
    refine ⟨4961877609652468976894309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307918406434979317929539 4961877609652468976894309)
    ·
      refine ⟨930352051809837933167683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4961877609652468976894309 930352051809837933167683)
      ·
        refine ⟨1395528077714756899751525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930352051809837933167683 1395528077714756899751525)
        ·
          refine ⟨261661514571516918703411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1395528077714756899751525 261661514571516918703411)
          ·
            refine ⟨392492271857275378055117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261661514571516918703411 392492271857275378055117)
            ·
              refine ⟨147184601946478266770669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392492271857275378055117 147184601946478266770669)
              ·
                refine ⟨55194225729929350039001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147184601946478266770669 55194225729929350039001)
                ·
                  refine ⟨41395669297447012529251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55194225729929350039001 41395669297447012529251)
                  ·
                    rfl

theorem cell20_90695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 2].length) (baseStart_90695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90695 prefixEnd_90695 := by exact prefixLift 90695
  have htrace : WordTrace (prefixWord ++ tailWord_90695) baseStart_90695 baseEnd_90695 := by
    simpa [prefixWord, tailWord_90695, baseEnd_90695] using wordTrace_append hprefix tailTrace_90695
  have hstable : (prefixWord ++ tailWord_90695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90695).length < 2 ^ (prefixWord ++ tailWord_90695).sum := by decide
  have hdescent : baseEnd_90695 < baseStart_90695 := by decide
  rcases family_descends (prefixWord ++ tailWord_90695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90718 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_90718 : Nat := 118140960795 + 90718 * 2 ^ 59
def prefixEnd_90718 : Nat := 4983230072969 + 3 ^ 40 * 90718 * 2
def baseEnd_90718 : Nat := 41406167124161154762491

theorem tailTrace_90718 : CollatzResearch.WordTrace tailWord_90718 prefixEnd_90718 41406167124161154762491 := by
  unfold tailWord_90718
  simp only [CollatzResearch.WordTrace]
  refine ⟨413594660668956780752101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2205838190234436164011205 413594660668956780752101)
  ·
    refine ⟨77548998875429396391019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 413594660668956780752101 77548998875429396391019)
    ·
      refine ⟨116323498313144094586529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77548998875429396391019 116323498313144094586529)
      ·
        refine ⟨87242623734858070939897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116323498313144094586529 87242623734858070939897)
        ·
          refine ⟨65431967801143553204923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87242623734858070939897 65431967801143553204923)
          ·
            refine ⟨98147951701715329807385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65431967801143553204923 98147951701715329807385)
            ·
              refine ⟨73610963776286497355539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98147951701715329807385 73610963776286497355539)
              ·
                refine ⟨110416445664429746033309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73610963776286497355539 110416445664429746033309)
                ·
                  refine ⟨41406167124161154762491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110416445664429746033309 41406167124161154762491)
                  ·
                    rfl

theorem cell20_90718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_90718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90718 prefixEnd_90718 := by exact prefixLift 90718
  have htrace : WordTrace (prefixWord ++ tailWord_90718) baseStart_90718 baseEnd_90718 := by
    simpa [prefixWord, tailWord_90718, baseEnd_90718] using wordTrace_append hprefix tailTrace_90718
  have hstable : (prefixWord ++ tailWord_90718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90718).length < 2 ^ (prefixWord ++ tailWord_90718).sum := by decide
  have hdescent : baseEnd_90718 < baseStart_90718 := by decide
  rcases family_descends (prefixWord ++ tailWord_90718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90722 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_90722 : Nat := 118140960795 + 90722 * 2 ^ 59
def prefixEnd_90722 : Nat := 4983230072969 + 3 ^ 40 * 90722 * 2
def baseEnd_90722 : Nat := 41407992833154918629141

theorem tailTrace_90722 : CollatzResearch.WordTrace tailWord_90722 prefixEnd_90722 41407992833154918629141 := by
  unfold tailWord_90722
  simp only [CollatzResearch.WordTrace]
  refine ⟨827225794334290732290605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2205935451558108619441613 827225794334290732290605)
  ·
    refine ⟨310209672875359024608977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 827225794334290732290605 310209672875359024608977)
    ·
      refine ⟨232657254656519268456733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310209672875359024608977 232657254656519268456733)
      ·
        refine ⟨87246470496194725671275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232657254656519268456733 87246470496194725671275)
        ·
          refine ⟨130869705744292088506913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87246470496194725671275 130869705744292088506913)
          ·
            refine ⟨98152279308219066380185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130869705744292088506913 98152279308219066380185)
            ·
              refine ⟨73614209481164299785139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98152279308219066380185 73614209481164299785139)
              ·
                refine ⟨110421314221746449677709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73614209481164299785139 110421314221746449677709)
                ·
                  refine ⟨41407992833154918629141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110421314221746449677709 41407992833154918629141)
                  ·
                    rfl

theorem cell20_90722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_90722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90722 prefixEnd_90722 := by exact prefixLift 90722
  have htrace : WordTrace (prefixWord ++ tailWord_90722) baseStart_90722 baseEnd_90722 := by
    simpa [prefixWord, tailWord_90722, baseEnd_90722] using wordTrace_append hprefix tailTrace_90722
  have hstable : (prefixWord ++ tailWord_90722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90722).length < 2 ^ (prefixWord ++ tailWord_90722).sum := by decide
  have hdescent : baseEnd_90722 < baseStart_90722 := by decide
  rcases family_descends (prefixWord ++ tailWord_90722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90751 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_90751 : Nat := 118140960795 + 90751 * 2 ^ 59
def prefixEnd_90751 : Nat := 4983230072969 + 3 ^ 40 * 90751 * 2
def baseEnd_90751 : Nat := 41421229223359706662355

theorem tailTrace_90751 : CollatzResearch.WordTrace tailWord_90751 prefixEnd_90751 41421229223359706662355 := by
  unfold tailWord_90751
  simp only [CollatzResearch.WordTrace]
  refine ⟨3309960894232100881968107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2206640596154733921312071 3309960894232100881968107)
  ·
    refine ⟨4964941341348151322952161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3309960894232100881968107 4964941341348151322952161)
    ·
      refine ⟨3723706006011113492214121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4964941341348151322952161 3723706006011113492214121)
      ·
        refine ⟨2792779504508335119160591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3723706006011113492214121 2792779504508335119160591)
        ·
          refine ⟨4189169256762502678740887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2792779504508335119160591 4189169256762502678740887)
          ·
            refine ⟨6283753885143754018111331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189169256762502678740887 6283753885143754018111331)
            ·
              refine ⟨9425630827715631027166997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6283753885143754018111331 9425630827715631027166997)
              ·
                refine ⟨441826445049170204398453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9425630827715631027166997 441826445049170204398453)
                ·
                  refine ⟨41421229223359706662355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 441826445049170204398453 41421229223359706662355)
                  ·
                    rfl

theorem cell20_90751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_90751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90751 prefixEnd_90751 := by exact prefixLift 90751
  have htrace : WordTrace (prefixWord ++ tailWord_90751) baseStart_90751 baseEnd_90751 := by
    simpa [prefixWord, tailWord_90751, baseEnd_90751] using wordTrace_append hprefix tailTrace_90751
  have hstable : (prefixWord ++ tailWord_90751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90751).length < 2 ^ (prefixWord ++ tailWord_90751).sum := by decide
  have hdescent : baseEnd_90751 < baseStart_90751 := by decide
  rcases family_descends (prefixWord ++ tailWord_90751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90775 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_90775 : Nat := 118140960795 + 90775 * 2 ^ 59
def prefixEnd_90775 : Nat := 4983230072969 + 3 ^ 40 * 90775 * 2
def baseEnd_90775 : Nat := 41432183477322289862257

theorem tailTrace_90775 : CollatzResearch.WordTrace tailWord_90775 prefixEnd_90775 41432183477322289862257 := by
  unfold tailWord_90775
  simp only [CollatzResearch.WordTrace]
  refine ⟨3310836246145152980841779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2207224164096768653894519 3310836246145152980841779)
  ·
    refine ⟨4966254369217729471262669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3310836246145152980841779 4966254369217729471262669)
    ·
      refine ⟨1862345388456648551723501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4966254369217729471262669 1862345388456648551723501)
      ·
        refine ⟨698379520671243206896313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1862345388456648551723501 698379520671243206896313)
        ·
          refine ⟨523784640503432405172235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698379520671243206896313 523784640503432405172235)
          ·
            refine ⟨785676960755148607758353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523784640503432405172235 785676960755148607758353)
            ·
              refine ⟨589257720566361455818765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785676960755148607758353 589257720566361455818765)
              ·
                refine ⟨220971645212385545932037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589257720566361455818765 220971645212385545932037)
                ·
                  refine ⟨41432183477322289862257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220971645212385545932037 41432183477322289862257)
                  ·
                    rfl

theorem cell20_90775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_90775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90775 prefixEnd_90775 := by exact prefixLift 90775
  have htrace : WordTrace (prefixWord ++ tailWord_90775) baseStart_90775 baseEnd_90775 := by
    simpa [prefixWord, tailWord_90775, baseEnd_90775] using wordTrace_append hprefix tailTrace_90775
  have hstable : (prefixWord ++ tailWord_90775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90775).length < 2 ^ (prefixWord ++ tailWord_90775).sum := by decide
  have hdescent : baseEnd_90775 < baseStart_90775 := by decide
  rcases family_descends (prefixWord ++ tailWord_90775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90789 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_90789 : Nat := 118140960795 + 90789 * 2 ^ 59
def prefixEnd_90789 : Nat := 4983230072969 + 3 ^ 40 * 90789 * 2
def baseEnd_90789 : Nat := 41438573458800463395533

theorem tailTrace_90789 : CollatzResearch.WordTrace tailWord_90789 prefixEnd_90789 41438573458800463395533 := by
  unfold tailWord_90789
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311346868094433371851421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2207564578729622247900947 3311346868094433371851421)
  ·
    refine ⟨1241755075535412514444283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3311346868094433371851421 1241755075535412514444283)
    ·
      refine ⟨1862632613303118771666425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1241755075535412514444283 1862632613303118771666425)
      ·
        refine ⟨1396974459977339078749819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1862632613303118771666425 1396974459977339078749819)
        ·
          refine ⟨2095461689966008618124729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396974459977339078749819 2095461689966008618124729)
          ·
            refine ⟨1571596267474506463593547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095461689966008618124729 1571596267474506463593547)
            ·
              refine ⟨2357394401211759695390321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571596267474506463593547 2357394401211759695390321)
              ·
                refine ⟨1768045800908819771542741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357394401211759695390321 1768045800908819771542741)
                ·
                  refine ⟨41438573458800463395533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1768045800908819771542741 41438573458800463395533)
                  ·
                    rfl

theorem cell20_90789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_90789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90789 prefixEnd_90789 := by exact prefixLift 90789
  have htrace : WordTrace (prefixWord ++ tailWord_90789) baseStart_90789 baseEnd_90789 := by
    simpa [prefixWord, tailWord_90789, baseEnd_90789] using wordTrace_append hprefix tailTrace_90789
  have hstable : (prefixWord ++ tailWord_90789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90789).length < 2 ^ (prefixWord ++ tailWord_90789).sum := by decide
  have hdescent : baseEnd_90789 < baseStart_90789 := by decide
  rcases family_descends (prefixWord ++ tailWord_90789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90799 : List Nat := [1, 1, 2, 1, 2, 6, 3, 4]
def baseStart_90799 : Nat := 118140960795 + 90799 * 2 ^ 59
def prefixEnd_90799 : Nat := 4983230072969 + 3 ^ 40 * 90799 * 2
def baseEnd_90799 : Nat := 13814379243761624354053

theorem tailTrace_90799 : CollatzResearch.WordTrace tailWord_90799 prefixEnd_90799 13814379243761624354053 := by
  unfold tailWord_90799
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311711598058205079715451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2207807732038803386476967 3311711598058205079715451)
  ·
    refine ⟨4967567397087307619573177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3311711598058205079715451 4967567397087307619573177)
    ·
      refine ⟨3725675547815480714679883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4967567397087307619573177 3725675547815480714679883)
      ·
        refine ⟨5588513321723221072019825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725675547815480714679883 5588513321723221072019825)
        ·
          refine ⟨4191384991292415804014869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5588513321723221072019825 4191384991292415804014869)
          ·
            refine ⟨196471171466831990813197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4191384991292415804014869 196471171466831990813197)
            ·
              refine ⟨73676689300061996554949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196471171466831990813197 73676689300061996554949)
              ·
                refine ⟨13814379243761624354053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73676689300061996554949 13814379243761624354053)
                ·
                  rfl

theorem cell20_90799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_90799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90799 prefixEnd_90799 := by exact prefixLift 90799
  have htrace : WordTrace (prefixWord ++ tailWord_90799) baseStart_90799 baseEnd_90799 := by
    simpa [prefixWord, tailWord_90799, baseEnd_90799] using wordTrace_append hprefix tailTrace_90799
  have hstable : (prefixWord ++ tailWord_90799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90799).length < 2 ^ (prefixWord ++ tailWord_90799).sum := by decide
  have hdescent : baseEnd_90799 < baseStart_90799 := by decide
  rcases family_descends (prefixWord ++ tailWord_90799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90830 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_90830 : Nat := 118140960795 + 90830 * 2 ^ 59
def prefixEnd_90830 : Nat := 4983230072969 + 3 ^ 40 * 90830 * 2
def baseEnd_90830 : Nat := 41457286975986543028699

theorem tailTrace_90830 : CollatzResearch.WordTrace tailWord_90830 prefixEnd_90830 41457286975986543028699 := by
  unfold tailWord_90830
  simp only [CollatzResearch.WordTrace]
  refine ⟨414105282618237171761743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2208561507297264916062629 414105282618237171761743)
  ·
    refine ⟨621157923927355757642615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414105282618237171761743 621157923927355757642615)
    ·
      refine ⟨931736885891033636463923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621157923927355757642615 931736885891033636463923)
      ·
        refine ⟨1397605328836550454695885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931736885891033636463923 1397605328836550454695885)
        ·
          refine ⟨524101998313706420510957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1397605328836550454695885 524101998313706420510957)
          ·
            refine ⟨196538249367639907691609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 524101998313706420510957 196538249367639907691609)
            ·
              refine ⟨147403687025729930768707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196538249367639907691609 147403687025729930768707)
              ·
                refine ⟨221105530538594896153061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147403687025729930768707 221105530538594896153061)
                ·
                  refine ⟨41457286975986543028699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221105530538594896153061 41457286975986543028699)
                  ·
                    rfl

theorem cell20_90830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_90830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90830 prefixEnd_90830 := by exact prefixLift 90830
  have htrace : WordTrace (prefixWord ++ tailWord_90830) baseStart_90830 baseEnd_90830 := by
    simpa [prefixWord, tailWord_90830, baseEnd_90830] using wordTrace_append hprefix tailTrace_90830
  have hstable : (prefixWord ++ tailWord_90830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90830).length < 2 ^ (prefixWord ++ tailWord_90830).sum := by decide
  have hdescent : baseEnd_90830 < baseStart_90830 := by decide
  rcases family_descends (prefixWord ++ tailWord_90830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90865 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_90865 : Nat := 118140960795 + 90865 * 2 ^ 59
def prefixEnd_90865 : Nat := 4983230072969 + 3 ^ 40 * 90865 * 2
def baseEnd_90865 : Nat := 41473261929681976861889

theorem tailTrace_90865 : CollatzResearch.WordTrace tailWord_90865 prefixEnd_90865 41473261929681976861889 := by
  unfold tailWord_90865
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314118815819098351618049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2209412543879398901078699 3314118815819098351618049)
  ·
    refine ⟨2485589111864323763713537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3314118815819098351618049 2485589111864323763713537)
    ·
      refine ⟨1864191833898242822785153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2485589111864323763713537 1864191833898242822785153)
      ·
        refine ⟨1398143875423682117088865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1864191833898242822785153 1398143875423682117088865)
        ·
          refine ⟨1048607906567761587816649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398143875423682117088865 1048607906567761587816649)
          ·
            refine ⟨786455929925821190862487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048607906567761587816649 786455929925821190862487)
            ·
              refine ⟨1179683894888731786293731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786455929925821190862487 1179683894888731786293731)
              ·
                refine ⟨1769525842333097679440597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179683894888731786293731 1769525842333097679440597)
                ·
                  refine ⟨41473261929681976861889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1769525842333097679440597 41473261929681976861889)
                  ·
                    rfl

theorem cell20_90865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_90865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90865 prefixEnd_90865 := by exact prefixLift 90865
  have htrace : WordTrace (prefixWord ++ tailWord_90865) baseStart_90865 baseEnd_90865 := by
    simpa [prefixWord, tailWord_90865, baseEnd_90865] using wordTrace_append hprefix tailTrace_90865
  have hstable : (prefixWord ++ tailWord_90865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90865).length < 2 ^ (prefixWord ++ tailWord_90865).sum := by decide
  have hdescent : baseEnd_90865 < baseStart_90865 := by decide
  rcases family_descends (prefixWord ++ tailWord_90865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90889 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_90889 : Nat := 118140960795 + 90889 * 2 ^ 59
def prefixEnd_90889 : Nat := 4983230072969 + 3 ^ 40 * 90889 * 2
def baseEnd_90889 : Nat := 41484216183644560061791

theorem tailTrace_90889 : CollatzResearch.WordTrace tailWord_90889 prefixEnd_90889 41484216183644560061791 := by
  unfold tailWord_90889
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314994167732150450491721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2209996111821433633661147 3314994167732150450491721)
  ·
    refine ⟨2486245625799112837868791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3314994167732150450491721 2486245625799112837868791)
    ·
      refine ⟨3729368438698669256803187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2486245625799112837868791 3729368438698669256803187)
      ·
        refine ⟨5594052658048003885204781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3729368438698669256803187 5594052658048003885204781)
        ·
          refine ⟨2097769746768001456951793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5594052658048003885204781 2097769746768001456951793)
          ·
            refine ⟨1573327310076001092713845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097769746768001456951793 1573327310076001092713845)
            ·
              refine ⟨147499435319625102441923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1573327310076001092713845 147499435319625102441923)
              ·
                refine ⟨221249152979437653662885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147499435319625102441923 221249152979437653662885)
                ·
                  refine ⟨41484216183644560061791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221249152979437653662885 41484216183644560061791)
                  ·
                    rfl

theorem cell20_90889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_90889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90889 prefixEnd_90889 := by exact prefixLift 90889
  have htrace : WordTrace (prefixWord ++ tailWord_90889) baseStart_90889 baseEnd_90889 := by
    simpa [prefixWord, tailWord_90889, baseEnd_90889] using wordTrace_append hprefix tailTrace_90889
  have hstable : (prefixWord ++ tailWord_90889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90889).length < 2 ^ (prefixWord ++ tailWord_90889).sum := by decide
  have hdescent : baseEnd_90889 < baseStart_90889 := by decide
  rcases family_descends (prefixWord ++ tailWord_90889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90965 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_90965 : Nat := 118140960795 + 90965 * 2 ^ 59
def prefixEnd_90965 : Nat := 4983230072969 + 3 ^ 40 * 90965 * 2
def baseEnd_90965 : Nat := 41518904654526073528147

theorem tailTrace_90965 : CollatzResearch.WordTrace tailWord_90965 prefixEnd_90965 41518904654526073528147 := by
  unfold tailWord_90965
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317766115456815430258349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2211844076971210286838899 3317766115456815430258349)
  ·
    refine ⟨1244162293296305786346881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3317766115456815430258349 1244162293296305786346881)
    ·
      refine ⟨933121719972229339760161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1244162293296305786346881 933121719972229339760161)
      ·
        refine ⟨699841289979172004820121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 933121719972229339760161 699841289979172004820121)
        ·
          refine ⟨524880967484379003615091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699841289979172004820121 524880967484379003615091)
          ·
            refine ⟨787321451226568505422637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524880967484379003615091 787321451226568505422637)
            ·
              refine ⟨295245544209963189533489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787321451226568505422637 295245544209963189533489)
              ·
                refine ⟨221434158157472392150117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295245544209963189533489 221434158157472392150117)
                ·
                  refine ⟨41518904654526073528147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221434158157472392150117 41518904654526073528147)
                  ·
                    rfl

theorem cell20_90965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_90965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90965 prefixEnd_90965 := by exact prefixLift 90965
  have htrace : WordTrace (prefixWord ++ tailWord_90965) baseStart_90965 baseEnd_90965 := by
    simpa [prefixWord, tailWord_90965, baseEnd_90965] using wordTrace_append hprefix tailTrace_90965
  have hstable : (prefixWord ++ tailWord_90965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90965).length < 2 ^ (prefixWord ++ tailWord_90965).sum := by decide
  have hdescent : baseEnd_90965 < baseStart_90965 := by decide
  rcases family_descends (prefixWord ++ tailWord_90965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90978 : List Nat := [3, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_90978 : Nat := 118140960795 + 90978 * 2 ^ 59
def prefixEnd_90978 : Nat := 4983230072969 + 3 ^ 40 * 90978 * 2
def baseEnd_90978 : Nat := 41524838208755806094761

theorem tailTrace_90978 : CollatzResearch.WordTrace tailWord_90978 prefixEnd_90978 41524838208755806094761 := by
  unfold tailWord_90978
  simp only [CollatzResearch.WordTrace]
  refine ⟨829560066102429662620397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2212160176273145766987725 829560066102429662620397)
  ·
    refine ⟨311085024788411123482649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 829560066102429662620397 311085024788411123482649)
    ·
      refine ⟨233313768591308342611987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311085024788411123482649 233313768591308342611987)
      ·
        refine ⟨349970652886962513917981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233313768591308342611987 349970652886962513917981)
        ·
          refine ⟨131238994832610942719243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349970652886962513917981 131238994832610942719243)
          ·
            refine ⟨196858492248916414078865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131238994832610942719243 196858492248916414078865)
            ·
              refine ⟨147643869186687310559149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196858492248916414078865 147643869186687310559149)
              ·
                refine ⟨55366450945007741459681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147643869186687310559149 55366450945007741459681)
                ·
                  refine ⟨41524838208755806094761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55366450945007741459681 41524838208755806094761)
                  ·
                    rfl

theorem cell20_90978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_90978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_90978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_90978 prefixEnd_90978 := by exact prefixLift 90978
  have htrace : WordTrace (prefixWord ++ tailWord_90978) baseStart_90978 baseEnd_90978 := by
    simpa [prefixWord, tailWord_90978, baseEnd_90978] using wordTrace_append hprefix tailTrace_90978
  have hstable : (prefixWord ++ tailWord_90978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90978).length < 2 ^ (prefixWord ++ tailWord_90978).sum := by decide
  have hdescent : baseEnd_90978 < baseStart_90978 := by decide
  rcases family_descends (prefixWord ++ tailWord_90978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91013 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 3]
def baseStart_91013 : Nat := 118140960795 + 91013 * 2 ^ 59
def prefixEnd_91013 : Nat := 4983230072969 + 3 ^ 40 * 91013 * 2
def baseEnd_91013 : Nat := 41540813162451239927951

theorem tailTrace_91013 : CollatzResearch.WordTrace tailWord_91013 prefixEnd_91013 41540813162451239927951 := by
  unfold tailWord_91013
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319516819282919628005693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2213011212855279752003795 3319516819282919628005693)
  ·
    refine ⟨1244818807231094860502135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3319516819282919628005693 1244818807231094860502135)
    ·
      refine ⟨1867228210846642290753203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244818807231094860502135 1867228210846642290753203)
      ·
        refine ⟨2800842316269963436129805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867228210846642290753203 2800842316269963436129805)
        ·
          refine ⟨1050315868601236288548677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2800842316269963436129805 1050315868601236288548677)
          ·
            refine ⟨196934225362731804102877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1050315868601236288548677 196934225362731804102877)
            ·
              refine ⟨73850334511024426538579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196934225362731804102877 73850334511024426538579)
              ·
                refine ⟨110775501766536639807869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73850334511024426538579 110775501766536639807869)
                ·
                  refine ⟨41540813162451239927951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110775501766536639807869 41540813162451239927951)
                  ·
                    rfl

theorem cell20_91013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_91013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91013 prefixEnd_91013 := by exact prefixLift 91013
  have htrace : WordTrace (prefixWord ++ tailWord_91013) baseStart_91013 baseEnd_91013 := by
    simpa [prefixWord, tailWord_91013, baseEnd_91013] using wordTrace_append hprefix tailTrace_91013
  have hstable : (prefixWord ++ tailWord_91013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91013).length < 2 ^ (prefixWord ++ tailWord_91013).sum := by decide
  have hdescent : baseEnd_91013 < baseStart_91013 := by decide
  rcases family_descends (prefixWord ++ tailWord_91013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91030 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_91030 : Nat := 118140960795 + 91030 * 2 ^ 59
def prefixEnd_91030 : Nat := 4983230072969 + 3 ^ 40 * 91030 * 2
def baseEnd_91030 : Nat := 41548572425674736361215

theorem tailTrace_91030 : CollatzResearch.WordTrace tailWord_91030 prefixEnd_91030 41548572425674736361215 := by
  unfold tailWord_91030
  simp only [CollatzResearch.WordTrace]
  refine ⟨207508553763833220710909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2213424573480887687583029 207508553763833220710909)
  ·
    refine ⟨77815707661437457766591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207508553763833220710909 77815707661437457766591)
    ·
      refine ⟨116723561492156186649887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77815707661437457766591 116723561492156186649887)
      ·
        refine ⟨175085342238234279974831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116723561492156186649887 175085342238234279974831)
        ·
          refine ⟨262628013357351419962247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175085342238234279974831 262628013357351419962247)
          ·
            refine ⟨393942020036027129943371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262628013357351419962247 393942020036027129943371)
            ·
              refine ⟨590913030054040694915057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393942020036027129943371 590913030054040694915057)
              ·
                refine ⟨443184772540530521186293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590913030054040694915057 443184772540530521186293)
                ·
                  refine ⟨41548572425674736361215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 443184772540530521186293 41548572425674736361215)
                  ·
                    rfl

theorem cell20_91030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_91030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91030 prefixEnd_91030 := by exact prefixLift 91030
  have htrace : WordTrace (prefixWord ++ tailWord_91030) baseStart_91030 baseEnd_91030 := by
    simpa [prefixWord, tailWord_91030, baseEnd_91030] using wordTrace_append hprefix tailTrace_91030
  have hstable : (prefixWord ++ tailWord_91030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91030).length < 2 ^ (prefixWord ++ tailWord_91030).sum := by decide
  have hdescent : baseEnd_91030 < baseStart_91030 := by decide
  rcases family_descends (prefixWord ++ tailWord_91030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91072 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_91072 : Nat := 118140960795 + 91072 * 2 ^ 59
def prefixEnd_91072 : Nat := 4983230072969 + 3 ^ 40 * 91072 * 2
def baseEnd_91072 : Nat := 41567742370109256961043

theorem tailTrace_91072 : CollatzResearch.WordTrace tailWord_91072 prefixEnd_91072 41567742370109256961043 := by
  unfold tailWord_91072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660834363034586352201735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2214445817379448469602313 1660834363034586352201735)
  ·
    refine ⟨2491251544551879528302603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1660834363034586352201735 2491251544551879528302603)
    ·
      refine ⟨3736877316827819292453905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491251544551879528302603 3736877316827819292453905)
      ·
        refine ⟨2802657987620864469340429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3736877316827819292453905 2802657987620864469340429)
        ·
          refine ⟨1050996745357824176002661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2802657987620864469340429 1050996745357824176002661)
          ·
            refine ⟨197061889754592033000499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1050996745357824176002661 197061889754592033000499)
            ·
              refine ⟨295592834631888049500749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197061889754592033000499 295592834631888049500749)
              ·
                refine ⟨110847312986958018562781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295592834631888049500749 110847312986958018562781)
                ·
                  refine ⟨41567742370109256961043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110847312986958018562781 41567742370109256961043)
                  ·
                    rfl

theorem cell20_91072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_91072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91072 prefixEnd_91072 := by exact prefixLift 91072
  have htrace : WordTrace (prefixWord ++ tailWord_91072) baseStart_91072 baseEnd_91072 := by
    simpa [prefixWord, tailWord_91072, baseEnd_91072] using wordTrace_append hprefix tailTrace_91072
  have hstable : (prefixWord ++ tailWord_91072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91072).length < 2 ^ (prefixWord ++ tailWord_91072).sum := by decide
  have hdescent : baseEnd_91072 < baseStart_91072 := by decide
  rcases family_descends (prefixWord ++ tailWord_91072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91086 : List Nat := [4, 1, 1, 1, 2, 3, 2, 6]
def baseStart_91086 : Nat := 118140960795 + 91086 * 2 ^ 59
def prefixEnd_91086 : Nat := 4983230072969 + 3 ^ 40 * 91086 * 2
def baseEnd_91086 : Nat := 13858044117195810164773

theorem tailTrace_91086 : CollatzResearch.WordTrace tailWord_91086 prefixEnd_91086 13858044117195810164773 := by
  unfold tailWord_91086
  simp only [CollatzResearch.WordTrace]
  refine ⟨415272418502306636926639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2214786232012302063608741 415272418502306636926639)
  ·
    refine ⟨622908627753459955389959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 415272418502306636926639 622908627753459955389959)
    ·
      refine ⟨934362941630189933084939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622908627753459955389959 934362941630189933084939)
      ·
        refine ⟨1401544412445284899627409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934362941630189933084939 1401544412445284899627409)
        ·
          refine ⟨1051158309333963674720557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401544412445284899627409 1051158309333963674720557)
          ·
            refine ⟨394184366000236378020209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1051158309333963674720557 394184366000236378020209)
            ·
              refine ⟨295638274500177283515157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394184366000236378020209 295638274500177283515157)
              ·
                refine ⟨13858044117195810164773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 295638274500177283515157 13858044117195810164773)
                ·
                  rfl

theorem cell20_91086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_91086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91086 prefixEnd_91086 := by exact prefixLift 91086
  have htrace : WordTrace (prefixWord ++ tailWord_91086) baseStart_91086 baseEnd_91086 := by
    simpa [prefixWord, tailWord_91086, baseEnd_91086] using wordTrace_append hprefix tailTrace_91086
  have hstable : (prefixWord ++ tailWord_91086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91086).length < 2 ^ (prefixWord ++ tailWord_91086).sum := by decide
  have hdescent : baseEnd_91086 < baseStart_91086 := by decide
  rcases family_descends (prefixWord ++ tailWord_91086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91106 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_91106 : Nat := 118140960795 + 91106 * 2 ^ 59
def prefixEnd_91106 : Nat := 4983230072969 + 3 ^ 40 * 91106 * 2
def baseEnd_91106 : Nat := 41583260896556249827571

theorem tailTrace_91106 : CollatzResearch.WordTrace tailWord_91106 prefixEnd_91106 41583260896556249827571 := by
  unfold tailWord_91106
  simp only [CollatzResearch.WordTrace]
  refine ⟨830727201986499127785293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2215272538630664340760781 830727201986499127785293)
  ·
    refine ⟨311522700744937172919485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 830727201986499127785293 311522700744937172919485)
    ·
      refine ⟨116821012779351439844807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311522700744937172919485 116821012779351439844807)
      ·
        refine ⟨175231519169027159767211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116821012779351439844807 175231519169027159767211)
        ·
          refine ⟨262847278753540739650817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175231519169027159767211 262847278753540739650817)
          ·
            refine ⟨197135459065155554738113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262847278753540739650817 197135459065155554738113)
            ·
              refine ⟨147851594298866666053585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197135459065155554738113 147851594298866666053585)
              ·
                refine ⟨110888695724149999540189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147851594298866666053585 110888695724149999540189)
                ·
                  refine ⟨41583260896556249827571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110888695724149999540189 41583260896556249827571)
                  ·
                    rfl

theorem cell20_91106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_91106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91106 prefixEnd_91106 := by exact prefixLift 91106
  have htrace : WordTrace (prefixWord ++ tailWord_91106) baseStart_91106 baseEnd_91106 := by
    simpa [prefixWord, tailWord_91106, baseEnd_91106] using wordTrace_append hprefix tailTrace_91106
  have hstable : (prefixWord ++ tailWord_91106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91106).length < 2 ^ (prefixWord ++ tailWord_91106).sum := by decide
  have hdescent : baseEnd_91106 < baseStart_91106 := by decide
  rcases family_descends (prefixWord ++ tailWord_91106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91109 : List Nat := [1, 3, 1, 6, 1, 2, 2, 2, 2]
def baseStart_91109 : Nat := 118140960795 + 91109 * 2 ^ 59
def prefixEnd_91109 : Nat := 4983230072969 + 3 ^ 40 * 91109 * 2
def baseEnd_91109 : Nat := 41584630178301572727559

theorem tailTrace_91109 : CollatzResearch.WordTrace tailWord_91109 prefixEnd_91109 41584630178301572727559 := by
  unfold tailWord_91109
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323018226935128023500381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2215345484623418682333587 3323018226935128023500381)
  ·
    refine ⟨1246131835100673008812643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3323018226935128023500381 1246131835100673008812643)
    ·
      refine ⟨1869197752651009513218965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1246131835100673008812643 1869197752651009513218965)
      ·
        refine ⟨87618644655516070932139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1869197752651009513218965 87618644655516070932139)
        ·
          refine ⟨131427966983274106398209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87618644655516070932139 131427966983274106398209)
          ·
            refine ⟨98570975237455579798657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131427966983274106398209 98570975237455579798657)
            ·
              refine ⟨73928231428091684848993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98570975237455579798657 73928231428091684848993)
              ·
                refine ⟨55446173571068763636745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73928231428091684848993 55446173571068763636745)
                ·
                  refine ⟨41584630178301572727559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55446173571068763636745 41584630178301572727559)
                  ·
                    rfl

theorem cell20_91109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_91109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91109 prefixEnd_91109 := by exact prefixLift 91109
  have htrace : WordTrace (prefixWord ++ tailWord_91109) baseStart_91109 baseEnd_91109 := by
    simpa [prefixWord, tailWord_91109, baseEnd_91109] using wordTrace_append hprefix tailTrace_91109
  have hstable : (prefixWord ++ tailWord_91109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91109).length < 2 ^ (prefixWord ++ tailWord_91109).sum := by decide
  have hdescent : baseEnd_91109 < baseStart_91109 := by decide
  rcases family_descends (prefixWord ++ tailWord_91109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91145 : List Nat := [1, 2, 1, 1, 3, 1, 1, 10]
def baseStart_91145 : Nat := 118140960795 + 91145 * 2 ^ 59
def prefixEnd_91145 : Nat := 4983230072969 + 3 ^ 40 * 91145 * 2
def baseEnd_91145 : Nat := 13867020519748482509137

theorem tailTrace_91145 : CollatzResearch.WordTrace tailWord_91145 prefixEnd_91145 13867020519748482509137 := by
  unfold tailWord_91145
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324331254804706171810889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2216220836536470781207259 3324331254804706171810889)
  ·
    refine ⟨2493248441103529628858167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3324331254804706171810889 2493248441103529628858167)
    ·
      refine ⟨3739872661655294443287251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493248441103529628858167 3739872661655294443287251)
      ·
        refine ⟨5609808992482941664930877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739872661655294443287251 5609808992482941664930877)
        ·
          refine ⟨2103678372181103124349079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5609808992482941664930877 2103678372181103124349079)
          ·
            refine ⟨3155517558271654686523619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103678372181103124349079 3155517558271654686523619)
            ·
              refine ⟨4733276337407482029785429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155517558271654686523619 4733276337407482029785429)
              ·
                refine ⟨13867020519748482509137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4733276337407482029785429 13867020519748482509137)
                ·
                  rfl

theorem cell20_91145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_91145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91145 prefixEnd_91145 := by exact prefixLift 91145
  have htrace : WordTrace (prefixWord ++ tailWord_91145) baseStart_91145 baseEnd_91145 := by
    simpa [prefixWord, tailWord_91145, baseEnd_91145] using wordTrace_append hprefix tailTrace_91145
  have hstable : (prefixWord ++ tailWord_91145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91145).length < 2 ^ (prefixWord ++ tailWord_91145).sum := by decide
  have hdescent : baseEnd_91145 < baseStart_91145 := by decide
  rcases family_descends (prefixWord ++ tailWord_91145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91172 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_91172 : Nat := 118140960795 + 91172 * 2 ^ 59
def prefixEnd_91172 : Nat := 4983230072969 + 3 ^ 40 * 91172 * 2
def baseEnd_91172 : Nat := 41613385094953353627301

theorem tailTrace_91172 : CollatzResearch.WordTrace tailWord_91172 prefixEnd_91172 41613385094953353627301 := by
  unfold tailWord_91172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662658012853444891521885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2216877350471259855362513 1662658012853444891521885)
  ·
    refine ⟨623496754820041834320707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1662658012853444891521885 623496754820041834320707)
    ·
      refine ⟨935245132230062751481061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623496754820041834320707 935245132230062751481061)
      ·
        refine ⟨175358462293136765902699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 935245132230062751481061 175358462293136765902699)
        ·
          refine ⟨263037693439705148854049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175358462293136765902699 263037693439705148854049)
          ·
            refine ⟨197278270079778861640537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263037693439705148854049 197278270079778861640537)
            ·
              refine ⟨147958702559834146230403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197278270079778861640537 147958702559834146230403)
              ·
                refine ⟨221938053839751219345605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147958702559834146230403 221938053839751219345605)
                ·
                  refine ⟨41613385094953353627301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221938053839751219345605 41613385094953353627301)
                  ·
                    rfl

theorem cell20_91172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_91172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91172 prefixEnd_91172 := by exact prefixLift 91172
  have htrace : WordTrace (prefixWord ++ tailWord_91172) baseStart_91172 baseEnd_91172 := by
    simpa [prefixWord, tailWord_91172, baseEnd_91172] using wordTrace_append hprefix tailTrace_91172
  have hstable : (prefixWord ++ tailWord_91172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91172).length < 2 ^ (prefixWord ++ tailWord_91172).sum := by decide
  have hdescent : baseEnd_91172 < baseStart_91172 := by decide
  rcases family_descends (prefixWord ++ tailWord_91172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91193 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_91193 : Nat := 118140960795 + 91193 * 2 ^ 59
def prefixEnd_91193 : Nat := 4983230072969 + 3 ^ 40 * 91193 * 2
def baseEnd_91193 : Nat := 41622970067170613927215

theorem tailTrace_91193 : CollatzResearch.WordTrace tailWord_91193 prefixEnd_91193 41622970067170613927215 := by
  unfold tailWord_91193
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326081958630810369558233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2217387972420540246372155 3326081958630810369558233)
  ·
    refine ⟨2494561468973107777168675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3326081958630810369558233 2494561468973107777168675)
    ·
      refine ⟨3741842203459661665753013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494561468973107777168675 3741842203459661665753013)
      ·
        refine ⟨350797706574343281164345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3741842203459661665753013 350797706574343281164345)
        ·
          refine ⟨263098279930757460873259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350797706574343281164345 263098279930757460873259)
          ·
            refine ⟨394647419896136191309889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263098279930757460873259 394647419896136191309889)
            ·
              refine ⟨295985564922102143482417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394647419896136191309889 295985564922102143482417)
              ·
                refine ⟨221989173691576607611813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295985564922102143482417 221989173691576607611813)
                ·
                  refine ⟨41622970067170613927215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221989173691576607611813 41622970067170613927215)
                  ·
                    rfl

theorem cell20_91193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_91193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91193 prefixEnd_91193 := by exact prefixLift 91193
  have htrace : WordTrace (prefixWord ++ tailWord_91193) baseStart_91193 baseEnd_91193 := by
    simpa [prefixWord, tailWord_91193, baseEnd_91193] using wordTrace_append hprefix tailTrace_91193
  have hstable : (prefixWord ++ tailWord_91193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91193).length < 2 ^ (prefixWord ++ tailWord_91193).sum := by decide
  have hdescent : baseEnd_91193 < baseStart_91193 := by decide
  rcases family_descends (prefixWord ++ tailWord_91193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91206 : List Nat := [6, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_91206 : Nat := 118140960795 + 91206 * 2 ^ 59
def prefixEnd_91206 : Nat := 4983230072969 + 3 ^ 40 * 91206 * 2
def baseEnd_91206 : Nat := 41628903621400346493829

theorem tailTrace_91206 : CollatzResearch.WordTrace tailWord_91206 prefixEnd_91206 41628903621400346493829 := by
  unfold tailWord_91206
  simp only [CollatzResearch.WordTrace]
  refine ⟨103954878361991049680671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2217704071722475726520981 103954878361991049680671)
  ·
    refine ⟨155932317542986574521007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103954878361991049680671 155932317542986574521007)
    ·
      refine ⟨233898476314479861781511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155932317542986574521007 233898476314479861781511)
      ·
        refine ⟨350847714471719792672267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233898476314479861781511 350847714471719792672267)
        ·
          refine ⟨526271571707579689008401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350847714471719792672267 526271571707579689008401)
          ·
            refine ⟨394703678780684766756301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526271571707579689008401 394703678780684766756301)
            ·
              refine ⟨148013879542756787533613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394703678780684766756301 148013879542756787533613)
              ·
                refine ⟨55505204828533795325105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148013879542756787533613 55505204828533795325105)
                ·
                  refine ⟨41628903621400346493829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55505204828533795325105 41628903621400346493829)
                  ·
                    rfl

theorem cell20_91206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_91206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91206 prefixEnd_91206 := by exact prefixLift 91206
  have htrace : WordTrace (prefixWord ++ tailWord_91206) baseStart_91206 baseEnd_91206 := by
    simpa [prefixWord, tailWord_91206, baseEnd_91206] using wordTrace_append hprefix tailTrace_91206
  have hstable : (prefixWord ++ tailWord_91206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91206).length < 2 ^ (prefixWord ++ tailWord_91206).sum := by decide
  have hdescent : baseEnd_91206 < baseStart_91206 := by decide
  rcases family_descends (prefixWord ++ tailWord_91206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91207 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_91207 : Nat := 118140960795 + 91207 * 2 ^ 59
def prefixEnd_91207 : Nat := 4983230072969 + 3 ^ 40 * 91207 * 2
def baseEnd_91207 : Nat := 41629360048648787460491

theorem tailTrace_91207 : CollatzResearch.WordTrace tailWord_91207 prefixEnd_91207 41629360048648787460491 := by
  unfold tailWord_91207
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326592580580090760567875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2217728387053393840378583 3326592580580090760567875)
  ·
    refine ⟨4989888870870136140851813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3326592580580090760567875 4989888870870136140851813)
    ·
      refine ⟨935604163288150526409715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4989888870870136140851813 935604163288150526409715)
      ·
        refine ⟨1403406244932225789614573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935604163288150526409715 1403406244932225789614573)
        ·
          refine ⟨526277341849584671105465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1403406244932225789614573 526277341849584671105465)
          ·
            refine ⟨394708006387188503329099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526277341849584671105465 394708006387188503329099)
            ·
              refine ⟨592062009580782754993649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394708006387188503329099 592062009580782754993649)
              ·
                refine ⟨444046507185587066245237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592062009580782754993649 444046507185587066245237)
                ·
                  refine ⟨41629360048648787460491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 444046507185587066245237 41629360048648787460491)
                  ·
                    rfl

theorem cell20_91207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_91207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91207 prefixEnd_91207 := by exact prefixLift 91207
  have htrace : WordTrace (prefixWord ++ tailWord_91207) baseStart_91207 baseEnd_91207 := by
    simpa [prefixWord, tailWord_91207, baseEnd_91207] using wordTrace_append hprefix tailTrace_91207
  have hstable : (prefixWord ++ tailWord_91207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91207).length < 2 ^ (prefixWord ++ tailWord_91207).sum := by decide
  have hdescent : baseEnd_91207 < baseStart_91207 := by decide
  rcases family_descends (prefixWord ++ tailWord_91207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91210 : List Nat := [3, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_91210 : Nat := 118140960795 + 91210 * 2 ^ 59
def prefixEnd_91210 : Nat := 4983230072969 + 3 ^ 40 * 91210 * 2
def baseEnd_91210 : Nat := 41630729330394110360479

theorem tailTrace_91210 : CollatzResearch.WordTrace tailWord_91210 prefixEnd_91210 41630729330394110360479 := by
  unfold tailWord_91210
  simp only [CollatzResearch.WordTrace]
  refine ⟨831675499892305568231771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2217801333046148181951389 831675499892305568231771)
  ·
    refine ⟨1247513249838458352347657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831675499892305568231771 1247513249838458352347657)
    ·
      refine ⟨935634937378843764260743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1247513249838458352347657 935634937378843764260743)
      ·
        refine ⟨1403452406068265646391115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935634937378843764260743 1403452406068265646391115)
        ·
          refine ⟨2105178609102398469586673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403452406068265646391115 2105178609102398469586673)
          ·
            refine ⟨1578883956826798852190005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2105178609102398469586673 1578883956826798852190005)
            ·
              refine ⟨148020370952512392392813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1578883956826798852190005 148020370952512392392813)
              ·
                refine ⟨55507639107192147147305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148020370952512392392813 55507639107192147147305)
                ·
                  refine ⟨41630729330394110360479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55507639107192147147305 41630729330394110360479)
                  ·
                    rfl

theorem cell20_91210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_91210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91210 prefixEnd_91210 := by exact prefixLift 91210
  have htrace : WordTrace (prefixWord ++ tailWord_91210) baseStart_91210 baseEnd_91210 := by
    simpa [prefixWord, tailWord_91210, baseEnd_91210] using wordTrace_append hprefix tailTrace_91210
  have hstable : (prefixWord ++ tailWord_91210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91210).length < 2 ^ (prefixWord ++ tailWord_91210).sum := by decide
  have hdescent : baseEnd_91210 < baseStart_91210 := by decide
  rcases family_descends (prefixWord ++ tailWord_91210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91241 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 3]
def baseStart_91241 : Nat := 118140960795 + 91241 * 2 ^ 59
def prefixEnd_91241 : Nat := 4983230072969 + 3 ^ 40 * 91241 * 2
def baseEnd_91241 : Nat := 41644878575095780327019

theorem tailTrace_91241 : CollatzResearch.WordTrace tailWord_91241 prefixEnd_91241 41644878575095780327019 := by
  unfold tailWord_91241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327832662456914567305577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2218555108304609711537051 3327832662456914567305577)
  ·
    refine ⟨2495874496842685925479183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3327832662456914567305577 2495874496842685925479183)
    ·
      refine ⟨3743811745264028888218775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2495874496842685925479183 3743811745264028888218775)
      ·
        refine ⟨5615717617896043332328163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3743811745264028888218775 5615717617896043332328163)
        ·
          refine ⟨8423576426844064998492245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615717617896043332328163 8423576426844064998492245)
          ·
            refine ⟨98713786252078886701081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 8423576426844064998492245 98713786252078886701081)
            ·
              refine ⟨74035339689059165025811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98713786252078886701081 74035339689059165025811)
              ·
                refine ⟨111053009533588747538717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74035339689059165025811 111053009533588747538717)
                ·
                  refine ⟨41644878575095780327019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111053009533588747538717 41644878575095780327019)
                  ·
                    rfl

theorem cell20_91241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_91241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91241 prefixEnd_91241 := by exact prefixLift 91241
  have htrace : WordTrace (prefixWord ++ tailWord_91241) baseStart_91241 baseEnd_91241 := by
    simpa [prefixWord, tailWord_91241, baseEnd_91241] using wordTrace_append hprefix tailTrace_91241
  have hstable : (prefixWord ++ tailWord_91241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91241).length < 2 ^ (prefixWord ++ tailWord_91241).sum := by decide
  have hdescent : baseEnd_91241 < baseStart_91241 := by decide
  rcases family_descends (prefixWord ++ tailWord_91241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91282 : List Nat := [3, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_91282 : Nat := 118140960795 + 91282 * 2 ^ 59
def prefixEnd_91282 : Nat := 4983230072969 + 3 ^ 40 * 91282 * 2
def baseEnd_91282 : Nat := 41663592092281859960185

theorem tailTrace_91282 : CollatzResearch.WordTrace tailWord_91282 prefixEnd_91282 41663592092281859960185 := by
  unfold tailWord_91282
  simp only [CollatzResearch.WordTrace]
  refine ⟨832332013827094642387025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2219552036872252379698733 832332013827094642387025)
  ·
    refine ⟨624249010370320981790269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 832332013827094642387025 624249010370320981790269)
    ·
      refine ⟨234093378888870368171351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 624249010370320981790269 234093378888870368171351)
      ·
        refine ⟨351140068333305552257027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234093378888870368171351 351140068333305552257027)
        ·
          refine ⟨526710102499958328385541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351140068333305552257027 526710102499958328385541)
          ·
            refine ⟨98758144218742186572289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 526710102499958328385541 98758144218742186572289)
            ·
              refine ⟨74068608164056639929217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98758144218742186572289 74068608164056639929217)
              ·
                refine ⟨55551456123042479946913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74068608164056639929217 55551456123042479946913)
                ·
                  refine ⟨41663592092281859960185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55551456123042479946913 41663592092281859960185)
                  ·
                    rfl

theorem cell20_91282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_91282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91282 prefixEnd_91282 := by exact prefixLift 91282
  have htrace : WordTrace (prefixWord ++ tailWord_91282) baseStart_91282 baseEnd_91282 := by
    simpa [prefixWord, tailWord_91282, baseEnd_91282] using wordTrace_append hprefix tailTrace_91282
  have hstable : (prefixWord ++ tailWord_91282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91282).length < 2 ^ (prefixWord ++ tailWord_91282).sum := by decide
  have hdescent : baseEnd_91282 < baseStart_91282 := by decide
  rcases family_descends (prefixWord ++ tailWord_91282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91283 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 3]
def baseStart_91283 : Nat := 118140960795 + 91283 * 2 ^ 59
def prefixEnd_91283 : Nat := 4983230072969 + 3 ^ 40 * 91283 * 2
def baseEnd_91283 : Nat := 41664048519530300926847

theorem tailTrace_91283 : CollatzResearch.WordTrace tailWord_91283 prefixEnd_91283 41664048519530300926847 := by
  unfold tailWord_91283
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329364528304755740334503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2219576352203170493556335 3329364528304755740334503)
  ·
    refine ⟨4994046792457133610501755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3329364528304755740334503 4994046792457133610501755)
    ·
      refine ⟨7491070188685700415752633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4994046792457133610501755 7491070188685700415752633)
      ·
        refine ⟨5618302641514275311814475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491070188685700415752633 5618302641514275311814475)
        ·
          refine ⟨8427453962271412967721713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5618302641514275311814475 8427453962271412967721713)
          ·
            refine ⟨6320590471703559725791285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8427453962271412967721713 6320590471703559725791285)
            ·
              refine ⟨592555356722208724292933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6320590471703559725791285 592555356722208724292933)
              ·
                refine ⟨111104129385414135804925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592555356722208724292933 111104129385414135804925)
                ·
                  refine ⟨41664048519530300926847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111104129385414135804925 41664048519530300926847)
                  ·
                    rfl

theorem cell20_91283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_91283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91283 prefixEnd_91283 := by exact prefixLift 91283
  have htrace : WordTrace (prefixWord ++ tailWord_91283) baseStart_91283 baseEnd_91283 := by
    simpa [prefixWord, tailWord_91283, baseEnd_91283] using wordTrace_append hprefix tailTrace_91283
  have hstable : (prefixWord ++ tailWord_91283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91283).length < 2 ^ (prefixWord ++ tailWord_91283).sum := by decide
  have hdescent : baseEnd_91283 < baseStart_91283 := by decide
  rcases family_descends (prefixWord ++ tailWord_91283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91300 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_91300 : Nat := 118140960795 + 91300 * 2 ^ 59
def prefixEnd_91300 : Nat := 4983230072969 + 3 ^ 40 * 91300 * 2
def baseEnd_91300 : Nat := 41671807782753797360111

theorem tailTrace_91300 : CollatzResearch.WordTrace tailWord_91300 prefixEnd_91300 41671807782753797360111 := by
  unfold tailWord_91300
  simp only [CollatzResearch.WordTrace]
  refine ⟨1664992284621583821851677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2219989712828778429135569 1664992284621583821851677)
  ·
    refine ⟨624372106733093933194379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1664992284621583821851677 624372106733093933194379)
    ·
      refine ⟨936558160099640899791569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 624372106733093933194379 936558160099640899791569)
      ·
        refine ⟨702418620074730674843677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 936558160099640899791569 702418620074730674843677)
        ·
          refine ⟨263406982528024003066379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 702418620074730674843677 263406982528024003066379)
          ·
            refine ⟨395110473792036004599569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263406982528024003066379 395110473792036004599569)
            ·
              refine ⟨296332855344027003449677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395110473792036004599569 296332855344027003449677)
              ·
                refine ⟨111124820754010126293629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296332855344027003449677 111124820754010126293629)
                ·
                  refine ⟨41671807782753797360111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111124820754010126293629 41671807782753797360111)
                  ·
                    rfl

theorem cell20_91300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_91300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91300 prefixEnd_91300 := by exact prefixLift 91300
  have htrace : WordTrace (prefixWord ++ tailWord_91300) baseStart_91300 baseEnd_91300 := by
    simpa [prefixWord, tailWord_91300, baseEnd_91300] using wordTrace_append hprefix tailTrace_91300
  have hstable : (prefixWord ++ tailWord_91300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91300).length < 2 ^ (prefixWord ++ tailWord_91300).sum := by decide
  have hdescent : baseEnd_91300 < baseStart_91300 := by decide
  rcases family_descends (prefixWord ++ tailWord_91300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91324 : List Nat := [2, 2, 2, 3, 2, 1, 1, 5, 2]
def baseStart_91324 : Nat := 118140960795 + 91324 * 2 ^ 59
def prefixEnd_91324 : Nat := 4983230072969 + 3 ^ 40 * 91324 * 2
def baseEnd_91324 : Nat := 41682762036716380560013

theorem tailTrace_91324 : CollatzResearch.WordTrace tailWord_91324 prefixEnd_91324 41682762036716380560013 := by
  unfold tailWord_91324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1665429960578109871288513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2220573280770813161718017 1665429960578109871288513)
  ·
    refine ⟨1249072470433582403466385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1665429960578109871288513 1249072470433582403466385)
    ·
      refine ⟨936804352825186802599789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1249072470433582403466385 936804352825186802599789)
      ·
        refine ⟨351301632309445050974921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 936804352825186802599789 351301632309445050974921)
        ·
          refine ⟨263476224232083788231191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351301632309445050974921 263476224232083788231191)
          ·
            refine ⟨395214336348125682346787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263476224232083788231191 395214336348125682346787)
            ·
              refine ⟨592821504522188523520181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395214336348125682346787 592821504522188523520181)
              ·
                refine ⟨55577016048955174080017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 592821504522188523520181 55577016048955174080017)
                ·
                  refine ⟨41682762036716380560013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55577016048955174080017 41682762036716380560013)
                  ·
                    rfl

theorem cell20_91324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_91324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91324 prefixEnd_91324 := by exact prefixLift 91324
  have htrace : WordTrace (prefixWord ++ tailWord_91324) baseStart_91324 baseEnd_91324 := by
    simpa [prefixWord, tailWord_91324, baseEnd_91324] using wordTrace_append hprefix tailTrace_91324
  have hstable : (prefixWord ++ tailWord_91324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91324).length < 2 ^ (prefixWord ++ tailWord_91324).sum := by decide
  have hdescent : baseEnd_91324 < baseStart_91324 := by decide
  rcases family_descends (prefixWord ++ tailWord_91324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91330 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_91330 : Nat := 118140960795 + 91330 * 2 ^ 59
def prefixEnd_91330 : Nat := 4983230072969 + 3 ^ 40 * 91330 * 2
def baseEnd_91330 : Nat := 41685500600207026359989

theorem tailTrace_91330 : CollatzResearch.WordTrace tailWord_91330 prefixEnd_91330 41685500600207026359989 := by
  unfold tailWord_91330
  simp only [CollatzResearch.WordTrace]
  refine ⟨832769689783620691823861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2220719172756321844863629 832769689783620691823861)
  ·
    refine ⟨78072158417214439858487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 832769689783620691823861 78072158417214439858487)
    ·
      refine ⟨117108237625821659787731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78072158417214439858487 117108237625821659787731)
      ·
        refine ⟨175662356438732489681597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117108237625821659787731 175662356438732489681597)
        ·
          refine ⟨65873383664524683630599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175662356438732489681597 65873383664524683630599)
          ·
            refine ⟨98810075496787025445899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65873383664524683630599 98810075496787025445899)
            ·
              refine ⟨148215113245180538168849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98810075496787025445899 148215113245180538168849)
              ·
                refine ⟨111161334933885403626637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148215113245180538168849 111161334933885403626637)
                ·
                  refine ⟨41685500600207026359989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111161334933885403626637 41685500600207026359989)
                  ·
                    rfl

theorem cell20_91330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_91330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91330 prefixEnd_91330 := by exact prefixLift 91330
  have htrace : WordTrace (prefixWord ++ tailWord_91330) baseStart_91330 baseEnd_91330 := by
    simpa [prefixWord, tailWord_91330, baseEnd_91330] using wordTrace_append hprefix tailTrace_91330
  have hstable : (prefixWord ++ tailWord_91330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91330).length < 2 ^ (prefixWord ++ tailWord_91330).sum := by decide
  have hdescent : baseEnd_91330 < baseStart_91330 := by decide
  rcases family_descends (prefixWord ++ tailWord_91330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91338 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_91338 : Nat := 118140960795 + 91338 * 2 ^ 59
def prefixEnd_91338 : Nat := 4983230072969 + 3 ^ 40 * 91338 * 2
def baseEnd_91338 : Nat := 41689152018194554093289

theorem tailTrace_91338 : CollatzResearch.WordTrace tailWord_91338 prefixEnd_91338 41689152018194554093289 := by
  unfold tailWord_91338
  simp only [CollatzResearch.WordTrace]
  refine ⟨832842635776375033396667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2220913695403666755724445 832842635776375033396667)
  ·
    refine ⟨1249263953664562550095001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832842635776375033396667 1249263953664562550095001)
    ·
      refine ⟨936947965248421912571251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1249263953664562550095001 936947965248421912571251)
      ·
        refine ⟨1405421947872632868856877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936947965248421912571251 1405421947872632868856877)
        ·
          refine ⟨527033230452237325821329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1405421947872632868856877 527033230452237325821329)
          ·
            refine ⟨395274922839177994365997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527033230452237325821329 395274922839177994365997)
            ·
              refine ⟨148228096064691747887249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395274922839177994365997 148228096064691747887249)
              ·
                refine ⟨111171072048518810915437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148228096064691747887249 111171072048518810915437)
                ·
                  refine ⟨41689152018194554093289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111171072048518810915437 41689152018194554093289)
                  ·
                    rfl

theorem cell20_91338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_91338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91338 prefixEnd_91338 := by exact prefixLift 91338
  have htrace : WordTrace (prefixWord ++ tailWord_91338) baseStart_91338 baseEnd_91338 := by
    simpa [prefixWord, tailWord_91338, baseEnd_91338] using wordTrace_append hprefix tailTrace_91338
  have hstable : (prefixWord ++ tailWord_91338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91338).length < 2 ^ (prefixWord ++ tailWord_91338).sum := by decide
  have hdescent : baseEnd_91338 < baseStart_91338 := by decide
  rcases family_descends (prefixWord ++ tailWord_91338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91359 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 3]
def baseStart_91359 : Nat := 118140960795 + 91359 * 2 ^ 59
def prefixEnd_91359 : Nat := 4983230072969 + 3 ^ 40 * 91359 * 2
def baseEnd_91359 : Nat := 41698736990411814393203

theorem tailTrace_91359 : CollatzResearch.WordTrace tailWord_91359 prefixEnd_91359 41698736990411814393203 := by
  unfold tailWord_91359
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332136476029420720101131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2221424317352947146734087 3332136476029420720101131)
  ·
    refine ⟨4998204714044131080151697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3332136476029420720101131 4998204714044131080151697)
    ·
      refine ⟨3748653535533098310113773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4998204714044131080151697 3748653535533098310113773)
      ·
        refine ⟨1405745075824911866292665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3748653535533098310113773 1405745075824911866292665)
        ·
          refine ⟨1054308806868683899719499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1405745075824911866292665 1054308806868683899719499)
          ·
            refine ⟨1581463210303025849579249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054308806868683899719499 1581463210303025849579249)
            ·
              refine ⟨1186097407727269387184437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581463210303025849579249 1186097407727269387184437)
              ·
                refine ⟨111196631974431505048541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1186097407727269387184437 111196631974431505048541)
                ·
                  refine ⟨41698736990411814393203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111196631974431505048541 41698736990411814393203)
                  ·
                    rfl

theorem cell20_91359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_91359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91359 prefixEnd_91359 := by exact prefixLift 91359
  have htrace : WordTrace (prefixWord ++ tailWord_91359) baseStart_91359 baseEnd_91359 := by
    simpa [prefixWord, tailWord_91359, baseEnd_91359] using wordTrace_append hprefix tailTrace_91359
  have hstable : (prefixWord ++ tailWord_91359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91359).length < 2 ^ (prefixWord ++ tailWord_91359).sum := by decide
  have hdescent : baseEnd_91359 < baseStart_91359 := by decide
  rcases family_descends (prefixWord ++ tailWord_91359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91390 : List Nat := [4, 2, 2, 1, 1, 2, 8]
def baseStart_91390 : Nat := 118140960795 + 91390 * 2 ^ 59
def prefixEnd_91390 : Nat := 4983230072969 + 3 ^ 40 * 91390 * 2
def baseEnd_91390 : Nat := 4634765137234831595527

theorem tailTrace_91390 : CollatzResearch.WordTrace tailWord_91390 prefixEnd_91390 4634765137234831595527 := by
  unfold tailWord_91390
  simp only [CollatzResearch.WordTrace]
  refine ⟨416658392364639126809953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2222178092611408676319749 416658392364639126809953)
  ·
    refine ⟨312493794273479345107465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 416658392364639126809953 312493794273479345107465)
    ·
      refine ⟨234370345705109508830599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 312493794273479345107465 234370345705109508830599)
      ·
        refine ⟨351555518557664263245899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234370345705109508830599 351555518557664263245899)
        ·
          refine ⟨527333277836496394868849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351555518557664263245899 527333277836496394868849)
          ·
            refine ⟨395499958377372296151637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527333277836496394868849 395499958377372296151637)
            ·
              refine ⟨4634765137234831595527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 395499958377372296151637 4634765137234831595527)
              ·
                rfl

theorem cell20_91390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 8].length) (baseStart_91390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91390 prefixEnd_91390 := by exact prefixLift 91390
  have htrace : WordTrace (prefixWord ++ tailWord_91390) baseStart_91390 baseEnd_91390 := by
    simpa [prefixWord, tailWord_91390, baseEnd_91390] using wordTrace_append hprefix tailTrace_91390
  have hstable : (prefixWord ++ tailWord_91390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91390).length < 2 ^ (prefixWord ++ tailWord_91390).sum := by decide
  have hdescent : baseEnd_91390 < baseStart_91390 := by decide
  rcases family_descends (prefixWord ++ tailWord_91390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91397 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 3]
def baseStart_91397 : Nat := 118140960795 + 91397 * 2 ^ 59
def prefixEnd_91397 : Nat := 4983230072969 + 3 ^ 40 * 91397 * 2
def baseEnd_91397 : Nat := 41716081225852571126381

theorem tailTrace_91397 : CollatzResearch.WordTrace tailWord_91397 prefixEnd_91397 41716081225852571126381 := by
  unfold tailWord_91397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333522449891753209984445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2222348299927835473322963 3333522449891753209984445)
  ·
    refine ⟨1250070918709407453744167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3333522449891753209984445 1250070918709407453744167)
    ·
      refine ⟨1875106378064111180616251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250070918709407453744167 1875106378064111180616251)
      ·
        refine ⟨2812659567096166770924377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875106378064111180616251 2812659567096166770924377)
        ·
          refine ⟨2109494675322125078193283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2812659567096166770924377 2109494675322125078193283)
          ·
            refine ⟨3164242012983187617289925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109494675322125078193283 3164242012983187617289925)
            ·
              refine ⟨593295377434347678241861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3164242012983187617289925 593295377434347678241861)
              ·
                refine ⟨111242883268940189670349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 593295377434347678241861 111242883268940189670349)
                ·
                  refine ⟨41716081225852571126381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111242883268940189670349 41716081225852571126381)
                  ·
                    rfl

theorem cell20_91397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_91397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91397 prefixEnd_91397 := by exact prefixLift 91397
  have htrace : WordTrace (prefixWord ++ tailWord_91397) baseStart_91397 baseEnd_91397 := by
    simpa [prefixWord, tailWord_91397, baseEnd_91397] using wordTrace_append hprefix tailTrace_91397
  have hstable : (prefixWord ++ tailWord_91397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91397).length < 2 ^ (prefixWord ++ tailWord_91397).sum := by decide
  have hdescent : baseEnd_91397 < baseStart_91397 := by decide
  rcases family_descends (prefixWord ++ tailWord_91397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91400 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_91400 : Nat := 118140960795 + 91400 * 2 ^ 59
def prefixEnd_91400 : Nat := 4983230072969 + 3 ^ 40 * 91400 * 2
def baseEnd_91400 : Nat := 41717450507597894026369

theorem tailTrace_91400 : CollatzResearch.WordTrace tailWord_91400 prefixEnd_91400 41717450507597894026369 := by
  unfold tailWord_91400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666815934440442361171827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2222421245920589814895769 1666815934440442361171827)
  ·
    refine ⟨2500223901660663541757741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1666815934440442361171827 2500223901660663541757741)
    ·
      refine ⟨937583963122748828159153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2500223901660663541757741 937583963122748828159153)
      ·
        refine ⟨703187972342061621119365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 937583963122748828159153 703187972342061621119365)
        ·
          refine ⟨131847744814136553959881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 703187972342061621119365 131847744814136553959881)
          ·
            refine ⟨98885808610602415469911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131847744814136553959881 98885808610602415469911)
            ·
              refine ⟨148328712915903623204867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98885808610602415469911 148328712915903623204867)
              ·
                refine ⟨222493069373855434807301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148328712915903623204867 222493069373855434807301)
                ·
                  refine ⟨41717450507597894026369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222493069373855434807301 41717450507597894026369)
                  ·
                    rfl

theorem cell20_91400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_91400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91400 prefixEnd_91400 := by exact prefixLift 91400
  have htrace : WordTrace (prefixWord ++ tailWord_91400) baseStart_91400 baseEnd_91400 := by
    simpa [prefixWord, tailWord_91400, baseEnd_91400] using wordTrace_append hprefix tailTrace_91400
  have hstable : (prefixWord ++ tailWord_91400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91400).length < 2 ^ (prefixWord ++ tailWord_91400).sum := by decide
  have hdescent : baseEnd_91400 < baseStart_91400 := by decide
  rcases family_descends (prefixWord ++ tailWord_91400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91410 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_91410 : Nat := 118140960795 + 91410 * 2 ^ 59
def prefixEnd_91410 : Nat := 4983230072969 + 3 ^ 40 * 91410 * 2
def baseEnd_91410 : Nat := 41722014780082303692995

theorem tailTrace_91410 : CollatzResearch.WordTrace tailWord_91410 prefixEnd_91410 41722014780082303692995 := by
  unfold tailWord_91410
  simp only [CollatzResearch.WordTrace]
  refine ⟨833499149711164107551921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2222664399229770953471789 833499149711164107551921)
  ·
    refine ⟨625124362283373080663941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 833499149711164107551921 625124362283373080663941)
    ·
      refine ⟨117210817928132452624489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 625124362283373080663941 117210817928132452624489)
      ·
        refine ⟨87908113446099339468367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117210817928132452624489 87908113446099339468367)
        ·
          refine ⟨131862170169149009202551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87908113446099339468367 131862170169149009202551)
          ·
            refine ⟨197793255253723513803827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131862170169149009202551 197793255253723513803827)
            ·
              refine ⟨296689882880585270705741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197793255253723513803827 296689882880585270705741)
              ·
                refine ⟨111258706080219476514653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296689882880585270705741 111258706080219476514653)
                ·
                  refine ⟨41722014780082303692995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111258706080219476514653 41722014780082303692995)
                  ·
                    rfl

theorem cell20_91410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_91410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91410 prefixEnd_91410 := by exact prefixLift 91410
  have htrace : WordTrace (prefixWord ++ tailWord_91410) baseStart_91410 baseEnd_91410 := by
    simpa [prefixWord, tailWord_91410, baseEnd_91410] using wordTrace_append hprefix tailTrace_91410
  have hstable : (prefixWord ++ tailWord_91410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91410).length < 2 ^ (prefixWord ++ tailWord_91410).sum := by decide
  have hdescent : baseEnd_91410 < baseStart_91410 := by decide
  rcases family_descends (prefixWord ++ tailWord_91410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91449 : List Nat := [1, 2, 1, 6, 10]
def baseStart_91449 : Nat := 118140960795 + 91449 * 2 ^ 59
def prefixEnd_91449 : Nat := 4983230072969 + 3 ^ 40 * 91449 * 2
def baseEnd_91449 : Nat := 515306363491006190035

theorem tailTrace_91449 : CollatzResearch.WordTrace tailWord_91449 prefixEnd_91449 515306363491006190035 := by
  unfold tailWord_91449
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335419045703366090877401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2223612697135577393918267 3335419045703366090877401)
  ·
    refine ⟨2501564284277524568158051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3335419045703366090877401 2501564284277524568158051)
    ·
      refine ⟨3752346426416286852237077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2501564284277524568158051 3752346426416286852237077)
      ·
        refine ⟨175891238738263446198613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3752346426416286852237077 175891238738263446198613)
        ·
          refine ⟨515306363491006190035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 175891238738263446198613 515306363491006190035)
          ·
            rfl

theorem cell20_91449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 10].length) (baseStart_91449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91449 prefixEnd_91449 := by exact prefixLift 91449
  have htrace : WordTrace (prefixWord ++ tailWord_91449) baseStart_91449 baseEnd_91449 := by
    simpa [prefixWord, tailWord_91449, baseEnd_91449] using wordTrace_append hprefix tailTrace_91449
  have hstable : (prefixWord ++ tailWord_91449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91449).length < 2 ^ (prefixWord ++ tailWord_91449).sum := by decide
  have hdescent : baseEnd_91449 < baseStart_91449 := by decide
  rcases family_descends (prefixWord ++ tailWord_91449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91452 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_91452 : Nat := 118140960795 + 91452 * 2 ^ 59
def prefixEnd_91452 : Nat := 4983230072969 + 3 ^ 40 * 91452 * 2
def baseEnd_91452 : Nat := 41741184724516824292823

theorem tailTrace_91452 : CollatzResearch.WordTrace tailWord_91452 prefixEnd_91452 41741184724516824292823 := by
  unfold tailWord_91452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1667764232346248801618305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2223685643128331735491073 1667764232346248801618305)
  ·
    refine ⟨1250823174259686601213729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1667764232346248801618305 1250823174259686601213729)
    ·
      refine ⟨938117380694764950910297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1250823174259686601213729 938117380694764950910297)
      ·
        refine ⟨703588035521073713182723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 938117380694764950910297 703588035521073713182723)
        ·
          refine ⟨1055382053281610569774085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703588035521073713182723 1055382053281610569774085)
          ·
            refine ⟨197884134990301981832641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1055382053281610569774085 197884134990301981832641)
            ·
              refine ⟨148413101242726486374481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197884134990301981832641 148413101242726486374481)
              ·
                refine ⟨111309825932044864780861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148413101242726486374481 111309825932044864780861)
                ·
                  refine ⟨41741184724516824292823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111309825932044864780861 41741184724516824292823)
                  ·
                    rfl

theorem cell20_91452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_91452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91452 prefixEnd_91452 := by exact prefixLift 91452
  have htrace : WordTrace (prefixWord ++ tailWord_91452) baseStart_91452 baseEnd_91452 := by
    simpa [prefixWord, tailWord_91452, baseEnd_91452] using wordTrace_append hprefix tailTrace_91452
  have hstable : (prefixWord ++ tailWord_91452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91452).length < 2 ^ (prefixWord ++ tailWord_91452).sum := by decide
  have hdescent : baseEnd_91452 < baseStart_91452 := by decide
  rcases family_descends (prefixWord ++ tailWord_91452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91455 : List Nat := [1, 1, 2, 2, 4, 4, 2, 2, 2]
def baseStart_91455 : Nat := 118140960795 + 91455 * 2 ^ 59
def prefixEnd_91455 : Nat := 4983230072969 + 3 ^ 40 * 91455 * 2
def baseEnd_91455 : Nat := 41742554006262147192811

theorem tailTrace_91455 : CollatzResearch.WordTrace tailWord_91455 prefixEnd_91455 41742554006262147192811 := by
  unfold tailWord_91455
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335637883681629115595819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2223758589121086077063879 3335637883681629115595819)
  ·
    refine ⟨5003456825522443673393729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3335637883681629115595819 5003456825522443673393729)
    ·
      refine ⟨3752592619141832755045297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5003456825522443673393729 3752592619141832755045297)
      ·
        refine ⟨2814444464356374566283973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3752592619141832755045297 2814444464356374566283973)
        ·
          refine ⟨527708337066820231178245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2814444464356374566283973 527708337066820231178245)
          ·
            refine ⟨98945313200028793345921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 527708337066820231178245 98945313200028793345921)
            ·
              refine ⟨74208984900021595009441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98945313200028793345921 74208984900021595009441)
              ·
                refine ⟨55656738675016196257081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74208984900021595009441 55656738675016196257081)
                ·
                  refine ⟨41742554006262147192811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55656738675016196257081 41742554006262147192811)
                  ·
                    rfl

theorem cell20_91455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 2].length) (baseStart_91455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91455 prefixEnd_91455 := by exact prefixLift 91455
  have htrace : WordTrace (prefixWord ++ tailWord_91455) baseStart_91455 baseEnd_91455 := by
    simpa [prefixWord, tailWord_91455, baseEnd_91455] using wordTrace_append hprefix tailTrace_91455
  have hstable : (prefixWord ++ tailWord_91455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91455).length < 2 ^ (prefixWord ++ tailWord_91455).sum := by decide
  have hdescent : baseEnd_91455 < baseStart_91455 := by decide
  rcases family_descends (prefixWord ++ tailWord_91455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91473 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 3]
def baseStart_91473 : Nat := 118140960795 + 91473 * 2 ^ 59
def prefixEnd_91473 : Nat := 4983230072969 + 3 ^ 40 * 91473 * 2
def baseEnd_91473 : Nat := 41750769696734084592737

theorem tailTrace_91473 : CollatzResearch.WordTrace tailWord_91473 prefixEnd_91473 41750769696734084592737 := by
  unfold tailWord_91473
  simp only [CollatzResearch.WordTrace]
  refine ⟨3336294397616418189751073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2224196265077612126500715 3336294397616418189751073)
  ·
    refine ⟨2502220798212313642313305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3336294397616418189751073 2502220798212313642313305)
    ·
      refine ⟨1876665598659235231734979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2502220798212313642313305 1876665598659235231734979)
      ·
        refine ⟨2814998397988852847602469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876665598659235231734979 2814998397988852847602469)
        ·
          refine ⟨527812199622909908925463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2814998397988852847602469 527812199622909908925463)
          ·
            refine ⟨791718299434364863388195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527812199622909908925463 791718299434364863388195)
            ·
              refine ⟨1187577449151547295082293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791718299434364863388195 1187577449151547295082293)
              ·
                refine ⟨111335385857957558913965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1187577449151547295082293 111335385857957558913965)
                ·
                  refine ⟨41750769696734084592737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111335385857957558913965 41750769696734084592737)
                  ·
                    rfl

theorem cell20_91473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_91473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91473 prefixEnd_91473 := by exact prefixLift 91473
  have htrace : WordTrace (prefixWord ++ tailWord_91473) baseStart_91473 baseEnd_91473 := by
    simpa [prefixWord, tailWord_91473, baseEnd_91473] using wordTrace_append hprefix tailTrace_91473
  have hstable : (prefixWord ++ tailWord_91473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91473).length < 2 ^ (prefixWord ++ tailWord_91473).sum := by decide
  have hdescent : baseEnd_91473 < baseStart_91473 := by decide
  rcases family_descends (prefixWord ++ tailWord_91473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91480 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_91480 : Nat := 118140960795 + 91480 * 2 ^ 59
def prefixEnd_91480 : Nat := 4983230072969 + 3 ^ 40 * 91480 * 2
def baseEnd_91480 : Nat := 41753964687473171359375

theorem tailTrace_91480 : CollatzResearch.WordTrace tailWord_91480 prefixEnd_91480 41753964687473171359375 := by
  unfold tailWord_91480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668274854295529192627947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2224366472394038923503929 1668274854295529192627947)
  ·
    refine ⟨2502412281443293788941921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668274854295529192627947 2502412281443293788941921)
    ·
      refine ⟨1876809211082470341706441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2502412281443293788941921 1876809211082470341706441)
      ·
        refine ⟨1407606908311852756279831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1876809211082470341706441 1407606908311852756279831)
        ·
          refine ⟨2111410362467779134419747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407606908311852756279831 2111410362467779134419747)
          ·
            refine ⟨3167115543701668701629621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111410362467779134419747 3167115543701668701629621)
            ·
              refine ⟨296917082222031440777777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3167115543701668701629621 296917082222031440777777)
              ·
                refine ⟨222687811666523580583333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296917082222031440777777 222687811666523580583333)
                ·
                  refine ⟨41753964687473171359375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222687811666523580583333 41753964687473171359375)
                  ·
                    rfl

theorem cell20_91480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_91480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91480 prefixEnd_91480 := by exact prefixLift 91480
  have htrace : WordTrace (prefixWord ++ tailWord_91480) baseStart_91480 baseEnd_91480 := by
    simpa [prefixWord, tailWord_91480, baseEnd_91480] using wordTrace_append hprefix tailTrace_91480
  have hstable : (prefixWord ++ tailWord_91480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91480).length < 2 ^ (prefixWord ++ tailWord_91480).sum := by decide
  have hdescent : baseEnd_91480 < baseStart_91480 := by decide
  rcases family_descends (prefixWord ++ tailWord_91480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91548 : List Nat := [2, 2, 3, 4, 1, 2, 1, 3, 2]
def baseStart_91548 : Nat := 118140960795 + 91548 * 2 ^ 59
def prefixEnd_91548 : Nat := 4983230072969 + 3 ^ 40 * 91548 * 2
def baseEnd_91548 : Nat := 41785001740367157092431

theorem tailTrace_91548 : CollatzResearch.WordTrace tailWord_91548 prefixEnd_91548 41785001740367157092431 := by
  unfold tailWord_91548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669514936172352999365649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2226019914896470665820865 1669514936172352999365649)
  ·
    refine ⟨1252136202129264749524237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1669514936172352999365649 1252136202129264749524237)
    ·
      refine ⟨469551075798474281071589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1252136202129264749524237 469551075798474281071589)
      ·
        refine ⟨88040826712213927700923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 469551075798474281071589 88040826712213927700923)
        ·
          refine ⟨132061240068320891551385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88040826712213927700923 132061240068320891551385)
          ·
            refine ⟨99045930051240668663539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132061240068320891551385 99045930051240668663539)
            ·
              refine ⟨148568895076861002995309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99045930051240668663539 148568895076861002995309)
              ·
                refine ⟨55713335653822876123241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148568895076861002995309 55713335653822876123241)
                ·
                  refine ⟨41785001740367157092431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55713335653822876123241 41785001740367157092431)
                  ·
                    rfl

theorem cell20_91548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_91548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91548 prefixEnd_91548 := by exact prefixLift 91548
  have htrace : WordTrace (prefixWord ++ tailWord_91548) baseStart_91548 baseEnd_91548 := by
    simpa [prefixWord, tailWord_91548, baseEnd_91548] using wordTrace_append hprefix tailTrace_91548
  have hstable : (prefixWord ++ tailWord_91548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91548).length < 2 ^ (prefixWord ++ tailWord_91548).sum := by decide
  have hdescent : baseEnd_91548 < baseStart_91548 := by decide
  rcases family_descends (prefixWord ++ tailWord_91548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91549 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_91549 : Nat := 118140960795 + 91549 * 2 ^ 59
def prefixEnd_91549 : Nat := 4983230072969 + 3 ^ 40 * 91549 * 2
def baseEnd_91549 : Nat := 41785458167615598059093

theorem tailTrace_91549 : CollatzResearch.WordTrace tailWord_91549 prefixEnd_91549 41785458167615598059093 := by
  unfold tailWord_91549
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339066345341083169517701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2226044230227388779678467 3339066345341083169517701)
  ·
    refine ⟨626074939751453094284569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3339066345341083169517701 626074939751453094284569)
    ·
      refine ⟨469556204813589820713427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626074939751453094284569 469556204813589820713427)
      ·
        refine ⟨704334307220384731070141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469556204813589820713427 704334307220384731070141)
        ·
          refine ⟨264125365207644274151303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 704334307220384731070141 264125365207644274151303)
          ·
            refine ⟨396188047811466411226955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264125365207644274151303 396188047811466411226955)
            ·
              refine ⟨594282071717199616840433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396188047811466411226955 594282071717199616840433)
              ·
                refine ⟨445711553787899712630325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594282071717199616840433 445711553787899712630325)
                ·
                  refine ⟨41785458167615598059093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445711553787899712630325 41785458167615598059093)
                  ·
                    rfl

theorem cell20_91549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_91549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91549 prefixEnd_91549 := by exact prefixLift 91549
  have htrace : WordTrace (prefixWord ++ tailWord_91549) baseStart_91549 baseEnd_91549 := by
    simpa [prefixWord, tailWord_91549, baseEnd_91549] using wordTrace_append hprefix tailTrace_91549
  have hstable : (prefixWord ++ tailWord_91549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91549).length < 2 ^ (prefixWord ++ tailWord_91549).sum := by decide
  have hdescent : baseEnd_91549 < baseStart_91549 := by decide
  rcases family_descends (prefixWord ++ tailWord_91549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91573 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_91573 : Nat := 118140960795 + 91573 * 2 ^ 59
def prefixEnd_91573 : Nat := 4983230072969 + 3 ^ 40 * 91573 * 2
def baseEnd_91573 : Nat := 41796412421578181258995

theorem tailTrace_91573 : CollatzResearch.WordTrace tailWord_91573 prefixEnd_91573 41796412421578181258995 := by
  unfold tailWord_91573
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339941697254135268391373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2226627798169423512260915 3339941697254135268391373)
  ·
    refine ⟨1252478136470300725646765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3339941697254135268391373 1252478136470300725646765)
    ·
      refine ⟨469679301176362772117537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1252478136470300725646765 469679301176362772117537)
      ·
        refine ⟨352259475882272079088153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469679301176362772117537 352259475882272079088153)
        ·
          refine ⟨264194606911704059316115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352259475882272079088153 264194606911704059316115)
          ·
            refine ⟨396291910367556088974173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264194606911704059316115 396291910367556088974173)
            ·
              refine ⟨148609466387833533365315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396291910367556088974173 148609466387833533365315)
              ·
                refine ⟨222914199581750300047973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148609466387833533365315 222914199581750300047973)
                ·
                  refine ⟨41796412421578181258995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222914199581750300047973 41796412421578181258995)
                  ·
                    rfl

theorem cell20_91573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_91573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91573 prefixEnd_91573 := by exact prefixLift 91573
  have htrace : WordTrace (prefixWord ++ tailWord_91573) baseStart_91573 baseEnd_91573 := by
    simpa [prefixWord, tailWord_91573, baseEnd_91573] using wordTrace_append hprefix tailTrace_91573
  have hstable : (prefixWord ++ tailWord_91573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91573).length < 2 ^ (prefixWord ++ tailWord_91573).sum := by decide
  have hdescent : baseEnd_91573 < baseStart_91573 := by decide
  rcases family_descends (prefixWord ++ tailWord_91573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91608 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_91608 : Nat := 118140960795 + 91608 * 2 ^ 59
def prefixEnd_91608 : Nat := 4983230072969 + 3 ^ 40 * 91608 * 2
def baseEnd_91608 : Nat := 41812387375273615092185

theorem tailTrace_91608 : CollatzResearch.WordTrace tailWord_91608 prefixEnd_91608 41812387375273615092185 := by
  unfold tailWord_91608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670609126063668122957739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2227478834751557497276985 1670609126063668122957739)
  ·
    refine ⟨2505913689095502184436609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1670609126063668122957739 2505913689095502184436609)
    ·
      refine ⟨1879435266821626638327457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2505913689095502184436609 1879435266821626638327457)
      ·
        refine ⟨1409576450116219978745593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1879435266821626638327457 1409576450116219978745593)
        ·
          refine ⟨1057182337587164984059195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409576450116219978745593 1057182337587164984059195)
          ·
            refine ⟨1585773506380747476088793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057182337587164984059195 1585773506380747476088793)
            ·
              refine ⟨1189330129785560607066595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585773506380747476088793 1189330129785560607066595)
              ·
                refine ⟨1783995194678340910599893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189330129785560607066595 1783995194678340910599893)
                ·
                  refine ⟨41812387375273615092185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1783995194678340910599893 41812387375273615092185)
                  ·
                    rfl

theorem cell20_91608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_91608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91608 prefixEnd_91608 := by exact prefixLift 91608
  have htrace : WordTrace (prefixWord ++ tailWord_91608) baseStart_91608 baseEnd_91608 := by
    simpa [prefixWord, tailWord_91608, baseEnd_91608] using wordTrace_append hprefix tailTrace_91608
  have hstable : (prefixWord ++ tailWord_91608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91608).length < 2 ^ (prefixWord ++ tailWord_91608).sum := by decide
  have hdescent : baseEnd_91608 < baseStart_91608 := by decide
  rcases family_descends (prefixWord ++ tailWord_91608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91649 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 4]
def baseStart_91649 : Nat := 118140960795 + 91649 * 2 ^ 59
def prefixEnd_91649 : Nat := 4983230072969 + 3 ^ 40 * 91649 * 2
def baseEnd_91649 : Nat := 41831100892459694725351

theorem tailTrace_91649 : CollatzResearch.WordTrace tailWord_91649 prefixEnd_91649 41831100892459694725351 := by
  unfold tailWord_91649
  simp only [CollatzResearch.WordTrace]
  refine ⟨3342713644978800248158001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2228475763319200165438667 3342713644978800248158001)
  ·
    refine ⟨2507035233734100186118501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3342713644978800248158001 2507035233734100186118501)
    ·
      refine ⟨470069106325143784897219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2507035233734100186118501 470069106325143784897219)
      ·
        refine ⟨705103659487715677345829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470069106325143784897219 705103659487715677345829)
        ·
          refine ⟨132206936153946689502343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 705103659487715677345829 132206936153946689502343)
          ·
            refine ⟨198310404230920034253515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132206936153946689502343 198310404230920034253515)
            ·
              refine ⟨297465606346380051380273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198310404230920034253515 297465606346380051380273)
              ·
                refine ⟨223099204759785038535205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297465606346380051380273 223099204759785038535205)
                ·
                  refine ⟨41831100892459694725351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223099204759785038535205 41831100892459694725351)
                  ·
                    rfl

theorem cell20_91649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_91649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91649 prefixEnd_91649 := by exact prefixLift 91649
  have htrace : WordTrace (prefixWord ++ tailWord_91649) baseStart_91649 baseEnd_91649 := by
    simpa [prefixWord, tailWord_91649, baseEnd_91649] using wordTrace_append hprefix tailTrace_91649
  have hstable : (prefixWord ++ tailWord_91649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91649).length < 2 ^ (prefixWord ++ tailWord_91649).sum := by decide
  have hdescent : baseEnd_91649 < baseStart_91649 := by decide
  rcases family_descends (prefixWord ++ tailWord_91649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91677 : List Nat := [1, 4, 2, 2, 1, 1, 9]
def baseStart_91677 : Nat := 118140960795 + 91677 * 2 ^ 59
def prefixEnd_91677 : Nat := 4983230072969 + 3 ^ 40 * 91677 * 2
def baseEnd_91677 : Nat := 4649320095046226865767

theorem tailTrace_91677 : CollatzResearch.WordTrace tailWord_91677 prefixEnd_91677 4649320095046226865767 := by
  unfold tailWord_91677
  simp only [CollatzResearch.WordTrace]
  refine ⟨3343734888877361030177285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2229156592584907353451523 3343734888877361030177285)
  ·
    refine ⟨626950291664505193158241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3343734888877361030177285 626950291664505193158241)
    ·
      refine ⟨470212718748378894868681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626950291664505193158241 470212718748378894868681)
      ·
        refine ⟨352659539061284171151511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470212718748378894868681 352659539061284171151511)
        ·
          refine ⟨528989308591926256727267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352659539061284171151511 528989308591926256727267)
          ·
            refine ⟨793483962887889385090901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528989308591926256727267 793483962887889385090901)
            ·
              refine ⟨4649320095046226865767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 793483962887889385090901 4649320095046226865767)
              ·
                rfl

theorem cell20_91677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_91677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91677 prefixEnd_91677 := by exact prefixLift 91677
  have htrace : WordTrace (prefixWord ++ tailWord_91677) baseStart_91677 baseEnd_91677 := by
    simpa [prefixWord, tailWord_91677, baseEnd_91677] using wordTrace_append hprefix tailTrace_91677
  have hstable : (prefixWord ++ tailWord_91677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91677).length < 2 ^ (prefixWord ++ tailWord_91677).sum := by decide
  have hdescent : baseEnd_91677 < baseStart_91677 := by decide
  rcases family_descends (prefixWord ++ tailWord_91677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91680 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_91680 : Nat := 118140960795 + 91680 * 2 ^ 59
def prefixEnd_91680 : Nat := 4983230072969 + 3 ^ 40 * 91680 * 2
def baseEnd_91680 : Nat := 41845250137161364691891

theorem tailTrace_91680 : CollatzResearch.WordTrace tailWord_91680 prefixEnd_91680 41845250137161364691891 := by
  unfold tailWord_91680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671922153933246271268247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2229229538577661695024329 1671922153933246271268247)
  ·
    refine ⟨2507883230899869406902371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671922153933246271268247 2507883230899869406902371)
    ·
      refine ⟨3761824846349804110353557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507883230899869406902371 3761824846349804110353557)
      ·
        refine ⟨176335539672647067672823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3761824846349804110353557 176335539672647067672823)
        ·
          refine ⟨264503309508970601509235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176335539672647067672823 264503309508970601509235)
          ·
            refine ⟨396754964263455902263853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264503309508970601509235 396754964263455902263853)
            ·
              refine ⟨148783111598795963348945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396754964263455902263853 148783111598795963348945)
              ·
                refine ⟨111587333699096972511709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148783111598795963348945 111587333699096972511709)
                ·
                  refine ⟨41845250137161364691891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111587333699096972511709 41845250137161364691891)
                  ·
                    rfl

theorem cell20_91680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_91680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91680 prefixEnd_91680 := by exact prefixLift 91680
  have htrace : WordTrace (prefixWord ++ tailWord_91680) baseStart_91680 baseEnd_91680 := by
    simpa [prefixWord, tailWord_91680, baseEnd_91680] using wordTrace_append hprefix tailTrace_91680
  have hstable : (prefixWord ++ tailWord_91680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91680).length < 2 ^ (prefixWord ++ tailWord_91680).sum := by decide
  have hdescent : baseEnd_91680 < baseStart_91680 := by decide
  rcases family_descends (prefixWord ++ tailWord_91680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91722 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_91722 : Nat := 118140960795 + 91722 * 2 ^ 59
def prefixEnd_91722 : Nat := 4983230072969 + 3 ^ 40 * 91722 * 2
def baseEnd_91722 : Nat := 41864420081595885291719

theorem tailTrace_91722 : CollatzResearch.WordTrace tailWord_91722 prefixEnd_91722 41864420081595885291719 := by
  unfold tailWord_91722
  simp only [CollatzResearch.WordTrace]
  refine ⟨836344043428583428891355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2230250782476222477043613 836344043428583428891355)
  ·
    refine ⟨1254516065142875143337033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 836344043428583428891355 1254516065142875143337033)
    ·
      refine ⟨940887048857156357502775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1254516065142875143337033 940887048857156357502775)
      ·
        refine ⟨1411330573285734536254163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940887048857156357502775 1411330573285734536254163)
        ·
          refine ⟨2116995859928601804381245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411330573285734536254163 2116995859928601804381245)
          ·
            refine ⟨793873447473225676642967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2116995859928601804381245 793873447473225676642967)
            ·
              refine ⟨1190810171209838514964451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793873447473225676642967 1190810171209838514964451)
              ·
                refine ⟨1786215256814757772446677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190810171209838514964451 1786215256814757772446677)
                ·
                  refine ⟨41864420081595885291719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1786215256814757772446677 41864420081595885291719)
                  ·
                    rfl

theorem cell20_91722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_91722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91722 prefixEnd_91722 := by exact prefixLift 91722
  have htrace : WordTrace (prefixWord ++ tailWord_91722) baseStart_91722 baseEnd_91722 := by
    simpa [prefixWord, tailWord_91722, baseEnd_91722] using wordTrace_append hprefix tailTrace_91722
  have hstable : (prefixWord ++ tailWord_91722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91722).length < 2 ^ (prefixWord ++ tailWord_91722).sum := by decide
  have hdescent : baseEnd_91722 < baseStart_91722 := by decide
  rcases family_descends (prefixWord ++ tailWord_91722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91767 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_91767 : Nat := 118140960795 + 91767 * 2 ^ 59
def prefixEnd_91767 : Nat := 4983230072969 + 3 ^ 40 * 91767 * 2
def baseEnd_91767 : Nat := 41884959307775728791535

theorem tailTrace_91767 : CollatzResearch.WordTrace tailWord_91767 prefixEnd_91767 41884959307775728791535 := by
  unfold tailWord_91767
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347017458551306400953555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2231344972367537600635703 3347017458551306400953555)
  ·
    refine ⟨5020526187826959601430333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3347017458551306400953555 5020526187826959601430333)
    ·
      refine ⟨1882697320435109850536375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5020526187826959601430333 1882697320435109850536375)
      ·
        refine ⟨2824045980652664775804563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882697320435109850536375 2824045980652664775804563)
        ·
          refine ⟨4236068970978997163706845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824045980652664775804563 4236068970978997163706845)
          ·
            refine ⟨1588525864117123936390067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4236068970978997163706845 1588525864117123936390067)
            ·
              refine ⟨2382788796175685904585101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588525864117123936390067 2382788796175685904585101)
              ·
                refine ⟨893545798565882214219413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2382788796175685904585101 893545798565882214219413)
                ·
                  refine ⟨41884959307775728791535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 893545798565882214219413 41884959307775728791535)
                  ·
                    rfl

theorem cell20_91767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_91767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91767 prefixEnd_91767 := by exact prefixLift 91767
  have htrace : WordTrace (prefixWord ++ tailWord_91767) baseStart_91767 baseEnd_91767 := by
    simpa [prefixWord, tailWord_91767, baseEnd_91767] using wordTrace_append hprefix tailTrace_91767
  have hstable : (prefixWord ++ tailWord_91767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91767).length < 2 ^ (prefixWord ++ tailWord_91767).sum := by decide
  have hdescent : baseEnd_91767 < baseStart_91767 := by decide
  rcases family_descends (prefixWord ++ tailWord_91767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91808 : List Nat := [2, 1, 1, 4, 3, 3, 1, 5]
def baseStart_91808 : Nat := 118140960795 + 91808 * 2 ^ 59
def prefixEnd_91808 : Nat := 4983230072969 + 3 ^ 40 * 91808 * 2
def baseEnd_91808 : Nat := 13967890941653936141567

theorem tailTrace_91808 : CollatzResearch.WordTrace tailWord_91808 prefixEnd_91808 13967890941653936141567 := by
  unfold tailWord_91808
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674256425701385201598039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2232341900935180268797385 1674256425701385201598039)
  ·
    refine ⟨2511384638552077802397059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1674256425701385201598039 2511384638552077802397059)
    ·
      refine ⟨3767076957828116703595589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2511384638552077802397059 3767076957828116703595589)
      ·
        refine ⟨706326929592771881924173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3767076957828116703595589 706326929592771881924173)
        ·
          refine ⟨264872598597289455721565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 706326929592771881924173 264872598597289455721565)
          ·
            refine ⟨99327224473983545895587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264872598597289455721565 99327224473983545895587)
            ·
              refine ⟨148990836710975318843381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99327224473983545895587 148990836710975318843381)
              ·
                refine ⟨13967890941653936141567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148990836710975318843381 13967890941653936141567)
                ·
                  rfl

theorem cell20_91808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_91808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91808 prefixEnd_91808 := by exact prefixLift 91808
  have htrace : WordTrace (prefixWord ++ tailWord_91808) baseStart_91808 baseEnd_91808 := by
    simpa [prefixWord, tailWord_91808, baseEnd_91808] using wordTrace_append hprefix tailTrace_91808
  have hstable : (prefixWord ++ tailWord_91808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91808).length < 2 ^ (prefixWord ++ tailWord_91808).sum := by decide
  have hdescent : baseEnd_91808 < baseStart_91808 := by decide
  rcases family_descends (prefixWord ++ tailWord_91808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91839 : List Nat := [1, 1, 2, 2, 2, 3, 4, 3, 2]
def baseStart_91839 : Nat := 118140960795 + 91839 * 2 ^ 59
def prefixEnd_91839 : Nat := 4983230072969 + 3 ^ 40 * 91839 * 2
def baseEnd_91839 : Nat := 41917822069663478391241

theorem tailTrace_91839 : CollatzResearch.WordTrace tailWord_91839 prefixEnd_91839 41917822069663478391241 := by
  unfold tailWord_91839
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349643514290462697574571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2233095676193641798383047 3349643514290462697574571)
  ·
    refine ⟨5024465271435694046361857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349643514290462697574571 5024465271435694046361857)
    ·
      refine ⟨3768348953576770534771393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5024465271435694046361857 3768348953576770534771393)
      ·
        refine ⟨2826261715182577901078545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3768348953576770534771393 2826261715182577901078545)
        ·
          refine ⟨2119696286386933425808909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826261715182577901078545 2119696286386933425808909)
          ·
            refine ⟨794886107395100034678341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2119696286386933425808909 794886107395100034678341)
            ·
              refine ⟨149041145136581256502189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 794886107395100034678341 149041145136581256502189)
              ·
                refine ⟨55890429426217971188321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149041145136581256502189 55890429426217971188321)
                ·
                  refine ⟨41917822069663478391241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55890429426217971188321 41917822069663478391241)
                  ·
                    rfl

theorem cell20_91839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 2].length) (baseStart_91839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91839 prefixEnd_91839 := by exact prefixLift 91839
  have htrace : WordTrace (prefixWord ++ tailWord_91839) baseStart_91839 baseEnd_91839 := by
    simpa [prefixWord, tailWord_91839, baseEnd_91839] using wordTrace_append hprefix tailTrace_91839
  have hstable : (prefixWord ++ tailWord_91839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91839).length < 2 ^ (prefixWord ++ tailWord_91839).sum := by decide
  have hdescent : baseEnd_91839 < baseStart_91839 := by decide
  rcases family_descends (prefixWord ++ tailWord_91839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91842 : List Nat := [3, 5, 1, 2, 1, 1, 7]
def baseStart_91842 : Nat := 118140960795 + 91842 * 2 ^ 59
def prefixEnd_91842 : Nat := 4983230072969 + 3 ^ 40 * 91842 * 2
def baseEnd_91842 : Nat := 4657687927934311254581

theorem tailTrace_91842 : CollatzResearch.WordTrace tailWord_91842 prefixEnd_91842 4657687927934311254581 := by
  unfold tailWord_91842
  simp only [CollatzResearch.WordTrace]
  refine ⟨837438233319898552483445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2233168622186396139955853 837438233319898552483445)
  ·
    refine ⟨78509834373740489295323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 837438233319898552483445 78509834373740489295323)
    ·
      refine ⟨117764751560610733942985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78509834373740489295323 117764751560610733942985)
      ·
        refine ⟨88323563670458050457239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117764751560610733942985 88323563670458050457239)
        ·
          refine ⟨132485345505687075685859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88323563670458050457239 132485345505687075685859)
          ·
            refine ⟨198728018258530613528789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132485345505687075685859 198728018258530613528789)
            ·
              refine ⟨4657687927934311254581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 198728018258530613528789 4657687927934311254581)
              ·
                rfl

theorem cell20_91842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 7].length) (baseStart_91842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91842 prefixEnd_91842 := by exact prefixLift 91842
  have htrace : WordTrace (prefixWord ++ tailWord_91842) baseStart_91842 baseEnd_91842 := by
    simpa [prefixWord, tailWord_91842, baseEnd_91842] using wordTrace_append hprefix tailTrace_91842
  have hstable : (prefixWord ++ tailWord_91842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91842).length < 2 ^ (prefixWord ++ tailWord_91842).sum := by decide
  have hdescent : baseEnd_91842 < baseStart_91842 := by decide
  rcases family_descends (prefixWord ++ tailWord_91842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91894 : List Nat := [5, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_91894 : Nat := 118140960795 + 91894 * 2 ^ 59
def prefixEnd_91894 : Nat := 4983230072969 + 3 ^ 40 * 91894 * 2
def baseEnd_91894 : Nat := 41942925568327731557683

theorem tailTrace_91894 : CollatzResearch.WordTrace tailWord_91894 prefixEnd_91894 41942925568327731557683 := by
  unfold tailWord_91894
  simp only [CollatzResearch.WordTrace]
  refine ⟨209478095568200443176671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2234433019394138060551157 209478095568200443176671)
  ·
    refine ⟨314217143352300664765007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209478095568200443176671 314217143352300664765007)
    ·
      refine ⟨471325715028450997147511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314217143352300664765007 471325715028450997147511)
      ·
        refine ⟨706988572542676495721267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471325715028450997147511 706988572542676495721267)
        ·
          refine ⟨1060482858814014743581901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706988572542676495721267 1060482858814014743581901)
          ·
            refine ⟨397681072055255528843213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1060482858814014743581901 397681072055255528843213)
            ·
              refine ⟨149130402020720823316205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397681072055255528843213 149130402020720823316205)
              ·
                refine ⟨55923900757770308743577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149130402020720823316205 55923900757770308743577)
                ·
                  refine ⟨41942925568327731557683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55923900757770308743577 41942925568327731557683)
                  ·
                    rfl

theorem cell20_91894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_91894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91894 prefixEnd_91894 := by exact prefixLift 91894
  have htrace : WordTrace (prefixWord ++ tailWord_91894) baseStart_91894 baseEnd_91894 := by
    simpa [prefixWord, tailWord_91894, baseEnd_91894] using wordTrace_append hprefix tailTrace_91894
  have hstable : (prefixWord ++ tailWord_91894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91894).length < 2 ^ (prefixWord ++ tailWord_91894).sum := by decide
  have hdescent : baseEnd_91894 < baseStart_91894 := by decide
  rcases family_descends (prefixWord ++ tailWord_91894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91911 : List Nat := [1, 1, 4, 4, 2, 1, 3, 2, 2]
def baseStart_91911 : Nat := 118140960795 + 91911 * 2 ^ 59
def prefixEnd_91911 : Nat := 4983230072969 + 3 ^ 40 * 91911 * 2
def baseEnd_91911 : Nat := 41950684831551227990947

theorem tailTrace_91911 : CollatzResearch.WordTrace tailWord_91911 prefixEnd_91911 41950684831551227990947 := by
  unfold tailWord_91911
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352269570029618994195587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2234846380019745996130391 3352269570029618994195587)
  ·
    refine ⟨5028404355044428491293381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352269570029618994195587 5028404355044428491293381)
    ·
      refine ⟨942825816570830342117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5028404355044428491293381 942825816570830342117509)
      ·
        refine ⟨176779840607030689147033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 942825816570830342117509 176779840607030689147033)
        ·
          refine ⟨132584880455273016860275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176779840607030689147033 132584880455273016860275)
          ·
            refine ⟨198877320682909525290413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132584880455273016860275 198877320682909525290413)
            ·
              refine ⟨74578995256091071983905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198877320682909525290413 74578995256091071983905)
              ·
                refine ⟨55934246442068303987929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74578995256091071983905 55934246442068303987929)
                ·
                  refine ⟨41950684831551227990947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55934246442068303987929 41950684831551227990947)
                  ·
                    rfl

theorem cell20_91911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 2].length) (baseStart_91911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91911 prefixEnd_91911 := by exact prefixLift 91911
  have htrace : WordTrace (prefixWord ++ tailWord_91911) baseStart_91911 baseEnd_91911 := by
    simpa [prefixWord, tailWord_91911, baseEnd_91911] using wordTrace_append hprefix tailTrace_91911
  have hstable : (prefixWord ++ tailWord_91911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91911).length < 2 ^ (prefixWord ++ tailWord_91911).sum := by decide
  have hdescent : baseEnd_91911 < baseStart_91911 := by decide
  rcases family_descends (prefixWord ++ tailWord_91911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91912 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_91912 : Nat := 118140960795 + 91912 * 2 ^ 59
def prefixEnd_91912 : Nat := 4983230072969 + 3 ^ 40 * 91912 * 2
def baseEnd_91912 : Nat := 41951141258799668957609

theorem tailTrace_91912 : CollatzResearch.WordTrace tailWord_91912 prefixEnd_91912 41951141258799668957609 := by
  unfold tailWord_91912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676153021512998082490995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2234870695350664109987993 1676153021512998082490995)
  ·
    refine ⟨2514229532269497123736493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676153021512998082490995 2514229532269497123736493)
    ·
      refine ⟨942836074601061421401185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2514229532269497123736493 942836074601061421401185)
      ·
        refine ⟨707127055950796066050889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942836074601061421401185 707127055950796066050889)
        ·
          refine ⟨530345291963097049538167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707127055950796066050889 530345291963097049538167)
          ·
            refine ⟨795517937944645574307251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530345291963097049538167 795517937944645574307251)
            ·
              refine ⟨1193276906916968361460877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795517937944645574307251 1193276906916968361460877)
              ·
                refine ⟨447478840093863135547829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193276906916968361460877 447478840093863135547829)
                ·
                  refine ⟨41951141258799668957609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 447478840093863135547829 41951141258799668957609)
                  ·
                    rfl

theorem cell20_91912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_91912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91912 prefixEnd_91912 := by exact prefixLift 91912
  have htrace : WordTrace (prefixWord ++ tailWord_91912) baseStart_91912 baseEnd_91912 := by
    simpa [prefixWord, tailWord_91912, baseEnd_91912] using wordTrace_append hprefix tailTrace_91912
  have hstable : (prefixWord ++ tailWord_91912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91912).length < 2 ^ (prefixWord ++ tailWord_91912).sum := by decide
  have hdescent : baseEnd_91912 < baseStart_91912 := by decide
  rcases family_descends (prefixWord ++ tailWord_91912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91917 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 3]
def baseStart_91917 : Nat := 118140960795 + 91917 * 2 ^ 59
def prefixEnd_91917 : Nat := 4983230072969 + 3 ^ 40 * 91917 * 2
def baseEnd_91917 : Nat := 41953423395041873790923

theorem tailTrace_91917 : CollatzResearch.WordTrace tailWord_91917 prefixEnd_91917 41953423395041873790923 := by
  unfold tailWord_91917
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352488408007882018914005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2234992272005254679276003 3352488408007882018914005)
  ·
    refine ⟨78573947062684734818297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3352488408007882018914005 78573947062684734818297)
    ·
      refine ⟨58930460297013551113723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78573947062684734818297 58930460297013551113723)
      ·
        refine ⟨88395690445520326670585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58930460297013551113723 88395690445520326670585)
        ·
          refine ⟨66296767834140245002939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88395690445520326670585 66296767834140245002939)
          ·
            refine ⟨99445151751210367504409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66296767834140245002939 99445151751210367504409)
            ·
              refine ⟨74583863813407775628307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99445151751210367504409 74583863813407775628307)
              ·
                refine ⟨111875795720111663442461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74583863813407775628307 111875795720111663442461)
                ·
                  refine ⟨41953423395041873790923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111875795720111663442461 41953423395041873790923)
                  ·
                    rfl

theorem cell20_91917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_91917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91917 prefixEnd_91917 := by exact prefixLift 91917
  have htrace : WordTrace (prefixWord ++ tailWord_91917) baseStart_91917 baseEnd_91917 := by
    simpa [prefixWord, tailWord_91917, baseEnd_91917] using wordTrace_append hprefix tailTrace_91917
  have hstable : (prefixWord ++ tailWord_91917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91917).length < 2 ^ (prefixWord ++ tailWord_91917).sum := by decide
  have hdescent : baseEnd_91917 < baseStart_91917 := by decide
  rcases family_descends (prefixWord ++ tailWord_91917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91919 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_91919 : Nat := 118140960795 + 91919 * 2 ^ 59
def prefixEnd_91919 : Nat := 4983230072969 + 3 ^ 40 * 91919 * 2
def baseEnd_91919 : Nat := 41954336249538755724247

theorem tailTrace_91919 : CollatzResearch.WordTrace tailWord_91919 prefixEnd_91919 41954336249538755724247 := by
  unfold tailWord_91919
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352561354000636360486811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2235040902667090906991207 3352561354000636360486811)
  ·
    refine ⟨5028842031000954540730217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352561354000636360486811 5028842031000954540730217)
    ·
      refine ⟨3771631523250715905547663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5028842031000954540730217 3771631523250715905547663)
      ·
        refine ⟨5657447284876073858321495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771631523250715905547663 5657447284876073858321495)
        ·
          refine ⟨8486170927314110787482243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657447284876073858321495 8486170927314110787482243)
          ·
            refine ⟨12729256390971166181223365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8486170927314110787482243 12729256390971166181223365)
            ·
              refine ⟨2386735573307093658979381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12729256390971166181223365 2386735573307093658979381)
              ·
                refine ⟨223756459997540030529317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2386735573307093658979381 223756459997540030529317)
                ·
                  refine ⟨41954336249538755724247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223756459997540030529317 41954336249538755724247)
                  ·
                    rfl

theorem cell20_91919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_91919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91919 prefixEnd_91919 := by exact prefixLift 91919
  have htrace : WordTrace (prefixWord ++ tailWord_91919) baseStart_91919 baseEnd_91919 := by
    simpa [prefixWord, tailWord_91919, baseEnd_91919] using wordTrace_append hprefix tailTrace_91919
  have hstable : (prefixWord ++ tailWord_91919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91919).length < 2 ^ (prefixWord ++ tailWord_91919).sum := by decide
  have hdescent : baseEnd_91919 < baseStart_91919 := by decide
  rcases family_descends (prefixWord ++ tailWord_91919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91922 : List Nat := [3, 2, 4, 1, 1, 1, 1, 7]
def baseStart_91922 : Nat := 118140960795 + 91922 * 2 ^ 59
def prefixEnd_91922 : Nat := 4983230072969 + 3 ^ 40 * 91922 * 2
def baseEnd_91922 : Nat := 13985235177094692874745

theorem tailTrace_91922 : CollatzResearch.WordTrace tailWord_91922 prefixEnd_91922 13985235177094692874745 := by
  unfold tailWord_91922
  simp only [CollatzResearch.WordTrace]
  refine ⟨838167693247441968211505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2235113848659845248564013 838167693247441968211505)
  ·
    refine ⟨628625769935581476158629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 838167693247441968211505 628625769935581476158629)
    ·
      refine ⟨117867331862921526779743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 628625769935581476158629 117867331862921526779743)
      ·
        refine ⟨176800997794382290169615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117867331862921526779743 176800997794382290169615)
        ·
          refine ⟨265201496691573435254423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176800997794382290169615 265201496691573435254423)
          ·
            refine ⟨397802245037360152881635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265201496691573435254423 397802245037360152881635)
            ·
              refine ⟨596703367556040229322453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397802245037360152881635 596703367556040229322453)
              ·
                refine ⟨13985235177094692874745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 596703367556040229322453 13985235177094692874745)
                ·
                  rfl

theorem cell20_91922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_91922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_91922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_91922 prefixEnd_91922 := by exact prefixLift 91922
  have htrace : WordTrace (prefixWord ++ tailWord_91922) baseStart_91922 baseEnd_91922 := by
    simpa [prefixWord, tailWord_91922, baseEnd_91922] using wordTrace_append hprefix tailTrace_91922
  have hstable : (prefixWord ++ tailWord_91922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91922).length < 2 ^ (prefixWord ++ tailWord_91922).sum := by decide
  have hdescent : baseEnd_91922 < baseStart_91922 := by decide
  rcases family_descends (prefixWord ++ tailWord_91922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92022 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_92022 : Nat := 118140960795 + 92022 * 2 ^ 59
def prefixEnd_92022 : Nat := 4983230072969 + 3 ^ 40 * 92022 * 2
def baseEnd_92022 : Nat := 42001348256128175290493

theorem tailTrace_92022 : CollatzResearch.WordTrace tailWord_92022 prefixEnd_92022 42001348256128175290493 := by
  unfold tailWord_92022
  simp only [CollatzResearch.WordTrace]
  refine ⟨209769879539217809467895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2237545381751656634324213 209769879539217809467895)
  ·
    refine ⟨314654819308826714201843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209769879539217809467895 314654819308826714201843)
    ·
      refine ⟨471982228963240071302765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314654819308826714201843 471982228963240071302765)
      ·
        refine ⟨176993335861215026738537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471982228963240071302765 176993335861215026738537)
        ·
          refine ⟨132745001895911270053903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176993335861215026738537 132745001895911270053903)
          ·
            refine ⟨199117502843866905080855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132745001895911270053903 199117502843866905080855)
            ·
              refine ⟨298676254265800357621283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199117502843866905080855 298676254265800357621283)
              ·
                refine ⟨448014381398700536431925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298676254265800357621283 448014381398700536431925)
                ·
                  refine ⟨42001348256128175290493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 448014381398700536431925 42001348256128175290493)
                  ·
                    rfl

theorem cell20_92022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_92022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92022 prefixEnd_92022 := by exact prefixLift 92022
  have htrace : WordTrace (prefixWord ++ tailWord_92022) baseStart_92022 baseEnd_92022 := by
    simpa [prefixWord, tailWord_92022, baseEnd_92022] using wordTrace_append hprefix tailTrace_92022
  have hstable : (prefixWord ++ tailWord_92022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92022).length < 2 ^ (prefixWord ++ tailWord_92022).sum := by decide
  have hdescent : baseEnd_92022 < baseStart_92022 := by decide
  rcases family_descends (prefixWord ++ tailWord_92022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92057 : List Nat := [1, 2, 1, 2, 1, 3, 6, 4]
def baseStart_92057 : Nat := 118140960795 + 92057 * 2 ^ 59
def prefixEnd_92057 : Nat := 4983230072969 + 3 ^ 40 * 92057 * 2
def baseEnd_92057 : Nat := 14005774403274536374561

theorem tailTrace_92057 : CollatzResearch.WordTrace tailWord_92057 prefixEnd_92057 14005774403274536374561 := by
  unfold tailWord_92057
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357594627500685929010425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2238396418333790619340283 3357594627500685929010425)
  ·
    refine ⟨2518195970625514446757819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3357594627500685929010425 2518195970625514446757819)
    ·
      refine ⟨3777293955938271670136729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2518195970625514446757819 3777293955938271670136729)
      ·
        refine ⟨2832970466953703752602547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3777293955938271670136729 2832970466953703752602547)
        ·
          refine ⟨4249455700430555628903821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832970466953703752602547 4249455700430555628903821)
          ·
            refine ⟨1593545887661458360838933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4249455700430555628903821 1593545887661458360838933)
            ·
              refine ⟨74697463484130860664325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1593545887661458360838933 74697463484130860664325)
              ·
                refine ⟨14005774403274536374561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74697463484130860664325 14005774403274536374561)
                ·
                  rfl

theorem cell20_92057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_92057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92057 prefixEnd_92057 := by exact prefixLift 92057
  have htrace : WordTrace (prefixWord ++ tailWord_92057) baseStart_92057 baseEnd_92057 := by
    simpa [prefixWord, tailWord_92057, baseEnd_92057] using wordTrace_append hprefix tailTrace_92057
  have hstable : (prefixWord ++ tailWord_92057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92057).length < 2 ^ (prefixWord ++ tailWord_92057).sum := by decide
  have hdescent : baseEnd_92057 < baseStart_92057 := by decide
  rcases family_descends (prefixWord ++ tailWord_92057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92063 : List Nat := [1, 1, 2, 5, 4, 1, 1, 3, 2]
def baseStart_92063 : Nat := 118140960795 + 92063 * 2 ^ 59
def prefixEnd_92063 : Nat := 4983230072969 + 3 ^ 40 * 92063 * 2
def baseEnd_92063 : Nat := 42020061773314254923659

theorem tailTrace_92063 : CollatzResearch.WordTrace tailWord_92063 prefixEnd_92063 42020061773314254923659 := by
  unfold tailWord_92063
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357813465478948953728843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2238542310319299302485895 3357813465478948953728843)
  ·
    refine ⟨5036720198218423430593265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357813465478948953728843 5036720198218423430593265)
    ·
      refine ⟨3777540148663817572944949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5036720198218423430593265 3777540148663817572944949)
      ·
        refine ⟨354144388937232897463589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3777540148663817572944949 354144388937232897463589)
        ·
          refine ⟨66402072925731168274423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354144388937232897463589 66402072925731168274423)
          ·
            refine ⟨99603109388596752411635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66402072925731168274423 99603109388596752411635)
            ·
              refine ⟨149404664082895128617453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99603109388596752411635 149404664082895128617453)
              ·
                refine ⟨56026749031085673231545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149404664082895128617453 56026749031085673231545)
                ·
                  refine ⟨42020061773314254923659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56026749031085673231545 42020061773314254923659)
                  ·
                    rfl

theorem cell20_92063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 2].length) (baseStart_92063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92063 prefixEnd_92063 := by exact prefixLift 92063
  have htrace : WordTrace (prefixWord ++ tailWord_92063) baseStart_92063 baseEnd_92063 := by
    simpa [prefixWord, tailWord_92063, baseEnd_92063] using wordTrace_append hprefix tailTrace_92063
  have hstable : (prefixWord ++ tailWord_92063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92063).length < 2 ^ (prefixWord ++ tailWord_92063).sum := by decide
  have hdescent : baseEnd_92063 < baseStart_92063 := by decide
  rcases family_descends (prefixWord ++ tailWord_92063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92171 : List Nat := [1, 1, 1, 1, 6, 1, 5, 4]
def baseStart_92171 : Nat := 118140960795 + 92171 * 2 ^ 59
def prefixEnd_92171 : Nat := 4983230072969 + 3 ^ 40 * 92171 * 2
def baseEnd_92171 : Nat := 14023118638715293107739

theorem tailTrace_92171 : CollatzResearch.WordTrace tailWord_92171 prefixEnd_92171 14023118638715293107739 := by
  unfold tailWord_92171
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361752549087683398660367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2241168366058455599106911 3361752549087683398660367)
  ·
    refine ⟨5042628823631525097990551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3361752549087683398660367 5042628823631525097990551)
    ·
      refine ⟨7563943235447287646985827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5042628823631525097990551 7563943235447287646985827)
      ·
        refine ⟨11345914853170931470478741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7563943235447287646985827 11345914853170931470478741)
        ·
          refine ⟨531839758742387412678691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11345914853170931470478741 531839758742387412678691)
          ·
            refine ⟨797759638113581119018037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531839758742387412678691 797759638113581119018037)
            ·
              refine ⟨74789966073148229907941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 797759638113581119018037 74789966073148229907941)
              ·
                refine ⟨14023118638715293107739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74789966073148229907941 14023118638715293107739)
                ·
                  rfl

theorem cell20_92171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_92171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92171 prefixEnd_92171 := by exact prefixLift 92171
  have htrace : WordTrace (prefixWord ++ tailWord_92171) baseStart_92171 baseEnd_92171 := by
    simpa [prefixWord, tailWord_92171, baseEnd_92171] using wordTrace_append hprefix tailTrace_92171
  have hstable : (prefixWord ++ tailWord_92171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92171).length < 2 ^ (prefixWord ++ tailWord_92171).sum := by decide
  have hdescent : baseEnd_92171 < baseStart_92171 := by decide
  rcases family_descends (prefixWord ++ tailWord_92171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92202 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_92202 : Nat := 118140960795 + 92202 * 2 ^ 59
def prefixEnd_92202 : Nat := 4983230072969 + 3 ^ 40 * 92202 * 2
def baseEnd_92202 : Nat := 42083505160847549289757

theorem tailTrace_92202 : CollatzResearch.WordTrace tailWord_92202 prefixEnd_92202 42083505160847549289757 := by
  unfold tailWord_92202
  simp only [CollatzResearch.WordTrace]
  refine ⟨840720802993843923259715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2241922141316917128692573 840720802993843923259715)
  ·
    refine ⟨1261081204490765884889573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840720802993843923259715 1261081204490765884889573)
    ·
      refine ⟨236452725842018603416795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1261081204490765884889573 236452725842018603416795)
      ·
        refine ⟨354679088763027905125193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236452725842018603416795 354679088763027905125193)
        ·
          refine ⟨266009316572270928843895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354679088763027905125193 266009316572270928843895)
          ·
            refine ⟨399013974858406393265843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266009316572270928843895 399013974858406393265843)
            ·
              refine ⟨598520962287609589898765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399013974858406393265843 598520962287609589898765)
              ·
                refine ⟨224445360857853596212037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 598520962287609589898765 224445360857853596212037)
                ·
                  refine ⟨42083505160847549289757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224445360857853596212037 42083505160847549289757)
                  ·
                    rfl

theorem cell20_92202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_92202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92202 prefixEnd_92202 := by exact prefixLift 92202
  have htrace : WordTrace (prefixWord ++ tailWord_92202) baseStart_92202 baseEnd_92202 := by
    simpa [prefixWord, tailWord_92202, baseEnd_92202] using wordTrace_append hprefix tailTrace_92202
  have hstable : (prefixWord ++ tailWord_92202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92202).length < 2 ^ (prefixWord ++ tailWord_92202).sum := by decide
  have hdescent : baseEnd_92202 < baseStart_92202 := by decide
  rcases family_descends (prefixWord ++ tailWord_92202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92222 : List Nat := [4, 2, 1, 3, 3, 1, 2, 4]
def baseStart_92222 : Nat := 118140960795 + 92222 * 2 ^ 59
def prefixEnd_92222 : Nat := 4983230072969 + 3 ^ 40 * 92222 * 2
def baseEnd_92222 : Nat := 14030877901938789541003

theorem tailTrace_92222 : CollatzResearch.WordTrace tailWord_92222 prefixEnd_92222 14030877901938789541003 := by
  unfold tailWord_92222
  simp only [CollatzResearch.WordTrace]
  refine ⟨420451583987864888595865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2242408447935279405844613 420451583987864888595865)
  ·
    refine ⟨315338687990898666446899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 420451583987864888595865 315338687990898666446899)
    ·
      refine ⟨473008031986347999670349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315338687990898666446899 473008031986347999670349)
      ·
        refine ⟨177378011994880499876381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473008031986347999670349 177378011994880499876381)
        ·
          refine ⟨66516754498080187453643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177378011994880499876381 66516754498080187453643)
          ·
            refine ⟨99775131747120281180465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66516754498080187453643 99775131747120281180465)
            ·
              refine ⟨74831348810340210885349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99775131747120281180465 74831348810340210885349)
              ·
                refine ⟨14030877901938789541003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74831348810340210885349 14030877901938789541003)
                ·
                  rfl

theorem cell20_92222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_92222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92222 prefixEnd_92222 := by exact prefixLift 92222
  have htrace : WordTrace (prefixWord ++ tailWord_92222) baseStart_92222 baseEnd_92222 := by
    simpa [prefixWord, tailWord_92222, baseEnd_92222] using wordTrace_append hprefix tailTrace_92222
  have hstable : (prefixWord ++ tailWord_92222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92222).length < 2 ^ (prefixWord ++ tailWord_92222).sum := by decide
  have hdescent : baseEnd_92222 < baseStart_92222 := by decide
  rcases family_descends (prefixWord ++ tailWord_92222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92223 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_92223 : Nat := 118140960795 + 92223 * 2 ^ 59
def prefixEnd_92223 : Nat := 4983230072969 + 3 ^ 40 * 92223 * 2
def baseEnd_92223 : Nat := 42093090133064809589671

theorem tailTrace_92223 : CollatzResearch.WordTrace tailWord_92223 prefixEnd_92223 42093090133064809589671 := by
  unfold tailWord_92223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3363649144899296279553323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2242432763266197519702215 3363649144899296279553323)
  ·
    refine ⟨5045473717348944419329985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3363649144899296279553323 5045473717348944419329985)
    ·
      refine ⟨3784105288011708314497489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5045473717348944419329985 3784105288011708314497489)
      ·
        refine ⟨2838078966008781235873117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3784105288011708314497489 2838078966008781235873117)
        ·
          refine ⟨1064279612253292963452419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2838078966008781235873117 1064279612253292963452419)
          ·
            refine ⟨1596419418379939445178629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064279612253292963452419 1596419418379939445178629)
            ·
              refine ⟨299328640946238645970993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1596419418379939445178629 299328640946238645970993)
              ·
                refine ⟨224496480709678984478245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299328640946238645970993 224496480709678984478245)
                ·
                  refine ⟨42093090133064809589671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224496480709678984478245 42093090133064809589671)
                  ·
                    rfl

theorem cell20_92223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_92223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92223 prefixEnd_92223 := by exact prefixLift 92223
  have htrace : WordTrace (prefixWord ++ tailWord_92223) baseStart_92223 baseEnd_92223 := by
    simpa [prefixWord, tailWord_92223, baseEnd_92223] using wordTrace_append hprefix tailTrace_92223
  have hstable : (prefixWord ++ tailWord_92223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92223).length < 2 ^ (prefixWord ++ tailWord_92223).sum := by decide
  have hdescent : baseEnd_92223 < baseStart_92223 := by decide
  rcases family_descends (prefixWord ++ tailWord_92223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92253 : List Nat := [1, 4, 4, 1, 1, 2, 3, 2, 2]
def baseStart_92253 : Nat := 118140960795 + 92253 * 2 ^ 59
def prefixEnd_92253 : Nat := 4983230072969 + 3 ^ 40 * 92253 * 2
def baseEnd_92253 : Nat := 42106782950518038589549

theorem tailTrace_92253 : CollatzResearch.WordTrace tailWord_92253 prefixEnd_92253 42106782950518038589549 := by
  unfold tailWord_92253
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364743334790611403145413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2243162223193740935430275 3364743334790611403145413)
  ·
    refine ⟨630889375273239638089765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3364743334790611403145413 630889375273239638089765)
    ·
      refine ⟨118291757863732432141831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 630889375273239638089765 118291757863732432141831)
      ·
        refine ⟨177437636795598648212747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118291757863732432141831 177437636795598648212747)
        ·
          refine ⟨266156455193397972319121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177437636795598648212747 266156455193397972319121)
          ·
            refine ⟨199617341395048479239341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266156455193397972319121 199617341395048479239341)
            ·
              refine ⟨74856503023143179714753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199617341395048479239341 74856503023143179714753)
              ·
                refine ⟨56142377267357384786065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74856503023143179714753 56142377267357384786065)
                ·
                  refine ⟨42106782950518038589549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56142377267357384786065 42106782950518038589549)
                  ·
                    rfl

theorem cell20_92253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_92253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92253 prefixEnd_92253 := by exact prefixLift 92253
  have htrace : WordTrace (prefixWord ++ tailWord_92253) baseStart_92253 baseEnd_92253 := by
    simpa [prefixWord, tailWord_92253, baseEnd_92253] using wordTrace_append hprefix tailTrace_92253
  have hstable : (prefixWord ++ tailWord_92253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92253).length < 2 ^ (prefixWord ++ tailWord_92253).sum := by decide
  have hdescent : baseEnd_92253 < baseStart_92253 := by decide
  rcases family_descends (prefixWord ++ tailWord_92253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92268 : List Nat := [2, 2, 1, 1, 3, 3, 1, 7]
def baseStart_92268 : Nat := 118140960795 + 92268 * 2 ^ 59
def prefixEnd_92268 : Nat := 4983230072969 + 3 ^ 40 * 92268 * 2
def baseEnd_92268 : Nat := 14037876453081551029829

theorem tailTrace_92268 : CollatzResearch.WordTrace tailWord_92268 prefixEnd_92268 14037876453081551029829 := by
  unfold tailWord_92268
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682645214868134482470729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2243526953157512643294305 1682645214868134482470729)
  ·
    refine ⟨1261983911151100861853047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1682645214868134482470729 1261983911151100861853047)
    ·
      refine ⟨1892975866726651292779571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261983911151100861853047 1892975866726651292779571)
      ·
        refine ⟨2839463800089976939169357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892975866726651292779571 2839463800089976939169357)
        ·
          refine ⟨1064798925033741352188509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2839463800089976939169357 1064798925033741352188509)
          ·
            refine ⟨399299596887653007070691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1064798925033741352188509 399299596887653007070691)
            ·
              refine ⟨598949395331479510606037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399299596887653007070691 598949395331479510606037)
              ·
                refine ⟨14037876453081551029829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 598949395331479510606037 14037876453081551029829)
                ·
                  rfl

theorem cell20_92268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_92268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92268 prefixEnd_92268 := by exact prefixLift 92268
  have htrace : WordTrace (prefixWord ++ tailWord_92268) baseStart_92268 baseEnd_92268 := by
    simpa [prefixWord, tailWord_92268, baseEnd_92268] using wordTrace_append hprefix tailTrace_92268
  have hstable : (prefixWord ++ tailWord_92268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92268).length < 2 ^ (prefixWord ++ tailWord_92268).sum := by decide
  have hdescent : baseEnd_92268 < baseStart_92268 := by decide
  rcases family_descends (prefixWord ++ tailWord_92268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92271 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 3]
def baseStart_92271 : Nat := 118140960795 + 92271 * 2 ^ 59
def prefixEnd_92271 : Nat := 4983230072969 + 3 ^ 40 * 92271 * 2
def baseEnd_92271 : Nat := 42114998640989975989475

theorem tailTrace_92271 : CollatzResearch.WordTrace tailWord_92271 prefixEnd_92271 42114998640989975989475 := by
  unfold tailWord_92271
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365399848725400477300667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2243599899150266984867111 3365399848725400477300667)
  ·
    refine ⟨5048099773088100715951001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3365399848725400477300667 5048099773088100715951001)
    ·
      refine ⟨3786074829816075536963251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5048099773088100715951001 3786074829816075536963251)
      ·
        refine ⟨5679112244724113305444877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786074829816075536963251 5679112244724113305444877)
        ·
          refine ⟨2129667091771542489541829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5679112244724113305444877 2129667091771542489541829)
          ·
            refine ⟨399312579707164216789093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2129667091771542489541829 399312579707164216789093)
            ·
              refine ⟨74871108695093290647955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399312579707164216789093 74871108695093290647955)
              ·
                refine ⟨112306663042639935971933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74871108695093290647955 112306663042639935971933)
                ·
                  refine ⟨42114998640989975989475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112306663042639935971933 42114998640989975989475)
                  ·
                    rfl

theorem cell20_92271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 3].length) (baseStart_92271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92271 prefixEnd_92271 := by exact prefixLift 92271
  have htrace : WordTrace (prefixWord ++ tailWord_92271) baseStart_92271 baseEnd_92271 := by
    simpa [prefixWord, tailWord_92271, baseEnd_92271] using wordTrace_append hprefix tailTrace_92271
  have hstable : (prefixWord ++ tailWord_92271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92271).length < 2 ^ (prefixWord ++ tailWord_92271).sum := by decide
  have hdescent : baseEnd_92271 < baseStart_92271 := by decide
  rcases family_descends (prefixWord ++ tailWord_92271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92308 : List Nat := [2, 4, 2, 3, 1, 2, 2, 2, 2]
def baseStart_92308 : Nat := 118140960795 + 92308 * 2 ^ 59
def prefixEnd_92308 : Nat := 4983230072969 + 3 ^ 40 * 92308 * 2
def baseEnd_92308 : Nat := 42131886449182291755991

theorem tailTrace_92308 : CollatzResearch.WordTrace tailWord_92308 prefixEnd_92308 42131886449182291755991 := by
  unfold tailWord_92308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683374674795677898198789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2244499566394237197598385 1683374674795677898198789)
  ·
    refine ⟨315632751524189605912273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1683374674795677898198789 315632751524189605912273)
    ·
      refine ⟨236724563643142204434205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315632751524189605912273 236724563643142204434205)
      ·
        refine ⟨88771711366178326662827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236724563643142204434205 88771711366178326662827)
        ·
          refine ⟨133157567049267489994241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88771711366178326662827 133157567049267489994241)
          ·
            refine ⟨99868175286950617495681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133157567049267489994241 99868175286950617495681)
            ·
              refine ⟨74901131465212963121761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99868175286950617495681 74901131465212963121761)
              ·
                refine ⟨56175848598909722341321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74901131465212963121761 56175848598909722341321)
                ·
                  refine ⟨42131886449182291755991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56175848598909722341321 42131886449182291755991)
                  ·
                    rfl

theorem cell20_92308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_92308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92308 prefixEnd_92308 := by exact prefixLift 92308
  have htrace : WordTrace (prefixWord ++ tailWord_92308) baseStart_92308 baseEnd_92308 := by
    simpa [prefixWord, tailWord_92308, baseEnd_92308] using wordTrace_append hprefix tailTrace_92308
  have hstable : (prefixWord ++ tailWord_92308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92308).length < 2 ^ (prefixWord ++ tailWord_92308).sum := by decide
  have hdescent : baseEnd_92308 < baseStart_92308 := by decide
  rcases family_descends (prefixWord ++ tailWord_92308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92313 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_92313 : Nat := 118140960795 + 92313 * 2 ^ 59
def prefixEnd_92313 : Nat := 4983230072969 + 3 ^ 40 * 92313 * 2
def baseEnd_92313 : Nat := 42134168585424496589303

theorem tailTrace_92313 : CollatzResearch.WordTrace tailWord_92313 prefixEnd_92313 42134168585424496589303 := by
  unfold tailWord_92313
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366931714573241650329593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2244621143048827766886395 3366931714573241650329593)
  ·
    refine ⟨2525198785929931237747195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3366931714573241650329593 2525198785929931237747195)
    ·
      refine ⟨3787798178894896856620793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2525198785929931237747195 3787798178894896856620793)
      ·
        refine ⟨2840848634171172642465595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3787798178894896856620793 2840848634171172642465595)
        ·
          refine ⟨4261272951256758963698393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840848634171172642465595 4261272951256758963698393)
          ·
            refine ⟨3195954713442569222773795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261272951256758963698393 3195954713442569222773795)
            ·
              refine ⟨4793932070163853834160693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195954713442569222773795 4793932070163853834160693)
              ·
                refine ⟨449431131577861296952565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4793932070163853834160693 449431131577861296952565)
                ·
                  refine ⟨42134168585424496589303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 449431131577861296952565 42134168585424496589303)
                  ·
                    rfl

theorem cell20_92313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_92313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92313 prefixEnd_92313 := by exact prefixLift 92313
  have htrace : WordTrace (prefixWord ++ tailWord_92313) baseStart_92313 baseEnd_92313 := by
    simpa [prefixWord, tailWord_92313, baseEnd_92313] using wordTrace_append hprefix tailTrace_92313
  have hstable : (prefixWord ++ tailWord_92313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92313).length < 2 ^ (prefixWord ++ tailWord_92313).sum := by decide
  have hdescent : baseEnd_92313 < baseStart_92313 := by decide
  rcases family_descends (prefixWord ++ tailWord_92313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92350 : List Nat := [4, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_92350 : Nat := 118140960795 + 92350 * 2 ^ 59
def prefixEnd_92350 : Nat := 4983230072969 + 3 ^ 40 * 92350 * 2
def baseEnd_92350 : Nat := 42151056393616812355819

theorem tailTrace_92350 : CollatzResearch.WordTrace tailWord_92350 prefixEnd_92350 42151056393616812355819 := by
  unfold tailWord_92350
  simp only [CollatzResearch.WordTrace]
  refine ⟨421035151929899621178313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2245520810292797979617669 421035151929899621178313)
  ·
    refine ⟨315776363947424715883735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 421035151929899621178313 315776363947424715883735)
    ·
      refine ⟨473664545921137073825603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315776363947424715883735 473664545921137073825603)
      ·
        refine ⟨710496818881705610738405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473664545921137073825603 710496818881705610738405)
        ·
          refine ⟨133218153540319802013451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 710496818881705610738405 133218153540319802013451)
          ·
            refine ⟨199827230310479703020177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133218153540319802013451 199827230310479703020177)
            ·
              refine ⟨149870422732859777265133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199827230310479703020177 149870422732859777265133)
              ·
                refine ⟨56201408524822416474425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149870422732859777265133 56201408524822416474425)
                ·
                  refine ⟨42151056393616812355819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56201408524822416474425 42151056393616812355819)
                  ·
                    rfl

theorem cell20_92350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_92350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92350 prefixEnd_92350 := by exact prefixLift 92350
  have htrace : WordTrace (prefixWord ++ tailWord_92350) baseStart_92350 baseEnd_92350 := by
    simpa [prefixWord, tailWord_92350, baseEnd_92350] using wordTrace_append hprefix tailTrace_92350
  have hstable : (prefixWord ++ tailWord_92350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92350).length < 2 ^ (prefixWord ++ tailWord_92350).sum := by decide
  have hdescent : baseEnd_92350 < baseStart_92350 := by decide
  rcases family_descends (prefixWord ++ tailWord_92350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92351 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_92351 : Nat := 118140960795 + 92351 * 2 ^ 59
def prefixEnd_92351 : Nat := 4983230072969 + 3 ^ 40 * 92351 * 2
def baseEnd_92351 : Nat := 42151512820865253322481

theorem tailTrace_92351 : CollatzResearch.WordTrace tailWord_92351 prefixEnd_92351 42151512820865253322481 := by
  unfold tailWord_92351
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368317688435574140212907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2245545125623716093475271 3368317688435574140212907)
  ·
    refine ⟨5052476532653361210319361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3368317688435574140212907 5052476532653361210319361)
    ·
      refine ⟨3789357399490020907739521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5052476532653361210319361 3789357399490020907739521)
      ·
        refine ⟨2842018049617515680804641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3789357399490020907739521 2842018049617515680804641)
        ·
          refine ⟨2131513537213136760603481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2842018049617515680804641 2131513537213136760603481)
          ·
            refine ⟨1598635152909852570452611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2131513537213136760603481 1598635152909852570452611)
            ·
              refine ⟨2397952729364778855678917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598635152909852570452611 2397952729364778855678917)
              ·
                refine ⟨449616136755896035439797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2397952729364778855678917 449616136755896035439797)
                ·
                  refine ⟨42151512820865253322481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 449616136755896035439797 42151512820865253322481)
                  ·
                    rfl

theorem cell20_92351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_92351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92351 prefixEnd_92351 := by exact prefixLift 92351
  have htrace : WordTrace (prefixWord ++ tailWord_92351) baseStart_92351 baseEnd_92351 := by
    simpa [prefixWord, tailWord_92351, baseEnd_92351] using wordTrace_append hprefix tailTrace_92351
  have hstable : (prefixWord ++ tailWord_92351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92351).length < 2 ^ (prefixWord ++ tailWord_92351).sum := by decide
  have hdescent : baseEnd_92351 < baseStart_92351 := by decide
  rcases family_descends (prefixWord ++ tailWord_92351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92385 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 3]
def baseStart_92385 : Nat := 118140960795 + 92385 * 2 ^ 59
def prefixEnd_92385 : Nat := 4983230072969 + 3 ^ 40 * 92385 * 2
def baseEnd_92385 : Nat := 42167031347312246189009

theorem tailTrace_92385 : CollatzResearch.WordTrace tailWord_92385 prefixEnd_92385 42167031347312246189009 := by
  unfold tailWord_92385
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369557770312397946950609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2246371846874931964633739 3369557770312397946950609)
  ·
    refine ⟨2527168327734298460212957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3369557770312397946950609 2527168327734298460212957)
    ·
      refine ⟨947688122900361922579859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2527168327734298460212957 947688122900361922579859)
      ·
        refine ⟨1421532184350542883869789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947688122900361922579859 1421532184350542883869789)
        ·
          refine ⟨533074569131453581451171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1421532184350542883869789 533074569131453581451171)
          ·
            refine ⟨799611853697180372176757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533074569131453581451171 799611853697180372176757)
            ·
              refine ⟨74963611284110659891571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 799611853697180372176757 74963611284110659891571)
              ·
                refine ⟨112445416926165989837357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74963611284110659891571 112445416926165989837357)
                ·
                  refine ⟨42167031347312246189009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112445416926165989837357 42167031347312246189009)
                  ·
                    rfl

theorem cell20_92385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_92385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92385 prefixEnd_92385 := by exact prefixLift 92385
  have htrace : WordTrace (prefixWord ++ tailWord_92385) baseStart_92385 baseEnd_92385 := by
    simpa [prefixWord, tailWord_92385, baseEnd_92385] using wordTrace_append hprefix tailTrace_92385
  have hstable : (prefixWord ++ tailWord_92385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92385).length < 2 ^ (prefixWord ++ tailWord_92385).sum := by decide
  have hdescent : baseEnd_92385 < baseStart_92385 := by decide
  rcases family_descends (prefixWord ++ tailWord_92385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92399 : List Nat := [1, 1, 2, 1, 6, 1, 4, 4]
def baseStart_92399 : Nat := 118140960795 + 92399 * 2 ^ 59
def prefixEnd_92399 : Nat := 4983230072969 + 3 ^ 40 * 92399 * 2
def baseEnd_92399 : Nat := 14057807109596806574095

theorem tailTrace_92399 : CollatzResearch.WordTrace tailWord_92399 prefixEnd_92399 14057807109596806574095 := by
  unfold tailWord_92399
  simp only [CollatzResearch.WordTrace]
  refine ⟨3370068392261678337960251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2246712261507785558640167 3370068392261678337960251)
  ·
    refine ⟨5055102588392517506940377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3370068392261678337960251 5055102588392517506940377)
    ·
      refine ⟨3791326941294388130205283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5055102588392517506940377 3791326941294388130205283)
      ·
        refine ⟨5686990411941582195307925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791326941294388130205283 5686990411941582195307925)
        ·
          refine ⟨266577675559761665405059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5686990411941582195307925 266577675559761665405059)
          ·
            refine ⟨399866513339642498107589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266577675559761665405059 399866513339642498107589)
            ·
              refine ⟨74974971251182968395173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399866513339642498107589 74974971251182968395173)
              ·
                refine ⟨14057807109596806574095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74974971251182968395173 14057807109596806574095)
                ·
                  rfl

theorem cell20_92399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_92399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92399 prefixEnd_92399 := by exact prefixLift 92399
  have htrace : WordTrace (prefixWord ++ tailWord_92399) baseStart_92399 baseEnd_92399 := by
    simpa [prefixWord, tailWord_92399, baseEnd_92399] using wordTrace_append hprefix tailTrace_92399
  have hstable : (prefixWord ++ tailWord_92399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92399).length < 2 ^ (prefixWord ++ tailWord_92399).sum := by decide
  have hdescent : baseEnd_92399 < baseStart_92399 := by decide
  rcases family_descends (prefixWord ++ tailWord_92399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92406 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_92406 : Nat := 118140960795 + 92406 * 2 ^ 59
def prefixEnd_92406 : Nat := 4983230072969 + 3 ^ 40 * 92406 * 2
def baseEnd_92406 : Nat := 42176616319529506488923

theorem tailTrace_92406 : CollatzResearch.WordTrace tailWord_92406 prefixEnd_92406 42176616319529506488923 := by
  unfold tailWord_92406
  simp only [CollatzResearch.WordTrace]
  refine ⟨210645231452269908341567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2246882468824212355643381 210645231452269908341567)
  ·
    refine ⟨315967847178404862512351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210645231452269908341567 315967847178404862512351)
    ·
      refine ⟨473951770767607293768527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315967847178404862512351 473951770767607293768527)
      ·
        refine ⟨710927656151410940652791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473951770767607293768527 710927656151410940652791)
        ·
          refine ⟨1066391484227116410979187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710927656151410940652791 1066391484227116410979187)
          ·
            refine ⟨1599587226340674616468781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066391484227116410979187 1599587226340674616468781)
            ·
              refine ⟨599845209877752981175793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1599587226340674616468781 599845209877752981175793)
              ·
                refine ⟨449883907408314735881845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599845209877752981175793 449883907408314735881845)
                ·
                  refine ⟨42176616319529506488923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 449883907408314735881845 42176616319529506488923)
                  ·
                    rfl

theorem cell20_92406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_92406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92406 prefixEnd_92406 := by exact prefixLift 92406
  have htrace : WordTrace (prefixWord ++ tailWord_92406) baseStart_92406 baseEnd_92406 := by
    simpa [prefixWord, tailWord_92406, baseEnd_92406] using wordTrace_append hprefix tailTrace_92406
  have hstable : (prefixWord ++ tailWord_92406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92406).length < 2 ^ (prefixWord ++ tailWord_92406).sum := by decide
  have hdescent : baseEnd_92406 < baseStart_92406 := by decide
  rcases family_descends (prefixWord ++ tailWord_92406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92427 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_92427 : Nat := 118140960795 + 92427 * 2 ^ 59
def prefixEnd_92427 : Nat := 4983230072969 + 3 ^ 40 * 92427 * 2
def baseEnd_92427 : Nat := 42186201291746766788837

theorem tailTrace_92427 : CollatzResearch.WordTrace tailWord_92427 prefixEnd_92427 42186201291746766788837 := by
  unfold tailWord_92427
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371089636160239119979535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2247393090773492746653023 3371089636160239119979535)
  ·
    refine ⟨5056634454240358679969303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371089636160239119979535 5056634454240358679969303)
    ·
      refine ⟨7584951681360538019953955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5056634454240358679969303 7584951681360538019953955)
      ·
        refine ⟨11377427522040807029930933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584951681360538019953955 11377427522040807029930933)
        ·
          refine ⟨1066633830191325659056025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11377427522040807029930933 1066633830191325659056025)
          ·
            refine ⟨799975372643494244292019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066633830191325659056025 799975372643494244292019)
            ·
              refine ⟨1199963058965241366438029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799975372643494244292019 1199963058965241366438029)
              ·
                refine ⟨449986147111965512414261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1199963058965241366438029 449986147111965512414261)
                ·
                  refine ⟨42186201291746766788837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 449986147111965512414261 42186201291746766788837)
                  ·
                    rfl

theorem cell20_92427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_92427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92427 prefixEnd_92427 := by exact prefixLift 92427
  have htrace : WordTrace (prefixWord ++ tailWord_92427) baseStart_92427 baseEnd_92427 := by
    simpa [prefixWord, tailWord_92427, baseEnd_92427] using wordTrace_append hprefix tailTrace_92427
  have hstable : (prefixWord ++ tailWord_92427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92427).length < 2 ^ (prefixWord ++ tailWord_92427).sum := by decide
  have hdescent : baseEnd_92427 < baseStart_92427 := by decide
  rcases family_descends (prefixWord ++ tailWord_92427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92481 : List Nat := [1, 2, 5, 2, 2, 2, 2, 2, 2]
def baseStart_92481 : Nat := 118140960795 + 92481 * 2 ^ 59
def prefixEnd_92481 : Nat := 4983230072969 + 3 ^ 40 * 92481 * 2
def baseEnd_92481 : Nat := 42210848363162578988617

theorem tailTrace_92481 : CollatzResearch.WordTrace tailWord_92481 prefixEnd_92481 42210848363162578988617 := by
  unfold tailWord_92481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373059177964606342445297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2248706118643070894963531 3373059177964606342445297)
  ·
    refine ⟨2529794383473454756833973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3373059177964606342445297 2529794383473454756833973)
    ·
      refine ⟨237168223450636383453185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2529794383473454756833973 237168223450636383453185)
      ·
        refine ⟨177876167587977287589889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237168223450636383453185 177876167587977287589889)
        ·
          refine ⟨133407125690982965692417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177876167587977287589889 133407125690982965692417)
          ·
            refine ⟨100055344268237224269313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133407125690982965692417 100055344268237224269313)
            ·
              refine ⟨75041508201177918201985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100055344268237224269313 75041508201177918201985)
              ·
                refine ⟨56281131150883438651489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75041508201177918201985 56281131150883438651489)
                ·
                  refine ⟨42210848363162578988617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56281131150883438651489 42210848363162578988617)
                  ·
                    rfl

theorem cell20_92481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_92481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92481 prefixEnd_92481 := by exact prefixLift 92481
  have htrace : WordTrace (prefixWord ++ tailWord_92481) baseStart_92481 baseEnd_92481 := by
    simpa [prefixWord, tailWord_92481, baseEnd_92481] using wordTrace_append hprefix tailTrace_92481
  have hstable : (prefixWord ++ tailWord_92481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92481).length < 2 ^ (prefixWord ++ tailWord_92481).sum := by decide
  have hdescent : baseEnd_92481 < baseStart_92481 := by decide
  rcases family_descends (prefixWord ++ tailWord_92481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92496 : List Nat := [2, 1, 1, 1, 1, 6, 3, 5]
def baseStart_92496 : Nat := 118140960795 + 92496 * 2 ^ 59
def prefixEnd_92496 : Nat := 4983230072969 + 3 ^ 40 * 92496 * 2
def baseEnd_92496 : Nat := 14072564923963064496185

theorem tailTrace_92496 : CollatzResearch.WordTrace tailWord_92496 prefixEnd_92496 14072564923963064496185 := by
  unfold tailWord_92496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686803136455131952120671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2249070848606842602827561 1686803136455131952120671)
  ·
    refine ⟨2530204704682697928181007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1686803136455131952120671 2530204704682697928181007)
    ·
      refine ⟨3795307057024046892271511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530204704682697928181007 3795307057024046892271511)
      ·
        refine ⟨5692960585536070338407267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795307057024046892271511 5692960585536070338407267)
        ·
          refine ⟨8539440878304105507610901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5692960585536070338407267 8539440878304105507610901)
          ·
            refine ⟨400286291170504945669261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8539440878304105507610901 400286291170504945669261)
            ·
              refine ⟨150107359188939354625973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400286291170504945669261 150107359188939354625973)
              ·
                refine ⟨14072564923963064496185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150107359188939354625973 14072564923963064496185)
                ·
                  rfl

theorem cell20_92496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_92496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92496 prefixEnd_92496 := by exact prefixLift 92496
  have htrace : WordTrace (prefixWord ++ tailWord_92496) baseStart_92496 baseEnd_92496 := by
    simpa [prefixWord, tailWord_92496, baseEnd_92496] using wordTrace_append hprefix tailTrace_92496
  have hstable : (prefixWord ++ tailWord_92496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92496).length < 2 ^ (prefixWord ++ tailWord_92496).sum := by decide
  have hdescent : baseEnd_92496 < baseStart_92496 := by decide
  rcases family_descends (prefixWord ++ tailWord_92496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92568 : List Nat := [2, 1, 2, 5, 1, 3, 2, 4]
def baseStart_92568 : Nat := 118140960795 + 92568 * 2 ^ 59
def prefixEnd_92568 : Nat := 4983230072969 + 3 ^ 40 * 92568 * 2
def baseEnd_92568 : Nat := 14083519177925647696087

theorem tailTrace_92568 : CollatzResearch.WordTrace tailWord_92568 prefixEnd_92568 14083519177925647696087 := by
  unfold tailWord_92568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1688116164324710100431179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2250821552432946800574905 1688116164324710100431179)
  ·
    refine ⟨2532174246487065150646769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1688116164324710100431179 2532174246487065150646769)
    ·
      refine ⟨1899130684865298862985077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2532174246487065150646769 1899130684865298862985077)
      ·
        refine ⟨178043501706121768404851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1899130684865298862985077 178043501706121768404851)
        ·
          refine ⟨267065252559182652607277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178043501706121768404851 267065252559182652607277)
          ·
            refine ⟨100149469709693494727729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267065252559182652607277 100149469709693494727729)
            ·
              refine ⟨75112102282270121045797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100149469709693494727729 75112102282270121045797)
              ·
                refine ⟨14083519177925647696087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75112102282270121045797 14083519177925647696087)
                ·
                  rfl

theorem cell20_92568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_92568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92568 prefixEnd_92568 := by exact prefixLift 92568
  have htrace : WordTrace (prefixWord ++ tailWord_92568) baseStart_92568 baseEnd_92568 := by
    simpa [prefixWord, tailWord_92568, baseEnd_92568] using wordTrace_append hprefix tailTrace_92568
  have hstable : (prefixWord ++ tailWord_92568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92568).length < 2 ^ (prefixWord ++ tailWord_92568).sum := by decide
  have hdescent : baseEnd_92568 < baseStart_92568 := by decide
  rcases family_descends (prefixWord ++ tailWord_92568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92579 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_92579 : Nat := 118140960795 + 92579 * 2 ^ 59
def prefixEnd_92579 : Nat := 4983230072969 + 3 ^ 40 * 92579 * 2
def baseEnd_92579 : Nat := 42255578233509793721549

theorem tailTrace_92579 : CollatzResearch.WordTrace tailWord_92579 prefixEnd_92579 42255578233509793721549 := by
  unfold tailWord_92579
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376633531609569079512791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2251089021073046053008527 3376633531609569079512791)
  ·
    refine ⟨5064950297414353619269187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376633531609569079512791 5064950297414353619269187)
    ·
      refine ⟨7597425446121530428903781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064950297414353619269187 7597425446121530428903781)
      ·
        refine ⟨1424517271147786955419459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7597425446121530428903781 1424517271147786955419459)
        ·
          refine ⟨2136775906721680433129189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424517271147786955419459 2136775906721680433129189)
          ·
            refine ⟨400645482510315081211723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2136775906721680433129189 400645482510315081211723)
            ·
              refine ⟨600968223765472621817585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400645482510315081211723 600968223765472621817585)
              ·
                refine ⟨450726167824104466363189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600968223765472621817585 450726167824104466363189)
                ·
                  refine ⟨42255578233509793721549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 450726167824104466363189 42255578233509793721549)
                  ·
                    rfl

theorem cell20_92579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_92579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92579 prefixEnd_92579 := by exact prefixLift 92579
  have htrace : WordTrace (prefixWord ++ tailWord_92579) baseStart_92579 baseEnd_92579 := by
    simpa [prefixWord, tailWord_92579, baseEnd_92579] using wordTrace_append hprefix tailTrace_92579
  have hstable : (prefixWord ++ tailWord_92579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92579).length < 2 ^ (prefixWord ++ tailWord_92579).sum := by decide
  have hdescent : baseEnd_92579 < baseStart_92579 := by decide
  rcases family_descends (prefixWord ++ tailWord_92579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92599 : List Nat := [1, 1, 3, 1, 3, 4, 3, 2, 2]
def baseStart_92599 : Nat := 118140960795 + 92599 * 2 ^ 59
def prefixEnd_92599 : Nat := 4983230072969 + 3 ^ 40 * 92599 * 2
def baseEnd_92599 : Nat := 42264706778478613054801

theorem tailTrace_92599 : CollatzResearch.WordTrace tailWord_92599 prefixEnd_92599 42264706778478613054801 := by
  unfold tailWord_92599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377362991537112495240851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2251575327691408330160567 3377362991537112495240851)
  ·
    refine ⟨5066044487305668742861277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3377362991537112495240851 5066044487305668742861277)
    ·
      refine ⟨1899766682739625778572979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5066044487305668742861277 1899766682739625778572979)
      ·
        refine ⟨2849650024109438667859469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899766682739625778572979 2849650024109438667859469)
        ·
          refine ⟨1068618759041039500447301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2849650024109438667859469 1068618759041039500447301)
          ·
            refine ⟨200366017320194906333869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1068618759041039500447301 200366017320194906333869)
            ·
              refine ⟨75137256495073089875201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200366017320194906333869 75137256495073089875201)
              ·
                refine ⟨56352942371304817406401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75137256495073089875201 56352942371304817406401)
                ·
                  refine ⟨42264706778478613054801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56352942371304817406401 42264706778478613054801)
                  ·
                    rfl

theorem cell20_92599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 2].length) (baseStart_92599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92599 prefixEnd_92599 := by exact prefixLift 92599
  have htrace : WordTrace (prefixWord ++ tailWord_92599) baseStart_92599 baseEnd_92599 := by
    simpa [prefixWord, tailWord_92599, baseEnd_92599] using wordTrace_append hprefix tailTrace_92599
  have hstable : (prefixWord ++ tailWord_92599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92599).length < 2 ^ (prefixWord ++ tailWord_92599).sum := by decide
  have hdescent : baseEnd_92599 < baseStart_92599 := by decide
  rcases family_descends (prefixWord ++ tailWord_92599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92609 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 3]
def baseStart_92609 : Nat := 118140960795 + 92609 * 2 ^ 59
def prefixEnd_92609 : Nat := 4983230072969 + 3 ^ 40 * 92609 * 2
def baseEnd_92609 : Nat := 42269271050963022721427

theorem tailTrace_92609 : CollatzResearch.WordTrace tailWord_92609 prefixEnd_92609 42269271050963022721427 := by
  unfold tailWord_92609
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377727721500884203104881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2251818481000589468736587 3377727721500884203104881)
  ·
    refine ⟨2533295791125663152328661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3377727721500884203104881 2533295791125663152328661)
    ·
      refine ⟨59374120104507730132703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2533295791125663152328661 59374120104507730132703)
      ·
        refine ⟨89061180156761595199055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59374120104507730132703 89061180156761595199055)
        ·
          refine ⟨133591770235142392798583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89061180156761595199055 133591770235142392798583)
          ·
            refine ⟨200387655352713589197875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133591770235142392798583 200387655352713589197875)
            ·
              refine ⟨300581483029070383796813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200387655352713589197875 300581483029070383796813)
              ·
                refine ⟨112718056135901393923805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300581483029070383796813 112718056135901393923805)
                ·
                  refine ⟨42269271050963022721427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112718056135901393923805 42269271050963022721427)
                  ·
                    rfl

theorem cell20_92609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_92609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92609 prefixEnd_92609 := by exact prefixLift 92609
  have htrace : WordTrace (prefixWord ++ tailWord_92609) baseStart_92609 baseEnd_92609 := by
    simpa [prefixWord, tailWord_92609, baseEnd_92609] using wordTrace_append hprefix tailTrace_92609
  have hstable : (prefixWord ++ tailWord_92609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92609).length < 2 ^ (prefixWord ++ tailWord_92609).sum := by decide
  have hdescent : baseEnd_92609 < baseStart_92609 := by decide
  rcases family_descends (prefixWord ++ tailWord_92609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92654 : List Nat := [4, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_92654 : Nat := 118140960795 + 92654 * 2 ^ 59
def prefixEnd_92654 : Nat := 4983230072969 + 3 ^ 40 * 92654 * 2
def baseEnd_92654 : Nat := 42289810277142866221243

theorem tailTrace_92654 : CollatzResearch.WordTrace tailWord_92654 prefixEnd_92654 42289810277142866221243 := by
  unfold tailWord_92654
  simp only [CollatzResearch.WordTrace]
  refine ⟨422421125792232111061627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2252912670891904592328677 422421125792232111061627)
  ·
    refine ⟨633631688688348166592441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 422421125792232111061627 633631688688348166592441)
    ·
      refine ⟨475223766516261124944331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 633631688688348166592441 475223766516261124944331)
      ·
        refine ⟨712835649774391687416497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475223766516261124944331 712835649774391687416497)
        ·
          refine ⟨534626737330793765562373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712835649774391687416497 534626737330793765562373)
          ·
            refine ⟨100242513249523831042945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 534626737330793765562373 100242513249523831042945)
            ·
              refine ⟨75181884937142873282209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100242513249523831042945 75181884937142873282209)
              ·
                refine ⟨56386413702857154961657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75181884937142873282209 56386413702857154961657)
                ·
                  refine ⟨42289810277142866221243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56386413702857154961657 42289810277142866221243)
                  ·
                    rfl

theorem cell20_92654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_92654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92654 prefixEnd_92654 := by exact prefixLift 92654
  have htrace : WordTrace (prefixWord ++ tailWord_92654) baseStart_92654 baseEnd_92654 := by
    simpa [prefixWord, tailWord_92654, baseEnd_92654] using wordTrace_append hprefix tailTrace_92654
  have hstable : (prefixWord ++ tailWord_92654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92654).length < 2 ^ (prefixWord ++ tailWord_92654).sum := by decide
  have hdescent : baseEnd_92654 < baseStart_92654 := by decide
  rcases family_descends (prefixWord ++ tailWord_92654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92661 : List Nat := [1, 3, 5, 1, 3, 1, 1, 5]
def baseStart_92661 : Nat := 118140960795 + 92661 * 2 ^ 59
def prefixEnd_92661 : Nat := 4983230072969 + 3 ^ 40 * 92661 * 2
def baseEnd_92661 : Nat := 14097668422627317662627

theorem tailTrace_92661 : CollatzResearch.WordTrace tailWord_92661 prefixEnd_92661 14097668422627317662627 := by
  unfold tailWord_92661
  simp only [CollatzResearch.WordTrace]
  refine ⟨3379624317312497083997837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2253082878208331389331891 3379624317312497083997837)
  ·
    refine ⟨1267359118992186406499189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3379624317312497083997837 1267359118992186406499189)
    ·
      refine ⟨118814917405517475609299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1267359118992186406499189 118814917405517475609299)
      ·
        refine ⟨178222376108276213413949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118814917405517475609299 178222376108276213413949)
        ·
          refine ⟨66833391040603580030231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178222376108276213413949 66833391040603580030231)
          ·
            refine ⟨100250086560905370045347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66833391040603580030231 100250086560905370045347)
            ·
              refine ⟨150375129841358055068021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100250086560905370045347 150375129841358055068021)
              ·
                refine ⟨14097668422627317662627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150375129841358055068021 14097668422627317662627)
                ·
                  rfl

theorem cell20_92661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5].length) (baseStart_92661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92661 prefixEnd_92661 := by exact prefixLift 92661
  have htrace : WordTrace (prefixWord ++ tailWord_92661) baseStart_92661 baseEnd_92661 := by
    simpa [prefixWord, tailWord_92661, baseEnd_92661] using wordTrace_append hprefix tailTrace_92661
  have hstable : (prefixWord ++ tailWord_92661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92661).length < 2 ^ (prefixWord ++ tailWord_92661).sum := by decide
  have hdescent : baseEnd_92661 < baseStart_92661 := by decide
  rcases family_descends (prefixWord ++ tailWord_92661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92678 : List Nat := [6, 2, 1, 1, 1, 2, 3, 4]
def baseStart_92678 : Nat := 118140960795 + 92678 * 2 ^ 59
def prefixEnd_92678 : Nat := 4983230072969 + 3 ^ 40 * 92678 * 2
def baseEnd_92678 : Nat := 14100254843701816473715

theorem tailTrace_92678 : CollatzResearch.WordTrace tailWord_92678 prefixEnd_92678 14100254843701816473715 := by
  unfold tailWord_92678
  simp only [CollatzResearch.WordTrace]
  refine ⟨105632636195340905855209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2253496238833939324911125 105632636195340905855209)
  ·
    refine ⟨79224477146505679391407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105632636195340905855209 79224477146505679391407)
    ·
      refine ⟨118836715719758519087111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79224477146505679391407 118836715719758519087111)
      ·
        refine ⟨178255073579637778630667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118836715719758519087111 178255073579637778630667)
        ·
          refine ⟨267382610369456667946001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178255073579637778630667 267382610369456667946001)
          ·
            refine ⟨200536957777092500959501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267382610369456667946001 200536957777092500959501)
            ·
              refine ⟨75201359166409687859813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200536957777092500959501 75201359166409687859813)
              ·
                refine ⟨14100254843701816473715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75201359166409687859813 14100254843701816473715)
                ·
                  rfl

theorem cell20_92678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_92678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92678 prefixEnd_92678 := by exact prefixLift 92678
  have htrace : WordTrace (prefixWord ++ tailWord_92678) baseStart_92678 baseEnd_92678 := by
    simpa [prefixWord, tailWord_92678, baseEnd_92678] using wordTrace_append hprefix tailTrace_92678
  have hstable : (prefixWord ++ tailWord_92678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92678).length < 2 ^ (prefixWord ++ tailWord_92678).sum := by decide
  have hdescent : baseEnd_92678 < baseStart_92678 := by decide
  rcases family_descends (prefixWord ++ tailWord_92678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92692 : List Nat := [2, 4, 3, 1, 1, 2, 2, 3, 2]
def baseStart_92692 : Nat := 118140960795 + 92692 * 2 ^ 59
def prefixEnd_92692 : Nat := 4983230072969 + 3 ^ 40 * 92692 * 2
def baseEnd_92692 : Nat := 42307154512583622954421

theorem tailTrace_92692 : CollatzResearch.WordTrace tailWord_92692 prefixEnd_92692 42307154512583622954421 := by
  unfold tailWord_92692
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690377490100094689188165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2253836653466792918917553 1690377490100094689188165)
  ·
    refine ⟨316945779393767754222781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1690377490100094689188165 316945779393767754222781)
    ·
      refine ⟨118854667272662907833543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316945779393767754222781 118854667272662907833543)
      ·
        refine ⟨178282000908994361750315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118854667272662907833543 178282000908994361750315)
        ·
          refine ⟨267423001363491542625473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178282000908994361750315 267423001363491542625473)
          ·
            refine ⟨200567251022618656969105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267423001363491542625473 200567251022618656969105)
            ·
              refine ⟨150425438266963992726829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200567251022618656969105 150425438266963992726829)
              ·
                refine ⟨56409539350111497272561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150425438266963992726829 56409539350111497272561)
                ·
                  refine ⟨42307154512583622954421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56409539350111497272561 42307154512583622954421)
                  ·
                    rfl

theorem cell20_92692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_92692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92692 prefixEnd_92692 := by exact prefixLift 92692
  have htrace : WordTrace (prefixWord ++ tailWord_92692) baseStart_92692 baseEnd_92692 := by
    simpa [prefixWord, tailWord_92692, baseEnd_92692] using wordTrace_append hprefix tailTrace_92692
  have hstable : (prefixWord ++ tailWord_92692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92692).length < 2 ^ (prefixWord ++ tailWord_92692).sum := by decide
  have hdescent : baseEnd_92692 < baseStart_92692 := by decide
  rcases family_descends (prefixWord ++ tailWord_92692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92693 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_92693 : Nat := 118140960795 + 92693 * 2 ^ 59
def prefixEnd_92693 : Nat := 4983230072969 + 3 ^ 40 * 92693 * 2
def baseEnd_92693 : Nat := 42307610939832063921083

theorem tailTrace_92693 : CollatzResearch.WordTrace tailWord_92693 prefixEnd_92693 42307610939832063921083 := by
  unfold tailWord_92693
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380791453196566549162733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2253860968797711032775155 3380791453196566549162733)
  ·
    refine ⟨1267796794948712455936025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3380791453196566549162733 1267796794948712455936025)
    ·
      refine ⟨950847596211534341952019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1267796794948712455936025 950847596211534341952019)
      ·
        refine ⟨1426271394317301512928029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950847596211534341952019 1426271394317301512928029)
        ·
          refine ⟨534851772868988067348011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1426271394317301512928029 534851772868988067348011)
          ·
            refine ⟨802277659303482101022017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534851772868988067348011 802277659303482101022017)
            ·
              refine ⟨601708244477611575766513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802277659303482101022017 601708244477611575766513)
              ·
                refine ⟨451281183358208681824885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601708244477611575766513 451281183358208681824885)
                ·
                  refine ⟨42307610939832063921083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 451281183358208681824885 42307610939832063921083)
                  ·
                    rfl

theorem cell20_92693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_92693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92693 prefixEnd_92693 := by exact prefixLift 92693
  have htrace : WordTrace (prefixWord ++ tailWord_92693) baseStart_92693 baseEnd_92693 := by
    simpa [prefixWord, tailWord_92693, baseEnd_92693] using wordTrace_append hprefix tailTrace_92693
  have hstable : (prefixWord ++ tailWord_92693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92693).length < 2 ^ (prefixWord ++ tailWord_92693).sum := by decide
  have hdescent : baseEnd_92693 < baseStart_92693 := by decide
  rcases family_descends (prefixWord ++ tailWord_92693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92696 : List Nat := [2, 1, 2, 3, 3, 1, 1, 5, 2]
def baseStart_92696 : Nat := 118140960795 + 92696 * 2 ^ 59
def prefixEnd_92696 : Nat := 4983230072969 + 3 ^ 40 * 92696 * 2
def baseEnd_92696 : Nat := 42308980221577386821071

theorem tailTrace_92696 : CollatzResearch.WordTrace tailWord_92696 prefixEnd_92696 42308980221577386821071 := by
  unfold tailWord_92696
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690450436092849030760971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2253933914790465374347961 1690450436092849030760971)
  ·
    refine ⟨2535675654139273546141457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1690450436092849030760971 2535675654139273546141457)
    ·
      refine ⟨1901756740604455159606093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2535675654139273546141457 1901756740604455159606093)
      ·
        refine ⟨713158777726670684852285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1901756740604455159606093 713158777726670684852285)
        ·
          refine ⟨267434541647501506819607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 713158777726670684852285 267434541647501506819607)
          ·
            refine ⟨401151812471252260229411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267434541647501506819607 401151812471252260229411)
            ·
              refine ⟨601727718706878390344117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401151812471252260229411 601727718706878390344117)
              ·
                refine ⟨56411973628769849094761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 601727718706878390344117 56411973628769849094761)
                ·
                  refine ⟨42308980221577386821071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56411973628769849094761 42308980221577386821071)
                  ·
                    rfl

theorem cell20_92696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_92696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92696 prefixEnd_92696 := by exact prefixLift 92696
  have htrace : WordTrace (prefixWord ++ tailWord_92696) baseStart_92696 baseEnd_92696 := by
    simpa [prefixWord, tailWord_92696, baseEnd_92696] using wordTrace_append hprefix tailTrace_92696
  have hstable : (prefixWord ++ tailWord_92696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92696).length < 2 ^ (prefixWord ++ tailWord_92696).sum := by decide
  have hdescent : baseEnd_92696 < baseStart_92696 := by decide
  rcases family_descends (prefixWord ++ tailWord_92696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92741 : List Nat := [1, 3, 1, 1, 1, 7, 2, 4]
def baseStart_92741 : Nat := 118140960795 + 92741 * 2 ^ 59
def prefixEnd_92741 : Nat := 4983230072969 + 3 ^ 40 * 92741 * 2
def baseEnd_92741 : Nat := 14109839815919076773629

theorem tailTrace_92741 : CollatzResearch.WordTrace tailWord_92741 prefixEnd_92741 14109839815919076773629 := by
  unfold tailWord_92741
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382542157022670746910077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2255028104681780497940051 3382542157022670746910077)
  ·
    refine ⟨1268453308883501530091279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3382542157022670746910077 1268453308883501530091279)
    ·
      refine ⟨1902679963325252295136919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1268453308883501530091279 1902679963325252295136919)
      ·
        refine ⟨2854019944987878442705379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902679963325252295136919 2854019944987878442705379)
        ·
          refine ⟨4281029917481817664058069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854019944987878442705379 4281029917481817664058069)
          ·
            refine ⟨100336638690980101501361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4281029917481817664058069 100336638690980101501361)
            ·
              refine ⟨75252479018235076126021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100336638690980101501361 75252479018235076126021)
              ·
                refine ⟨14109839815919076773629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75252479018235076126021 14109839815919076773629)
                ·
                  rfl

theorem cell20_92741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_92741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92741 prefixEnd_92741 := by exact prefixLift 92741
  have htrace : WordTrace (prefixWord ++ tailWord_92741) baseStart_92741 baseEnd_92741 := by
    simpa [prefixWord, tailWord_92741, baseEnd_92741] using wordTrace_append hprefix tailTrace_92741
  have hstable : (prefixWord ++ tailWord_92741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92741).length < 2 ^ (prefixWord ++ tailWord_92741).sum := by decide
  have hdescent : baseEnd_92741 < baseStart_92741 := by decide
  rcases family_descends (prefixWord ++ tailWord_92741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92769 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_92769 : Nat := 118140960795 + 92769 * 2 ^ 59
def prefixEnd_92769 : Nat := 4983230072969 + 3 ^ 40 * 92769 * 2
def baseEnd_92769 : Nat := 42342299410713577387439

theorem tailTrace_92769 : CollatzResearch.WordTrace tailWord_92769 prefixEnd_92769 42342299410713577387439 := by
  unfold tailWord_92769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383563400921231528929361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2255708933947487685952907 3383563400921231528929361)
  ·
    refine ⟨2537672550690923646697021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3383563400921231528929361 2537672550690923646697021)
    ·
      refine ⟨951627206509096367511383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2537672550690923646697021 951627206509096367511383)
      ·
        refine ⟨1427440809763644551267075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951627206509096367511383 1427440809763644551267075)
        ·
          refine ⟨2141161214645466826900613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427440809763644551267075 2141161214645466826900613)
          ·
            refine ⟨401467727746025030043865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2141161214645466826900613 401467727746025030043865)
            ·
              refine ⟨301100795809518772532899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401467727746025030043865 301100795809518772532899)
              ·
                refine ⟨451651193714278158799349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301100795809518772532899 451651193714278158799349)
                ·
                  refine ⟨42342299410713577387439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 451651193714278158799349 42342299410713577387439)
                  ·
                    rfl

theorem cell20_92769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_92769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92769 prefixEnd_92769 := by exact prefixLift 92769
  have htrace : WordTrace (prefixWord ++ tailWord_92769) baseStart_92769 baseEnd_92769 := by
    simpa [prefixWord, tailWord_92769, baseEnd_92769] using wordTrace_append hprefix tailTrace_92769
  have hstable : (prefixWord ++ tailWord_92769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92769).length < 2 ^ (prefixWord ++ tailWord_92769).sum := by decide
  have hdescent : baseEnd_92769 < baseStart_92769 := by decide
  rcases family_descends (prefixWord ++ tailWord_92769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92782 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_92782 : Nat := 118140960795 + 92782 * 2 ^ 59
def prefixEnd_92782 : Nat := 4983230072969 + 3 ^ 40 * 92782 * 2
def baseEnd_92782 : Nat := 42348232964943309954053

theorem tailTrace_92782 : CollatzResearch.WordTrace tailWord_92782 prefixEnd_92782 42348232964943309954053 := by
  unfold tailWord_92782
  simp only [CollatzResearch.WordTrace]
  refine ⟨423004693734266843644075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2256025033249423166101733 423004693734266843644075)
  ·
    refine ⟨634507040601400265466113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 423004693734266843644075 634507040601400265466113)
    ·
      refine ⟨475880280451050199099585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 634507040601400265466113 475880280451050199099585)
      ·
        refine ⟨356910210338287649324689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475880280451050199099585 356910210338287649324689)
        ·
          refine ⟨267682657753715736993517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356910210338287649324689 267682657753715736993517)
          ·
            refine ⟨100380996657643401372569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267682657753715736993517 100380996657643401372569)
            ·
              refine ⟨75285747493232551029427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100380996657643401372569 75285747493232551029427)
              ·
                refine ⟨112928621239848826544141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75285747493232551029427 112928621239848826544141)
                ·
                  refine ⟨42348232964943309954053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112928621239848826544141 42348232964943309954053)
                  ·
                    rfl

theorem cell20_92782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_92782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92782 prefixEnd_92782 := by exact prefixLift 92782
  have htrace : WordTrace (prefixWord ++ tailWord_92782) baseStart_92782 baseEnd_92782 := by
    simpa [prefixWord, tailWord_92782, baseEnd_92782] using wordTrace_append hprefix tailTrace_92782
  have hstable : (prefixWord ++ tailWord_92782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92782).length < 2 ^ (prefixWord ++ tailWord_92782).sum := by decide
  have hdescent : baseEnd_92782 < baseStart_92782 := by decide
  rcases family_descends (prefixWord ++ tailWord_92782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92783 : List Nat := [1, 1, 2, 1, 3, 2, 3, 7]
def baseStart_92783 : Nat := 118140960795 + 92783 * 2 ^ 59
def prefixEnd_92783 : Nat := 4983230072969 + 3 ^ 40 * 92783 * 2
def baseEnd_92783 : Nat := 14116229797397250306905

theorem tailTrace_92783 : CollatzResearch.WordTrace tailWord_92783 prefixEnd_92783 14116229797397250306905 := by
  unfold tailWord_92783
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384074022870511919939003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2256049348580341279959335 3384074022870511919939003)
  ·
    refine ⟨5076111034305767879908505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3384074022870511919939003 5076111034305767879908505)
    ·
      refine ⟨3807083275729325909931379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5076111034305767879908505 3807083275729325909931379)
      ·
        refine ⟨5710624913593988864897069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807083275729325909931379 5710624913593988864897069)
        ·
          refine ⟨2141484342597745824336401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5710624913593988864897069 2141484342597745824336401)
          ·
            refine ⟨1606113256948309368252301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2141484342597745824336401 1606113256948309368252301)
            ·
              refine ⟨602292471355616013094613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1606113256948309368252301 602292471355616013094613)
              ·
                refine ⟨14116229797397250306905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 602292471355616013094613 14116229797397250306905)
                ·
                  rfl

theorem cell20_92783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_92783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92783 prefixEnd_92783 := by exact prefixLift 92783
  have htrace : WordTrace (prefixWord ++ tailWord_92783) baseStart_92783 baseEnd_92783 := by
    simpa [prefixWord, tailWord_92783, baseEnd_92783] using wordTrace_append hprefix tailTrace_92783
  have hstable : (prefixWord ++ tailWord_92783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92783).length < 2 ^ (prefixWord ++ tailWord_92783).sum := by decide
  have hdescent : baseEnd_92783 < baseStart_92783 := by decide
  rcases family_descends (prefixWord ++ tailWord_92783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92824 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_92824 : Nat := 118140960795 + 92824 * 2 ^ 59
def prefixEnd_92824 : Nat := 4983230072969 + 3 ^ 40 * 92824 * 2
def baseEnd_92824 : Nat := 42367402909377830553881

theorem tailTrace_92824 : CollatzResearch.WordTrace tailWord_92824 prefixEnd_92824 42367402909377830553881 := by
  unfold tailWord_92824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692784707860987961090763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2257046277147983948121017 1692784707860987961090763)
  ·
    refine ⟨2539177061791481941636145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692784707860987961090763 2539177061791481941636145)
    ·
      refine ⟨1904382796343611456227109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2539177061791481941636145 1904382796343611456227109)
      ·
        refine ⟨357071774314427148042583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1904382796343611456227109 357071774314427148042583)
        ·
          refine ⟨535607661471640722063875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357071774314427148042583 535607661471640722063875)
          ·
            refine ⟨803411492207461083095813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535607661471640722063875 803411492207461083095813)
            ·
              refine ⟨150639654788898953080465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 803411492207461083095813 150639654788898953080465)
              ·
                refine ⟨112979741091674214810349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150639654788898953080465 112979741091674214810349)
                ·
                  refine ⟨42367402909377830553881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112979741091674214810349 42367402909377830553881)
                  ·
                    rfl

theorem cell20_92824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_92824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92824 prefixEnd_92824 := by exact prefixLift 92824
  have htrace : WordTrace (prefixWord ++ tailWord_92824) baseStart_92824 baseEnd_92824 := by
    simpa [prefixWord, tailWord_92824, baseEnd_92824] using wordTrace_append hprefix tailTrace_92824
  have hstable : (prefixWord ++ tailWord_92824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92824).length < 2 ^ (prefixWord ++ tailWord_92824).sum := by decide
  have hdescent : baseEnd_92824 < baseStart_92824 := by decide
  rcases family_descends (prefixWord ++ tailWord_92824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92855 : List Nat := [1, 1, 3, 1, 6, 1, 3, 4]
def baseStart_92855 : Nat := 118140960795 + 92855 * 2 ^ 59
def prefixEnd_92855 : Nat := 4983230072969 + 3 ^ 40 * 92855 * 2
def baseEnd_92855 : Nat := 14127184051359833506807

theorem tailTrace_92855 : CollatzResearch.WordTrace tailWord_92855 prefixEnd_92855 14127184051359833506807 := by
  unfold tailWord_92855
  simp only [CollatzResearch.WordTrace]
  refine ⟨3386700078609668216560019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2257800052406445477706679 3386700078609668216560019)
  ·
    refine ⟨5080050117914502324840029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3386700078609668216560019 5080050117914502324840029)
    ·
      refine ⟨1905018794217938371815011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5080050117914502324840029 1905018794217938371815011)
      ·
        refine ⟨2857528191326907557722517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905018794217938371815011 2857528191326907557722517)
        ·
          refine ⟨133946633968448791768243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2857528191326907557722517 133946633968448791768243)
          ·
            refine ⟨200919950952673187652365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133946633968448791768243 200919950952673187652365)
            ·
              refine ⟨75344981607252445369637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200919950952673187652365 75344981607252445369637)
              ·
                refine ⟨14127184051359833506807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75344981607252445369637 14127184051359833506807)
                ·
                  rfl

theorem cell20_92855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_92855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92855 prefixEnd_92855 := by exact prefixLift 92855
  have htrace : WordTrace (prefixWord ++ tailWord_92855) baseStart_92855 baseEnd_92855 := by
    simpa [prefixWord, tailWord_92855, baseEnd_92855] using wordTrace_append hprefix tailTrace_92855
  have hstable : (prefixWord ++ tailWord_92855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92855).length < 2 ^ (prefixWord ++ tailWord_92855).sum := by decide
  have hdescent : baseEnd_92855 < baseStart_92855 := by decide
  rcases family_descends (prefixWord ++ tailWord_92855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92876 : List Nat := [2, 2, 1, 5, 1, 2, 7]
def baseStart_92876 : Nat := 118140960795 + 92876 * 2 ^ 59
def prefixEnd_92876 : Nat := 4983230072969 + 3 ^ 40 * 92876 * 2
def baseEnd_92876 : Nat := 4710126347366306757815

theorem tailTrace_92876 : CollatzResearch.WordTrace tailWord_92876 prefixEnd_92876 4710126347366306757815 := by
  unfold tailWord_92876
  simp only [CollatzResearch.WordTrace]
  refine ⟨1693733005766794401537241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2258310674355725868716321 1693733005766794401537241)
  ·
    refine ⟨1270299754325095801152931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1693733005766794401537241 1270299754325095801152931)
    ·
      refine ⟨1905449631487643701729397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270299754325095801152931 1905449631487643701729397)
      ·
        refine ⟨178635902951966597037131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1905449631487643701729397 178635902951966597037131)
        ·
          refine ⟨267953854427949895555697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178635902951966597037131 267953854427949895555697)
          ·
            refine ⟨200965390820962421666773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267953854427949895555697 200965390820962421666773)
            ·
              refine ⟨4710126347366306757815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 200965390820962421666773 4710126347366306757815)
              ·
                rfl

theorem cell20_92876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 7].length) (baseStart_92876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92876 prefixEnd_92876 := by exact prefixLift 92876
  have htrace : WordTrace (prefixWord ++ tailWord_92876) baseStart_92876 baseEnd_92876 := by
    simpa [prefixWord, tailWord_92876, baseEnd_92876] using wordTrace_append hprefix tailTrace_92876
  have hstable : (prefixWord ++ tailWord_92876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92876).length < 2 ^ (prefixWord ++ tailWord_92876).sum := by decide
  have hdescent : baseEnd_92876 < baseStart_92876 := by decide
  rcases family_descends (prefixWord ++ tailWord_92876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92914 : List Nat := [3, 2, 1, 3, 1, 3, 1, 6]
def baseStart_92914 : Nat := 118140960795 + 92914 * 2 ^ 59
def prefixEnd_92914 : Nat := 4983230072969 + 3 ^ 40 * 92914 * 2
def baseEnd_92914 : Nat := 14136160453912505851171

theorem tailTrace_92914 : CollatzResearch.WordTrace tailWord_92914 prefixEnd_92914 14136160453912505851171 := by
  unfold tailWord_92914
  simp only [CollatzResearch.WordTrace]
  refine ⟨847212996348980323239449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2259234656930614195305197 847212996348980323239449)
  ·
    refine ⟨635409747261735242429587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 847212996348980323239449 635409747261735242429587)
    ·
      refine ⟨953114620892602863644381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635409747261735242429587 953114620892602863644381)
      ·
        refine ⟨357417982834726073866643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 953114620892602863644381 357417982834726073866643)
        ·
          refine ⟨536126974252089110799965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357417982834726073866643 536126974252089110799965)
          ·
            refine ⟨201047615344533416549987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536126974252089110799965 201047615344533416549987)
            ·
              refine ⟨301571423016800124824981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201047615344533416549987 301571423016800124824981)
              ·
                refine ⟨14136160453912505851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 301571423016800124824981 14136160453912505851171)
                ·
                  rfl

theorem cell20_92914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_92914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92914 prefixEnd_92914 := by exact prefixLift 92914
  have htrace : WordTrace (prefixWord ++ tailWord_92914) baseStart_92914 baseEnd_92914 := by
    simpa [prefixWord, tailWord_92914, baseEnd_92914] using wordTrace_append hprefix tailTrace_92914
  have hstable : (prefixWord ++ tailWord_92914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92914).length < 2 ^ (prefixWord ++ tailWord_92914).sum := by decide
  have hdescent : baseEnd_92914 < baseStart_92914 := by decide
  rcases family_descends (prefixWord ++ tailWord_92914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92916 : List Nat := [2, 6, 1, 1, 3, 1, 1, 3, 2]
def baseStart_92916 : Nat := 118140960795 + 92916 * 2 ^ 59
def prefixEnd_92916 : Nat := 4983230072969 + 3 ^ 40 * 92916 * 2
def baseEnd_92916 : Nat := 42409394216234399486839

theorem tailTrace_92916 : CollatzResearch.WordTrace tailWord_92916 prefixEnd_92916 42409394216234399486839 := by
  unfold tailWord_92916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694462465694337817265301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2259283287592450423020401 1694462465694337817265301)
  ·
    refine ⟨79427928079422085184311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1694462465694337817265301 79427928079422085184311)
    ·
      refine ⟨119141892119133127776467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79427928079422085184311 119141892119133127776467)
      ·
        refine ⟨178712838178699691664701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119141892119133127776467 178712838178699691664701)
        ·
          refine ⟨67017314317012384374263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178712838178699691664701 67017314317012384374263)
          ·
            refine ⟨100525971475518576561395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67017314317012384374263 100525971475518576561395)
            ·
              refine ⟨150788957213277864842093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100525971475518576561395 150788957213277864842093)
              ·
                refine ⟨56545858954979199315785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150788957213277864842093 56545858954979199315785)
                ·
                  refine ⟨42409394216234399486839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56545858954979199315785 42409394216234399486839)
                  ·
                    rfl

theorem cell20_92916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_92916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92916 prefixEnd_92916 := by exact prefixLift 92916
  have htrace : WordTrace (prefixWord ++ tailWord_92916) baseStart_92916 baseEnd_92916 := by
    simpa [prefixWord, tailWord_92916, baseEnd_92916] using wordTrace_append hprefix tailTrace_92916
  have hstable : (prefixWord ++ tailWord_92916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92916).length < 2 ^ (prefixWord ++ tailWord_92916).sum := by decide
  have hdescent : baseEnd_92916 < baseStart_92916 := by decide
  rcases family_descends (prefixWord ++ tailWord_92916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92924 : List Nat := [2, 2, 2, 1, 3, 2, 3, 3, 2]
def baseStart_92924 : Nat := 118140960795 + 92924 * 2 ^ 59
def prefixEnd_92924 : Nat := 4983230072969 + 3 ^ 40 * 92924 * 2
def baseEnd_92924 : Nat := 42413045634221927220139

theorem tailTrace_92924 : CollatzResearch.WordTrace tailWord_92924 prefixEnd_92924 42413045634221927220139 := by
  unfold tailWord_92924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694608357679846500410913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2259477810239795333881217 1694608357679846500410913)
  ·
    refine ⟨1270956268259884875308185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1694608357679846500410913 1270956268259884875308185)
    ·
      refine ⟨953217201194913656481139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1270956268259884875308185 953217201194913656481139)
      ·
        refine ⟨1429825801792370484721709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953217201194913656481139 1429825801792370484721709)
        ·
          refine ⟨536184675672138931770641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1429825801792370484721709 536184675672138931770641)
          ·
            refine ⟨402138506754104198827981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536184675672138931770641 402138506754104198827981)
            ·
              refine ⟨150801940032789074560493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402138506754104198827981 150801940032789074560493)
              ·
                refine ⟨56550727512295902960185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150801940032789074560493 56550727512295902960185)
                ·
                  refine ⟨42413045634221927220139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56550727512295902960185 42413045634221927220139)
                  ·
                    rfl

theorem cell20_92924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_92924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92924 prefixEnd_92924 := by exact prefixLift 92924
  have htrace : WordTrace (prefixWord ++ tailWord_92924) baseStart_92924 baseEnd_92924 := by
    simpa [prefixWord, tailWord_92924, baseEnd_92924] using wordTrace_append hprefix tailTrace_92924
  have hstable : (prefixWord ++ tailWord_92924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92924).length < 2 ^ (prefixWord ++ tailWord_92924).sum := by decide
  have hdescent : baseEnd_92924 < baseStart_92924 := by decide
  rcases family_descends (prefixWord ++ tailWord_92924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92945 : List Nat := [1, 2, 2, 1, 1, 3, 2, 6, 2]
def baseStart_92945 : Nat := 118140960795 + 92945 * 2 ^ 59
def prefixEnd_92945 : Nat := 4983230072969 + 3 ^ 40 * 92945 * 2
def baseEnd_92945 : Nat := 42422630606439187520053

theorem tailTrace_92945 : CollatzResearch.WordTrace tailWord_92945 prefixEnd_92945 42422630606439187520053 := by
  unfold tailWord_92945
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389982648283613587336289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2259988432189075724890859 3389982648283613587336289)
  ·
    refine ⟨2542486986212710190502217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3389982648283613587336289 2542486986212710190502217)
    ·
      refine ⟨1906865239659532642876663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2542486986212710190502217 1906865239659532642876663)
      ·
        refine ⟨2860297859489298964314995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906865239659532642876663 2860297859489298964314995)
        ·
          refine ⟨4290446789233948446472493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860297859489298964314995 4290446789233948446472493)
          ·
            refine ⟨1608917545962730667427185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4290446789233948446472493 1608917545962730667427185)
            ·
              refine ⟨1206688159472048000570389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608917545962730667427185 1206688159472048000570389)
              ·
                refine ⟨56563507475252250026737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1206688159472048000570389 56563507475252250026737)
                ·
                  refine ⟨42422630606439187520053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56563507475252250026737 42422630606439187520053)
                  ·
                    rfl

theorem cell20_92945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_92945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92945 prefixEnd_92945 := by exact prefixLift 92945
  have htrace : WordTrace (prefixWord ++ tailWord_92945) baseStart_92945 baseEnd_92945 := by
    simpa [prefixWord, tailWord_92945, baseEnd_92945] using wordTrace_append hprefix tailTrace_92945
  have hstable : (prefixWord ++ tailWord_92945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92945).length < 2 ^ (prefixWord ++ tailWord_92945).sum := by decide
  have hdescent : baseEnd_92945 < baseStart_92945 := by decide
  rcases family_descends (prefixWord ++ tailWord_92945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92983 : List Nat := [1, 1, 3, 1, 2, 1, 4, 5, 2]
def baseStart_92983 : Nat := 118140960795 + 92983 * 2 ^ 59
def prefixEnd_92983 : Nat := 4983230072969 + 3 ^ 40 * 92983 * 2
def baseEnd_92983 : Nat := 42439974841879944253231

theorem tailTrace_92983 : CollatzResearch.WordTrace tailWord_92983 prefixEnd_92983 42439974841879944253231 := by
  unfold tailWord_92983
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391368622145946077219603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2260912414763964051479735 3391368622145946077219603)
  ·
    refine ⟨5087052933218919115829405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391368622145946077219603 5087052933218919115829405)
    ·
      refine ⟨1907644849957094668436027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5087052933218919115829405 1907644849957094668436027)
      ·
        refine ⟨2861467274935642002654041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907644849957094668436027 2861467274935642002654041)
        ·
          refine ⟨2146100456201731501990531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2861467274935642002654041 2146100456201731501990531)
          ·
            refine ⟨3219150684302597252985797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146100456201731501990531 3219150684302597252985797)
            ·
              refine ⟨603590753306736984934837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3219150684302597252985797 603590753306736984934837)
              ·
                refine ⟨56586633122506592337641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603590753306736984934837 56586633122506592337641)
                ·
                  refine ⟨42439974841879944253231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56586633122506592337641 42439974841879944253231)
                  ·
                    rfl

theorem cell20_92983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 2].length) (baseStart_92983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92983 prefixEnd_92983 := by exact prefixLift 92983
  have htrace : WordTrace (prefixWord ++ tailWord_92983) baseStart_92983 baseEnd_92983 := by
    simpa [prefixWord, tailWord_92983, baseEnd_92983] using wordTrace_append hprefix tailTrace_92983
  have hstable : (prefixWord ++ tailWord_92983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92983).length < 2 ^ (prefixWord ++ tailWord_92983).sum := by decide
  have hdescent : baseEnd_92983 < baseStart_92983 := by decide
  rcases family_descends (prefixWord ++ tailWord_92983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92990 : List Nat := [4, 2, 1, 2, 3, 8]
def baseStart_92990 : Nat := 118140960795 + 92990 * 2 ^ 59
def prefixEnd_92990 : Nat := 4983230072969 + 3 ^ 40 * 92990 * 2
def baseEnd_92990 : Nat := 1571969253059964111847

theorem tailTrace_92990 : CollatzResearch.WordTrace tailWord_92990 prefixEnd_92990 1571969253059964111847 := by
  unfold tailWord_92990
  simp only [CollatzResearch.WordTrace]
  refine ⟨423952991640073284090553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2261082622080390848482949 423952991640073284090553)
  ·
    refine ⟨317964743730054963067915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 423952991640073284090553 317964743730054963067915)
    ·
      refine ⟨476947115595082444601873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317964743730054963067915 476947115595082444601873)
      ·
        refine ⟨357710336696311833451405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476947115595082444601873 357710336696311833451405)
        ·
          refine ⟨134141376261116937544277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357710336696311833451405 134141376261116937544277)
          ·
            refine ⟨1571969253059964111847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 134141376261116937544277 1571969253059964111847)
            ·
              rfl

theorem cell20_92990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 8].length) (baseStart_92990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92990 prefixEnd_92990 := by exact prefixLift 92990
  have htrace : WordTrace (prefixWord ++ tailWord_92990) baseStart_92990 baseEnd_92990 := by
    simpa [prefixWord, tailWord_92990, baseEnd_92990] using wordTrace_append hprefix tailTrace_92990
  have hstable : (prefixWord ++ tailWord_92990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92990).length < 2 ^ (prefixWord ++ tailWord_92990).sum := by decide
  have hdescent : baseEnd_92990 < baseStart_92990 := by decide
  rcases family_descends (prefixWord ++ tailWord_92990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92996 : List Nat := [2, 3, 4, 2, 1, 1, 1, 4, 2]
def baseStart_92996 : Nat := 118140960795 + 92996 * 2 ^ 59
def prefixEnd_92996 : Nat := 4983230072969 + 3 ^ 40 * 92996 * 2
def baseEnd_92996 : Nat := 42445908396109676819845

theorem tailTrace_92996 : CollatzResearch.WordTrace tailWord_92996 prefixEnd_92996 42445908396109676819845 := by
  unfold tailWord_92996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695921385549424648721421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2261228514065899531628561 1695921385549424648721421)
  ·
    refine ⟨635970519581034243270533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1695921385549424648721421 635970519581034243270533)
    ·
      refine ⟨119244472421443920613225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 635970519581034243270533 119244472421443920613225)
      ·
        refine ⟨89433354316082940459919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119244472421443920613225 89433354316082940459919)
        ·
          refine ⟨134150031474124410689879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89433354316082940459919 134150031474124410689879)
          ·
            refine ⟨201225047211186616034819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134150031474124410689879 201225047211186616034819)
            ·
              refine ⟨301837570816779924052229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201225047211186616034819 301837570816779924052229)
              ·
                refine ⟨56594544528146235759793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 301837570816779924052229 56594544528146235759793)
                ·
                  refine ⟨42445908396109676819845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56594544528146235759793 42445908396109676819845)
                  ·
                    rfl

theorem cell20_92996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_92996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_92996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_92996 prefixEnd_92996 := by exact prefixLift 92996
  have htrace : WordTrace (prefixWord ++ tailWord_92996) baseStart_92996 baseEnd_92996 := by
    simpa [prefixWord, tailWord_92996, baseEnd_92996] using wordTrace_append hprefix tailTrace_92996
  have hstable : (prefixWord ++ tailWord_92996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92996).length < 2 ^ (prefixWord ++ tailWord_92996).sum := by decide
  have hdescent : baseEnd_92996 < baseStart_92996 := by decide
  rcases family_descends (prefixWord ++ tailWord_92996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93049 : List Nat := [1, 2, 1, 3, 2, 4, 7]
def baseStart_93049 : Nat := 118140960795 + 93049 * 2 ^ 59
def prefixEnd_93049 : Nat := 4983230072969 + 3 ^ 40 * 93049 * 2
def baseEnd_93049 : Nat := 4718899893364116450329

theorem tailTrace_93049 : CollatzResearch.WordTrace tailWord_93049 prefixEnd_93049 4718899893364116450329 := by
  unfold tailWord_93049
  simp only [CollatzResearch.WordTrace]
  refine ⟨3393775839906839349122201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2262517226604559566081467 3393775839906839349122201)
  ·
    refine ⟨2545331879930129511841651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3393775839906839349122201 2545331879930129511841651)
    ·
      refine ⟨3817997819895194267762477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2545331879930129511841651 3817997819895194267762477)
      ·
        refine ⟨1431749182460697850410929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3817997819895194267762477 1431749182460697850410929)
        ·
          refine ⟨1073811886845523387808197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1431749182460697850410929 1073811886845523387808197)
          ·
            refine ⟨201339728783535635214037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1073811886845523387808197 201339728783535635214037)
            ·
              refine ⟨4718899893364116450329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 201339728783535635214037 4718899893364116450329)
              ·
                rfl

theorem cell20_93049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_93049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93049 prefixEnd_93049 := by exact prefixLift 93049
  have htrace : WordTrace (prefixWord ++ tailWord_93049) baseStart_93049 baseEnd_93049 := by
    simpa [prefixWord, tailWord_93049, baseEnd_93049] using wordTrace_append hprefix tailTrace_93049
  have hstable : (prefixWord ++ tailWord_93049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93049).length < 2 ^ (prefixWord ++ tailWord_93049).sum := by decide
  have hdescent : baseEnd_93049 < baseStart_93049 := by decide
  rcases family_descends (prefixWord ++ tailWord_93049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93059 : List Nat := [1, 1, 1, 3, 4, 1, 1, 6, 2]
def baseStart_93059 : Nat := 118140960795 + 93059 * 2 ^ 59
def prefixEnd_93059 : Nat := 4983230072969 + 3 ^ 40 * 93059 * 2
def baseEnd_93059 : Nat := 42474663312761457719587

theorem tailTrace_93059 : CollatzResearch.WordTrace tailWord_93059 prefixEnd_93059 42474663312761457719587 := by
  unfold tailWord_93059
  simp only [CollatzResearch.WordTrace]
  refine ⟨3394140569870611056986231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2262760379913740704657487 3394140569870611056986231)
  ·
    refine ⟨5091210854805916585479347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3394140569870611056986231 5091210854805916585479347)
    ·
      refine ⟨7636816282208874878219021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5091210854805916585479347 7636816282208874878219021)
      ·
        refine ⟨2863806105828328079332133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7636816282208874878219021 2863806105828328079332133)
        ·
          refine ⟨536963644842811514874775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2863806105828328079332133 536963644842811514874775)
          ·
            refine ⟨805445467264217272312163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536963644842811514874775 805445467264217272312163)
            ·
              refine ⟨1208168200896325908468245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805445467264217272312163 1208168200896325908468245)
              ·
                refine ⟨56632884417015276959449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1208168200896325908468245 56632884417015276959449)
                ·
                  refine ⟨42474663312761457719587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56632884417015276959449 42474663312761457719587)
                  ·
                    rfl

theorem cell20_93059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 2].length) (baseStart_93059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93059 prefixEnd_93059 := by exact prefixLift 93059
  have htrace : WordTrace (prefixWord ++ tailWord_93059) baseStart_93059 baseEnd_93059 := by
    simpa [prefixWord, tailWord_93059, baseEnd_93059] using wordTrace_append hprefix tailTrace_93059
  have hstable : (prefixWord ++ tailWord_93059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93059).length < 2 ^ (prefixWord ++ tailWord_93059).sum := by decide
  have hdescent : baseEnd_93059 < baseStart_93059 := by decide
  rcases family_descends (prefixWord ++ tailWord_93059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93114 : List Nat := [3, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_93114 : Nat := 118140960795 + 93114 * 2 ^ 59
def prefixEnd_93114 : Nat := 4983230072969 + 3 ^ 40 * 93114 * 2
def baseEnd_93114 : Nat := 42499766811425710886029

theorem tailTrace_93114 : CollatzResearch.WordTrace tailWord_93114 prefixEnd_93114 42499766811425710886029 := by
  unfold tailWord_93114
  simp only [CollatzResearch.WordTrace]
  refine ⟨849036646167838862559599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2264097723114236966825597 849036646167838862559599)
  ·
    refine ⟨1273554969251758293839399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 849036646167838862559599 1273554969251758293839399)
    ·
      refine ⟨1910332453877637440759099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273554969251758293839399 1910332453877637440759099)
      ·
        refine ⟨2865498680816456161138649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910332453877637440759099 2865498680816456161138649)
        ·
          refine ⟨2149124010612342120853987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2865498680816456161138649 2149124010612342120853987)
          ·
            refine ⟨3223686015918513181280981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149124010612342120853987 3223686015918513181280981)
            ·
              refine ⟨75555140998090152686273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3223686015918513181280981 75555140998090152686273)
              ·
                refine ⟨56666355748567614514705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75555140998090152686273 56666355748567614514705)
                ·
                  refine ⟨42499766811425710886029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56666355748567614514705 42499766811425710886029)
                  ·
                    rfl

theorem cell20_93114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_93114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93114 prefixEnd_93114 := by exact prefixLift 93114
  have htrace : WordTrace (prefixWord ++ tailWord_93114) baseStart_93114 baseEnd_93114 := by
    simpa [prefixWord, tailWord_93114, baseEnd_93114] using wordTrace_append hprefix tailTrace_93114
  have hstable : (prefixWord ++ tailWord_93114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93114).length < 2 ^ (prefixWord ++ tailWord_93114).sum := by decide
  have hdescent : baseEnd_93114 < baseStart_93114 := by decide
  rcases family_descends (prefixWord ++ tailWord_93114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93128 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_93128 : Nat := 118140960795 + 93128 * 2 ^ 59
def prefixEnd_93128 : Nat := 4983230072969 + 3 ^ 40 * 93128 * 2
def baseEnd_93128 : Nat := 42506156792903884419305

theorem tailTrace_93128 : CollatzResearch.WordTrace tailWord_93128 prefixEnd_93128 42506156792903884419305 := by
  unfold tailWord_93128
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698328603310317920624019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2264438137747090560832025 1698328603310317920624019)
  ·
    refine ⟨2547492904965476880936029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698328603310317920624019 2547492904965476880936029)
    ·
      refine ⟨955309839362053830351011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2547492904965476880936029 955309839362053830351011)
      ·
        refine ⟨1432964759043080745526517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955309839362053830351011 1432964759043080745526517)
        ·
          refine ⟨134340446160288819893111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1432964759043080745526517 134340446160288819893111)
          ·
            refine ⟨201510669240433229839667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134340446160288819893111 201510669240433229839667)
            ·
              refine ⟨302266003860649844759501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201510669240433229839667 302266003860649844759501)
              ·
                refine ⟨113349751447743691784813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302266003860649844759501 113349751447743691784813)
                ·
                  refine ⟨42506156792903884419305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113349751447743691784813 42506156792903884419305)
                  ·
                    rfl

theorem cell20_93128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_93128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93128 prefixEnd_93128 := by exact prefixLift 93128
  have htrace : WordTrace (prefixWord ++ tailWord_93128) baseStart_93128 baseEnd_93128 := by
    simpa [prefixWord, tailWord_93128, baseEnd_93128] using wordTrace_append hprefix tailTrace_93128
  have hstable : (prefixWord ++ tailWord_93128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93128).length < 2 ^ (prefixWord ++ tailWord_93128).sum := by decide
  have hdescent : baseEnd_93128 < baseStart_93128 := by decide
  rcases family_descends (prefixWord ++ tailWord_93128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93169 : List Nat := [1, 2, 2, 2, 4, 3, 2, 2, 2]
def baseStart_93169 : Nat := 118140960795 + 93169 * 2 ^ 59
def prefixEnd_93169 : Nat := 4983230072969 + 3 ^ 40 * 93169 * 2
def baseEnd_93169 : Nat := 42524870310089964052471

theorem tailTrace_93169 : CollatzResearch.WordTrace tailWord_93169 prefixEnd_93169 42524870310089964052471 := by
  unfold tailWord_93169
  simp only [CollatzResearch.WordTrace]
  refine ⟨3398152599472099843490561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2265435066314733228993707 3398152599472099843490561)
  ·
    refine ⟨2548614449604074882617921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3398152599472099843490561 2548614449604074882617921)
    ·
      refine ⟨1911460837203056161963441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2548614449604074882617921 1911460837203056161963441)
      ·
        refine ⟨1433595627902292121472581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1911460837203056161963441 1433595627902292121472581)
        ·
          refine ⟨268799180231679772776109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1433595627902292121472581 268799180231679772776109)
          ·
            refine ⟨100799692586879914791041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268799180231679772776109 100799692586879914791041)
            ·
              refine ⟨75599769440159936093281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100799692586879914791041 75599769440159936093281)
              ·
                refine ⟨56699827080119952069961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75599769440159936093281 56699827080119952069961)
                ·
                  refine ⟨42524870310089964052471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56699827080119952069961 42524870310089964052471)
                  ·
                    rfl

theorem cell20_93169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_93169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93169 prefixEnd_93169 := by exact prefixLift 93169
  have htrace : WordTrace (prefixWord ++ tailWord_93169) baseStart_93169 baseEnd_93169 := by
    simpa [prefixWord, tailWord_93169, baseEnd_93169] using wordTrace_append hprefix tailTrace_93169
  have hstable : (prefixWord ++ tailWord_93169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93169).length < 2 ^ (prefixWord ++ tailWord_93169).sum := by decide
  have hdescent : baseEnd_93169 < baseStart_93169 := by decide
  rcases family_descends (prefixWord ++ tailWord_93169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93172 : List Nat := [2, 6, 2, 1, 1, 2, 1, 5]
def baseStart_93172 : Nat := 118140960795 + 93172 * 2 ^ 59
def prefixEnd_93172 : Nat := 4983230072969 + 3 ^ 40 * 93172 * 2
def baseEnd_93172 : Nat := 14175413197278428984153

theorem tailTrace_93172 : CollatzResearch.WordTrace tailWord_93172 prefixEnd_93172 14175413197278428984153 := by
  unfold tailWord_93172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699131009230615677924885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2265508012307487570566513 1699131009230615677924885)
  ·
    refine ⟨79646766057685109902729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1699131009230615677924885 79646766057685109902729)
    ·
      refine ⟨59735074543263832427047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79646766057685109902729 59735074543263832427047)
      ·
        refine ⟨89602611814895748640571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59735074543263832427047 89602611814895748640571)
        ·
          refine ⟨134403917722343622960857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89602611814895748640571 134403917722343622960857)
          ·
            refine ⟨100802938291757717220643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134403917722343622960857 100802938291757717220643)
            ·
              refine ⟨151204407437636575830965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100802938291757717220643 151204407437636575830965)
              ·
                refine ⟨14175413197278428984153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151204407437636575830965 14175413197278428984153)
                ·
                  rfl

theorem cell20_93172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_93172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93172 prefixEnd_93172 := by exact prefixLift 93172
  have htrace : WordTrace (prefixWord ++ tailWord_93172) baseStart_93172 baseEnd_93172 := by
    simpa [prefixWord, tailWord_93172, baseEnd_93172] using wordTrace_append hprefix tailTrace_93172
  have hstable : (prefixWord ++ tailWord_93172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93172).length < 2 ^ (prefixWord ++ tailWord_93172).sum := by decide
  have hdescent : baseEnd_93172 < baseStart_93172 := by decide
  rcases family_descends (prefixWord ++ tailWord_93172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93180 : List Nat := [2, 2, 2, 1, 2, 5, 1, 5]
def baseStart_93180 : Nat := 118140960795 + 93180 * 2 ^ 59
def prefixEnd_93180 : Nat := 4983230072969 + 3 ^ 40 * 93180 * 2
def baseEnd_93180 : Nat := 14176630336607604895253

theorem tailTrace_93180 : CollatzResearch.WordTrace tailWord_93180 prefixEnd_93180 14176630336607604895253 := by
  unfold tailWord_93180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699276901216124361070497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2265702534954832481427329 1699276901216124361070497)
  ·
    refine ⟨1274457675912093270802873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1699276901216124361070497 1274457675912093270802873)
    ·
      refine ⟨955843256934069953102155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1274457675912093270802873 955843256934069953102155)
      ·
        refine ⟨1433764885401104929653233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955843256934069953102155 1433764885401104929653233)
        ·
          refine ⟨1075323664050828697239925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1433764885401104929653233 1075323664050828697239925)
          ·
            refine ⟨100811593504765190366243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1075323664050828697239925 100811593504765190366243)
            ·
              refine ⟨151217390257147785549365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100811593504765190366243 151217390257147785549365)
              ·
                refine ⟨14176630336607604895253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151217390257147785549365 14176630336607604895253)
                ·
                  rfl

theorem cell20_93180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_93180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93180 prefixEnd_93180 := by exact prefixLift 93180
  have htrace : WordTrace (prefixWord ++ tailWord_93180) baseStart_93180 baseEnd_93180 := by
    simpa [prefixWord, tailWord_93180, baseEnd_93180] using wordTrace_append hprefix tailTrace_93180
  have hstable : (prefixWord ++ tailWord_93180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93180).length < 2 ^ (prefixWord ++ tailWord_93180).sum := by decide
  have hdescent : baseEnd_93180 < baseStart_93180 := by decide
  rcases family_descends (prefixWord ++ tailWord_93180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93194 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_93194 : Nat := 118140960795 + 93194 * 2 ^ 59
def prefixEnd_93194 : Nat := 4983230072969 + 3 ^ 40 * 93194 * 2
def baseEnd_93194 : Nat := 42536280991300988219035

theorem tailTrace_93194 : CollatzResearch.WordTrace tailWord_93194 prefixEnd_93194 42536280991300988219035 := by
  unfold tailWord_93194
  simp only [CollatzResearch.WordTrace]
  refine ⟨849766106095382278287659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2266042949587686075433757 849766106095382278287659)
  ·
    refine ⟨1274649159143073417431489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 849766106095382278287659 1274649159143073417431489)
    ·
      refine ⟨955986869357305063073617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1274649159143073417431489 955986869357305063073617)
      ·
        refine ⟨716990152017978797305213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955986869357305063073617 716990152017978797305213)
        ·
          refine ⟨268871307006742048989455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 716990152017978797305213 268871307006742048989455)
          ·
            refine ⟨403306960510113073484183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268871307006742048989455 403306960510113073484183)
            ·
              refine ⟨604960440765169610226275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403306960510113073484183 604960440765169610226275)
              ·
                refine ⟨907440661147754415339413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604960440765169610226275 907440661147754415339413)
                ·
                  refine ⟨42536280991300988219035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 907440661147754415339413 42536280991300988219035)
                  ·
                    rfl

theorem cell20_93194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_93194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93194 prefixEnd_93194 := by exact prefixLift 93194
  have htrace : WordTrace (prefixWord ++ tailWord_93194) baseStart_93194 baseEnd_93194 := by
    simpa [prefixWord, tailWord_93194, baseEnd_93194] using wordTrace_append hprefix tailTrace_93194
  have hstable : (prefixWord ++ tailWord_93194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93194).length < 2 ^ (prefixWord ++ tailWord_93194).sum := by decide
  have hdescent : baseEnd_93194 < baseStart_93194 := by decide
  rcases family_descends (prefixWord ++ tailWord_93194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93232 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_93232 : Nat := 118140960795 + 93232 * 2 ^ 59
def prefixEnd_93232 : Nat := 4983230072969 + 3 ^ 40 * 93232 * 2
def baseEnd_93232 : Nat := 42553625226741744952213

theorem tailTrace_93232 : CollatzResearch.WordTrace tailWord_93232 prefixEnd_93232 42553625226741744952213 := by
  unfold tailWord_93232
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700225199121930801516975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2266966932162574402022633 1700225199121930801516975)
  ·
    refine ⟨2550337798682896202275463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1700225199121930801516975 2550337798682896202275463)
    ·
      refine ⟨3825506698024344303413195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550337798682896202275463 3825506698024344303413195)
      ·
        refine ⟨5738260047036516455119793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825506698024344303413195 5738260047036516455119793)
        ·
          refine ⟨4303695035277387341339845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5738260047036516455119793 4303695035277387341339845)
          ·
            refine ⟨806942819114510126501221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4303695035277387341339845 806942819114510126501221)
            ·
              refine ⟨151301778583970648718979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 806942819114510126501221 151301778583970648718979)
              ·
                refine ⟨226952667875955973078469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151301778583970648718979 226952667875955973078469)
                ·
                  refine ⟨42553625226741744952213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226952667875955973078469 42553625226741744952213)
                  ·
                    rfl

theorem cell20_93232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_93232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93232 prefixEnd_93232 := by exact prefixLift 93232
  have htrace : WordTrace (prefixWord ++ tailWord_93232) baseStart_93232 baseEnd_93232 := by
    simpa [prefixWord, tailWord_93232, baseEnd_93232] using wordTrace_append hprefix tailTrace_93232
  have hstable : (prefixWord ++ tailWord_93232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93232).length < 2 ^ (prefixWord ++ tailWord_93232).sum := by decide
  have hdescent : baseEnd_93232 < baseStart_93232 := by decide
  rcases family_descends (prefixWord ++ tailWord_93232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93266 : List Nat := [3, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_93266 : Nat := 118140960795 + 93266 * 2 ^ 59
def prefixEnd_93266 : Nat := 4983230072969 + 3 ^ 40 * 93266 * 2
def baseEnd_93266 : Nat := 42569143753188737818741

theorem tailTrace_93266 : CollatzResearch.WordTrace tailWord_93266 prefixEnd_93266 42569143753188737818741 := by
  unfold tailWord_93266
  simp only [CollatzResearch.WordTrace]
  refine ⟨850422620030171352442913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2267793653413790273181101 850422620030171352442913)
  ·
    refine ⟨637816965022628514332185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 850422620030171352442913 637816965022628514332185)
    ·
      refine ⟨478362723766971385749139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 637816965022628514332185 478362723766971385749139)
      ·
        refine ⟨717544085650457078623709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478362723766971385749139 717544085650457078623709)
        ·
          refine ⟨269079032118921404483891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 717544085650457078623709 269079032118921404483891)
          ·
            refine ⟨403618548178382106725837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269079032118921404483891 403618548178382106725837)
            ·
              refine ⟨151356955566893290022189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 403618548178382106725837 151356955566893290022189)
              ·
                refine ⟨56758858337584983758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151356955566893290022189 56758858337584983758321)
                ·
                  refine ⟨42569143753188737818741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56758858337584983758321 42569143753188737818741)
                  ·
                    rfl

theorem cell20_93266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_93266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93266 prefixEnd_93266 := by exact prefixLift 93266
  have htrace : WordTrace (prefixWord ++ tailWord_93266) baseStart_93266 baseEnd_93266 := by
    simpa [prefixWord, tailWord_93266, baseEnd_93266] using wordTrace_append hprefix tailTrace_93266
  have hstable : (prefixWord ++ tailWord_93266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93266).length < 2 ^ (prefixWord ++ tailWord_93266).sum := by decide
  have hdescent : baseEnd_93266 < baseStart_93266 := by decide
  rcases family_descends (prefixWord ++ tailWord_93266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93287 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 4]
def baseStart_93287 : Nat := 118140960795 + 93287 * 2 ^ 59
def prefixEnd_93287 : Nat := 4983230072969 + 3 ^ 40 * 93287 * 2
def baseEnd_93287 : Nat := 42578728725405998118655

theorem tailTrace_93287 : CollatzResearch.WordTrace tailWord_93287 prefixEnd_93287 42578728725405998118655 := by
  unfold tailWord_93287
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402456413044605996286115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2268304275363070664190743 3402456413044605996286115)
  ·
    refine ⟨5103684619566908994429173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3402456413044605996286115 5103684619566908994429173)
    ·
      refine ⟨478470433084397718227735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5103684619566908994429173 478470433084397718227735)
      ·
        refine ⟨717705649626596577341603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478470433084397718227735 717705649626596577341603)
        ·
          refine ⟨1076558474439894866012405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717705649626596577341603 1076558474439894866012405)
          ·
            refine ⟨100927356978740143688663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1076558474439894866012405 100927356978740143688663)
            ·
              refine ⟨151391035468110215532995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100927356978740143688663 151391035468110215532995)
              ·
                refine ⟨227086553202165323299493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151391035468110215532995 227086553202165323299493)
                ·
                  refine ⟨42578728725405998118655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227086553202165323299493 42578728725405998118655)
                  ·
                    rfl

theorem cell20_93287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_93287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93287 prefixEnd_93287 := by exact prefixLift 93287
  have htrace : WordTrace (prefixWord ++ tailWord_93287) baseStart_93287 baseEnd_93287 := by
    simpa [prefixWord, tailWord_93287, baseEnd_93287] using wordTrace_append hprefix tailTrace_93287
  have hstable : (prefixWord ++ tailWord_93287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93287).length < 2 ^ (prefixWord ++ tailWord_93287).sum := by decide
  have hdescent : baseEnd_93287 < baseStart_93287 := by decide
  rcases family_descends (prefixWord ++ tailWord_93287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93294 : List Nat := [4, 1, 2, 2, 1, 3, 2, 5]
def baseStart_93294 : Nat := 118140960795 + 93294 * 2 ^ 59
def prefixEnd_93294 : Nat := 4983230072969 + 3 ^ 40 * 93294 * 2
def baseEnd_93294 : Nat := 14193974572048361628431

theorem tailTrace_93294 : CollatzResearch.WordTrace tailWord_93294 prefixEnd_93294 14193974572048361628431 := by
  unfold tailWord_93294
  simp only [CollatzResearch.WordTrace]
  refine ⟨425338965502405773973867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2268474482679497461193957 425338965502405773973867)
  ·
    refine ⟨638008448253608660960801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425338965502405773973867 638008448253608660960801)
    ·
      refine ⟨478506336190206495720601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638008448253608660960801 478506336190206495720601)
      ·
        refine ⟨358879752142654871790451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478506336190206495720601 358879752142654871790451)
        ·
          refine ⟨538319628213982307685677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358879752142654871790451 538319628213982307685677)
          ·
            refine ⟨201869860580243365382129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 538319628213982307685677 201869860580243365382129)
            ·
              refine ⟨151402395435182524036597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201869860580243365382129 151402395435182524036597)
              ·
                refine ⟨14193974572048361628431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151402395435182524036597 14193974572048361628431)
                ·
                  rfl

theorem cell20_93294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_93294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93294 prefixEnd_93294 := by exact prefixLift 93294
  have htrace : WordTrace (prefixWord ++ tailWord_93294) baseStart_93294 baseEnd_93294 := by
    simpa [prefixWord, tailWord_93294, baseEnd_93294] using wordTrace_append hprefix tailTrace_93294
  have hstable : (prefixWord ++ tailWord_93294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93294).length < 2 ^ (prefixWord ++ tailWord_93294).sum := by decide
  have hdescent : baseEnd_93294 < baseStart_93294 := by decide
  rcases family_descends (prefixWord ++ tailWord_93294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93422 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_93422 : Nat := 118140960795 + 93422 * 2 ^ 59
def prefixEnd_93422 : Nat := 4983230072969 + 3 ^ 40 * 93422 * 2
def baseEnd_93422 : Nat := 42640346403945528618103

theorem tailTrace_93422 : CollatzResearch.WordTrace tailWord_93422 prefixEnd_93422 42640346403945528618103 := by
  unfold tailWord_93422
  simp only [CollatzResearch.WordTrace]
  refine ⟨425922533444440506556315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2271586845037016034967013 425922533444440506556315)
  ·
    refine ⟨638883800166660759834473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425922533444440506556315 638883800166660759834473)
    ·
      refine ⟨479162850124995569875855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638883800166660759834473 479162850124995569875855)
      ·
        refine ⟨718744275187493354813783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479162850124995569875855 718744275187493354813783)
        ·
          refine ⟨1078116412781240032220675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718744275187493354813783 1078116412781240032220675)
          ·
            refine ⟨1617174619171860048331013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078116412781240032220675 1617174619171860048331013)
            ·
              refine ⟨303220241094723759062065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1617174619171860048331013 303220241094723759062065)
              ·
                refine ⟨227415180821042819296549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303220241094723759062065 227415180821042819296549)
                ·
                  refine ⟨42640346403945528618103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227415180821042819296549 42640346403945528618103)
                  ·
                    rfl

theorem cell20_93422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_93422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93422 prefixEnd_93422 := by exact prefixLift 93422
  have htrace : WordTrace (prefixWord ++ tailWord_93422) baseStart_93422 baseEnd_93422 := by
    simpa [prefixWord, tailWord_93422, baseEnd_93422] using wordTrace_append hprefix tailTrace_93422
  have hstable : (prefixWord ++ tailWord_93422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93422).length < 2 ^ (prefixWord ++ tailWord_93422).sum := by decide
  have hdescent : baseEnd_93422 < baseStart_93422 := by decide
  rcases family_descends (prefixWord ++ tailWord_93422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93439 : List Nat := [1, 1, 2, 2, 1, 5, 3, 3, 2]
def baseStart_93439 : Nat := 118140960795 + 93439 * 2 ^ 59
def prefixEnd_93439 : Nat := 4983230072969 + 3 ^ 40 * 93439 * 2
def baseEnd_93439 : Nat := 42648105667169025051367

theorem tailTrace_93439 : CollatzResearch.WordTrace tailWord_93439 prefixEnd_93439 42648105667169025051367 := by
  unfold tailWord_93439
  simp only [CollatzResearch.WordTrace]
  refine ⟨3408000308493935955819371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2272000205662623970546247 3408000308493935955819371)
  ·
    refine ⟨5112000462740903933729057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3408000308493935955819371 5112000462740903933729057)
    ·
      refine ⟨3834000347055677950296793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5112000462740903933729057 3834000347055677950296793)
      ·
        refine ⟨2875500260291758462722595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3834000347055677950296793 2875500260291758462722595)
        ·
          refine ⟨4313250390437637694083893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875500260291758462722595 4313250390437637694083893)
          ·
            refine ⟨404367224103528533820365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4313250390437637694083893 404367224103528533820365)
            ·
              refine ⟨151637709038823200182637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404367224103528533820365 151637709038823200182637)
              ·
                refine ⟨56864140889558700068489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151637709038823200182637 56864140889558700068489)
                ·
                  refine ⟨42648105667169025051367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56864140889558700068489 42648105667169025051367)
                  ·
                    rfl

theorem cell20_93439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 2].length) (baseStart_93439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93439 prefixEnd_93439 := by exact prefixLift 93439
  have htrace : WordTrace (prefixWord ++ tailWord_93439) baseStart_93439 baseEnd_93439 := by
    simpa [prefixWord, tailWord_93439, baseEnd_93439] using wordTrace_append hprefix tailTrace_93439
  have hstable : (prefixWord ++ tailWord_93439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93439).length < 2 ^ (prefixWord ++ tailWord_93439).sum := by decide
  have hdescent : baseEnd_93439 < baseStart_93439 := by decide
  rcases family_descends (prefixWord ++ tailWord_93439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93488 : List Nat := [2, 1, 1, 1, 2, 2, 3, 8]
def baseStart_93488 : Nat := 118140960795 + 93488 * 2 ^ 59
def prefixEnd_93488 : Nat := 4983230072969 + 3 ^ 40 * 93488 * 2
def baseEnd_93488 : Nat := 14223490200780877472611

theorem tailTrace_93488 : CollatzResearch.WordTrace tailWord_93488 prefixEnd_93488 14223490200780877472611 := by
  unfold tailWord_93488
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704893742658208662176559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2273191656877611549568745 1704893742658208662176559)
  ·
    refine ⟨2557340613987312993264839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1704893742658208662176559 2557340613987312993264839)
    ·
      refine ⟨3836010920980969489897259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557340613987312993264839 3836010920980969489897259)
      ·
        refine ⟨5754016381471454234845889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3836010920980969489897259 5754016381471454234845889)
        ·
          refine ⟨4315512286103590676134417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5754016381471454234845889 4315512286103590676134417)
          ·
            refine ⟨3236634214577693007100813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4315512286103590676134417 3236634214577693007100813)
            ·
              refine ⟨1213737830466634877662805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3236634214577693007100813 1213737830466634877662805)
              ·
                refine ⟨14223490200780877472611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1213737830466634877662805 14223490200780877472611)
                ·
                  rfl

theorem cell20_93488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_93488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93488 prefixEnd_93488 := by exact prefixLift 93488
  have htrace : WordTrace (prefixWord ++ tailWord_93488) baseStart_93488 baseEnd_93488 := by
    simpa [prefixWord, tailWord_93488, baseEnd_93488] using wordTrace_append hprefix tailTrace_93488
  have hstable : (prefixWord ++ tailWord_93488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93488).length < 2 ^ (prefixWord ++ tailWord_93488).sum := by decide
  have hdescent : baseEnd_93488 < baseStart_93488 := by decide
  rcases family_descends (prefixWord ++ tailWord_93488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93505 : List Nat := [1, 2, 5, 2, 1, 9]
def baseStart_93505 : Nat := 118140960795 + 93505 * 2 ^ 59
def prefixEnd_93505 : Nat := 4983230072969 + 3 ^ 40 * 93505 * 2
def baseEnd_93505 : Nat := 1580675180206152920411

theorem tailTrace_93505 : CollatzResearch.WordTrace tailWord_93505 prefixEnd_93505 1580675180206152920411 := by
  unfold tailWord_93505
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410407526254829227721969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2273605017503219485147979 3410407526254829227721969)
  ·
    refine ⟨2557805644691121920791477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3410407526254829227721969 2557805644691121920791477)
    ·
      refine ⟨239794279189792680074201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2557805644691121920791477 239794279189792680074201)
      ·
        refine ⟨179845709392344510055651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239794279189792680074201 179845709392344510055651)
        ·
          refine ⟨269768564088516765083477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179845709392344510055651 269768564088516765083477)
          ·
            refine ⟨1580675180206152920411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 269768564088516765083477 1580675180206152920411)
            ·
              rfl

theorem cell20_93505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 9].length) (baseStart_93505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93505 prefixEnd_93505 := by exact prefixLift 93505
  have htrace : WordTrace (prefixWord ++ tailWord_93505) baseStart_93505 baseEnd_93505 := by
    simpa [prefixWord, tailWord_93505, baseEnd_93505] using wordTrace_append hprefix tailTrace_93505
  have hstable : (prefixWord ++ tailWord_93505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93505).length < 2 ^ (prefixWord ++ tailWord_93505).sum := by decide
  have hdescent : baseEnd_93505 < baseStart_93505 := by decide
  rcases family_descends (prefixWord ++ tailWord_93505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93508 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_93508 : Nat := 118140960795 + 93508 * 2 ^ 59
def prefixEnd_93508 : Nat := 4983230072969 + 3 ^ 40 * 93508 * 2
def baseEnd_93508 : Nat := 42679599147311451751085

theorem tailTrace_93508 : CollatzResearch.WordTrace tailWord_93508 prefixEnd_93508 42679599147311451751085 := by
  unfold tailWord_93508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705258472621980370040589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2273677963495973826720785 1705258472621980370040589)
  ·
    refine ⟨639471927233242638765221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1705258472621980370040589 639471927233242638765221)
    ·
      refine ⟨119900986356232994768479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 639471927233242638765221 119900986356232994768479)
      ·
        refine ⟨179851479534349492152719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119900986356232994768479 179851479534349492152719)
        ·
          refine ⟨269777219301524238229079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179851479534349492152719 269777219301524238229079)
          ·
            refine ⟨404665828952286357343619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269777219301524238229079 404665828952286357343619)
            ·
              refine ⟨606998743428429536015429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404665828952286357343619 606998743428429536015429)
              ·
                refine ⟨113812264392830538002893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606998743428429536015429 113812264392830538002893)
                ·
                  refine ⟨42679599147311451751085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113812264392830538002893 42679599147311451751085)
                  ·
                    rfl

theorem cell20_93508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_93508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93508 prefixEnd_93508 := by exact prefixLift 93508
  have htrace : WordTrace (prefixWord ++ tailWord_93508) baseStart_93508 baseEnd_93508 := by
    simpa [prefixWord, tailWord_93508, baseEnd_93508] using wordTrace_append hprefix tailTrace_93508
  have hstable : (prefixWord ++ tailWord_93508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93508).length < 2 ^ (prefixWord ++ tailWord_93508).sum := by decide
  have hdescent : baseEnd_93508 < baseStart_93508 := by decide
  rcases family_descends (prefixWord ++ tailWord_93508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93536 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_93536 : Nat := 118140960795 + 93536 * 2 ^ 59
def prefixEnd_93536 : Nat := 4983230072969 + 3 ^ 40 * 93536 * 2
def baseEnd_93536 : Nat := 42692379110267798817637

theorem tailTrace_93536 : CollatzResearch.WordTrace tailWord_93536 prefixEnd_93536 42692379110267798817637 := by
  unfold tailWord_93536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705769094571260761050231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2274358792761681014733641 1705769094571260761050231)
  ·
    refine ⟨2558653641856891141575347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1705769094571260761050231 2558653641856891141575347)
    ·
      refine ⟨3837980462785336712363021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558653641856891141575347 3837980462785336712363021)
      ·
        refine ⟨1439242673544501267136133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3837980462785336712363021 1439242673544501267136133)
        ·
          refine ⟨269858001289593987588025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1439242673544501267136133 269858001289593987588025)
          ·
            refine ⟨202393500967195490691019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269858001289593987588025 202393500967195490691019)
            ·
              refine ⟨303590251450793236036529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202393500967195490691019 303590251450793236036529)
              ·
                refine ⟨227692688588094927027397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303590251450793236036529 227692688588094927027397)
                ·
                  refine ⟨42692379110267798817637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227692688588094927027397 42692379110267798817637)
                  ·
                    rfl

theorem cell20_93536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_93536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93536 prefixEnd_93536 := by exact prefixLift 93536
  have htrace : WordTrace (prefixWord ++ tailWord_93536) baseStart_93536 baseEnd_93536 := by
    simpa [prefixWord, tailWord_93536, baseEnd_93536] using wordTrace_append hprefix tailTrace_93536
  have hstable : (prefixWord ++ tailWord_93536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93536).length < 2 ^ (prefixWord ++ tailWord_93536).sum := by decide
  have hdescent : baseEnd_93536 < baseStart_93536 := by decide
  rcases family_descends (prefixWord ++ tailWord_93536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93564 : List Nat := [2, 2, 2, 1, 1, 1, 11]
def baseStart_93564 : Nat := 118140960795 + 93564 * 2 ^ 59
def prefixEnd_93564 : Nat := 4983230072969 + 3 ^ 40 * 93564 * 2
def baseEnd_93564 : Nat := 4745017674802682876021

theorem tailTrace_93564 : CollatzResearch.WordTrace tailWord_93564 prefixEnd_93564 4745017674802682876021 := by
  unfold tailWord_93564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706279716520541152059873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2275039622027388202746497 1706279716520541152059873)
  ·
    refine ⟨1279709787390405864044905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1706279716520541152059873 1279709787390405864044905)
    ·
      refine ⟨959782340542804398033679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1279709787390405864044905 959782340542804398033679)
      ·
        refine ⟨1439673510814206597050519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959782340542804398033679 1439673510814206597050519)
        ·
          refine ⟨2159510266221309895575779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439673510814206597050519 2159510266221309895575779)
          ·
            refine ⟨3239265399331964843363669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159510266221309895575779 3239265399331964843363669)
            ·
              refine ⟨4745017674802682876021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3239265399331964843363669 4745017674802682876021)
              ·
                rfl

theorem cell20_93564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 11].length) (baseStart_93564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93564 prefixEnd_93564 := by exact prefixLift 93564
  have htrace : WordTrace (prefixWord ++ tailWord_93564) baseStart_93564 baseEnd_93564 := by
    simpa [prefixWord, tailWord_93564, baseEnd_93564] using wordTrace_append hprefix tailTrace_93564
  have hstable : (prefixWord ++ tailWord_93564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93564).length < 2 ^ (prefixWord ++ tailWord_93564).sum := by decide
  have hdescent : baseEnd_93564 < baseStart_93564 := by decide
  rcases family_descends (prefixWord ++ tailWord_93564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93570 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_93570 : Nat := 118140960795 + 93570 * 2 ^ 59
def prefixEnd_93570 : Nat := 4983230072969 + 3 ^ 40 * 93570 * 2
def baseEnd_93570 : Nat := 42707897636714791684165

theorem tailTrace_93570 : CollatzResearch.WordTrace tailWord_93570 prefixEnd_93570 42707897636714791684165 := by
  unfold tailWord_93570
  simp only [CollatzResearch.WordTrace]
  refine ⟨853194567754836332209541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2275185514012896885892109 853194567754836332209541)
  ·
    refine ⟨159973981454031812289289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 853194567754836332209541 159973981454031812289289)
    ·
      refine ⟨119980486090523859216967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159973981454031812289289 119980486090523859216967)
      ·
        refine ⟨179970729135785788825451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119980486090523859216967 179970729135785788825451)
        ·
          refine ⟨269956093703678683238177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179970729135785788825451 269956093703678683238177)
          ·
            refine ⟨202467070277759012428633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269956093703678683238177 202467070277759012428633)
            ·
              refine ⟨151850302708319259321475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202467070277759012428633 151850302708319259321475)
              ·
                refine ⟨227775454062478888982213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151850302708319259321475 227775454062478888982213)
                ·
                  refine ⟨42707897636714791684165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227775454062478888982213 42707897636714791684165)
                  ·
                    rfl

theorem cell20_93570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_93570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93570 prefixEnd_93570 := by exact prefixLift 93570
  have htrace : WordTrace (prefixWord ++ tailWord_93570) baseStart_93570 baseEnd_93570 := by
    simpa [prefixWord, tailWord_93570, baseEnd_93570] using wordTrace_append hprefix tailTrace_93570
  have hstable : (prefixWord ++ tailWord_93570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93570).length < 2 ^ (prefixWord ++ tailWord_93570).sum := by decide
  have hdescent : baseEnd_93570 < baseStart_93570 := by decide
  rcases family_descends (prefixWord ++ tailWord_93570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93636 : List Nat := [2, 3, 3, 2, 1, 2, 2, 5]
def baseStart_93636 : Nat := 118140960795 + 93636 * 2 ^ 59
def prefixEnd_93636 : Nat := 4983230072969 + 3 ^ 40 * 93636 * 2
def baseEnd_93636 : Nat := 14246007278370631827965

theorem tailTrace_93636 : CollatzResearch.WordTrace tailWord_93636 prefixEnd_93636 14246007278370631827965 := by
  unfold tailWord_93636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707592744390119300370381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2276790325853492400493841 1707592744390119300370381)
  ·
    refine ⟨640347279146294737638893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1707592744390119300370381 640347279146294737638893)
    ·
      refine ⟨240130229679860526614585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 640347279146294737638893 240130229679860526614585)
      ·
        refine ⟨180097672259895394960939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240130229679860526614585 180097672259895394960939)
        ·
          refine ⟨270146508389843092441409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180097672259895394960939 270146508389843092441409)
          ·
            refine ⟨202609881292382319331057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270146508389843092441409 202609881292382319331057)
            ·
              refine ⟨151957410969286739498293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202609881292382319331057 151957410969286739498293)
              ·
                refine ⟨14246007278370631827965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151957410969286739498293 14246007278370631827965)
                ·
                  rfl

theorem cell20_93636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_93636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93636 prefixEnd_93636 := by exact prefixLift 93636
  have htrace : WordTrace (prefixWord ++ tailWord_93636) baseStart_93636 baseEnd_93636 := by
    simpa [prefixWord, tailWord_93636, baseEnd_93636] using wordTrace_append hprefix tailTrace_93636
  have hstable : (prefixWord ++ tailWord_93636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93636).length < 2 ^ (prefixWord ++ tailWord_93636).sum := by decide
  have hdescent : baseEnd_93636 < baseStart_93636 := by decide
  rcases family_descends (prefixWord ++ tailWord_93636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93643 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 3]
def baseStart_93643 : Nat := 118140960795 + 93643 * 2 ^ 59
def prefixEnd_93643 : Nat := 4983230072969 + 3 ^ 40 * 93643 * 2
def baseEnd_93643 : Nat := 42741216825850982250533

theorem tailTrace_93643 : CollatzResearch.WordTrace tailWord_93643 prefixEnd_93643 42741216825850982250533 := by
  unfold tailWord_93643
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415440799754878796245583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2276960533169919197497055 3415440799754878796245583)
  ·
    refine ⟨5123161199632318194368375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3415440799754878796245583 5123161199632318194368375)
    ·
      refine ⟨7684741799448477291552563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5123161199632318194368375 7684741799448477291552563)
      ·
        refine ⟨11527112699172715937328845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7684741799448477291552563 11527112699172715937328845)
        ·
          refine ⟨4322667262189768476498317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11527112699172715937328845 4322667262189768476498317)
          ·
            refine ⟨1621000223321163178686869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4322667262189768476498317 1621000223321163178686869)
            ·
              refine ⟨75984385468179524000947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1621000223321163178686869 75984385468179524000947)
              ·
                refine ⟨113976578202269286001421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75984385468179524000947 113976578202269286001421)
                ·
                  refine ⟨42741216825850982250533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113976578202269286001421 42741216825850982250533)
                  ·
                    rfl

theorem cell20_93643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 3].length) (baseStart_93643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93643 prefixEnd_93643 := by exact prefixLift 93643
  have htrace : WordTrace (prefixWord ++ tailWord_93643) baseStart_93643 baseEnd_93643 := by
    simpa [prefixWord, tailWord_93643, baseEnd_93643] using wordTrace_append hprefix tailTrace_93643
  have hstable : (prefixWord ++ tailWord_93643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93643).length < 2 ^ (prefixWord ++ tailWord_93643).sum := by decide
  have hdescent : baseEnd_93643 < baseStart_93643 := by decide
  rcases family_descends (prefixWord ++ tailWord_93643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93681 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 3]
def baseStart_93681 : Nat := 118140960795 + 93681 * 2 ^ 59
def prefixEnd_93681 : Nat := 4983230072969 + 3 ^ 40 * 93681 * 2
def baseEnd_93681 : Nat := 42758561061291738983711

theorem tailTrace_93681 : CollatzResearch.WordTrace tailWord_93681 prefixEnd_93681 42758561061291738983711 := by
  unfold tailWord_93681
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416826773617211286128897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2277884515744807524085931 3416826773617211286128897)
  ·
    refine ⟨2562620080212908464596673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3416826773617211286128897 2562620080212908464596673)
    ·
      refine ⟨1921965060159681348447505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2562620080212908464596673 1921965060159681348447505)
      ·
        refine ⟨1441473795119761011335629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1921965060159681348447505 1441473795119761011335629)
        ·
          refine ⟨540552673169910379250861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1441473795119761011335629 540552673169910379250861)
          ·
            refine ⟨202707252438716392219073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540552673169910379250861 202707252438716392219073)
            ·
              refine ⟨152030439329037294164305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202707252438716392219073 152030439329037294164305)
              ·
                refine ⟨114022829496777970623229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152030439329037294164305 114022829496777970623229)
                ·
                  refine ⟨42758561061291738983711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114022829496777970623229 42758561061291738983711)
                  ·
                    rfl

theorem cell20_93681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_93681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93681 prefixEnd_93681 := by exact prefixLift 93681
  have htrace : WordTrace (prefixWord ++ tailWord_93681) baseStart_93681 baseEnd_93681 := by
    simpa [prefixWord, tailWord_93681, baseEnd_93681] using wordTrace_append hprefix tailTrace_93681
  have hstable : (prefixWord ++ tailWord_93681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93681).length < 2 ^ (prefixWord ++ tailWord_93681).sum := by decide
  have hdescent : baseEnd_93681 < baseStart_93681 := by decide
  rcases family_descends (prefixWord ++ tailWord_93681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93698 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_93698 : Nat := 118140960795 + 93698 * 2 ^ 59
def prefixEnd_93698 : Nat := 4983230072969 + 3 ^ 40 * 93698 * 2
def baseEnd_93698 : Nat := 42766320324515235416975

theorem tailTrace_93698 : CollatzResearch.WordTrace tailWord_93698 prefixEnd_93698 42766320324515235416975 := by
  unfold tailWord_93698
  simp only [CollatzResearch.WordTrace]
  refine ⟨854361703638905797374437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2278297876370415459665165 854361703638905797374437)
  ·
    refine ⟨160192819432294837007707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 854361703638905797374437 160192819432294837007707)
    ·
      refine ⟨240289229148442255511561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160192819432294837007707 240289229148442255511561)
      ·
        refine ⟨180216921861331691633671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240289229148442255511561 180216921861331691633671)
        ·
          refine ⟨270325382791997537450507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180216921861331691633671 270325382791997537450507)
          ·
            refine ⟨405488074187996306175761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270325382791997537450507 405488074187996306175761)
            ·
              refine ⟨304116055640997229631821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405488074187996306175761 304116055640997229631821)
              ·
                refine ⟨114043520865373961111933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304116055640997229631821 114043520865373961111933)
                ·
                  refine ⟨42766320324515235416975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114043520865373961111933 42766320324515235416975)
                  ·
                    rfl

theorem cell20_93698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_93698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93698 prefixEnd_93698 := by exact prefixLift 93698
  have htrace : WordTrace (prefixWord ++ tailWord_93698) baseStart_93698 baseEnd_93698 := by
    simpa [prefixWord, tailWord_93698, baseEnd_93698] using wordTrace_append hprefix tailTrace_93698
  have hstable : (prefixWord ++ tailWord_93698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93698).length < 2 ^ (prefixWord ++ tailWord_93698).sum := by decide
  have hdescent : baseEnd_93698 < baseStart_93698 := by decide
  rcases family_descends (prefixWord ++ tailWord_93698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93747 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_93747 : Nat := 118140960795 + 93747 * 2 ^ 59
def prefixEnd_93747 : Nat := 4983230072969 + 3 ^ 40 * 93747 * 2
def baseEnd_93747 : Nat := 42788685259688842783441

theorem tailTrace_93747 : CollatzResearch.WordTrace tailWord_93747 prefixEnd_93747 42788685259688842783441 := by
  unfold tailWord_93747
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419233991378104558031495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2279489327585403038687663 3419233991378104558031495)
  ·
    refine ⟨5128850987067156837047243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3419233991378104558031495 5128850987067156837047243)
    ·
      refine ⟨7693276480600735255570865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5128850987067156837047243 7693276480600735255570865)
      ·
        refine ⟨5769957360450551441678149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7693276480600735255570865 5769957360450551441678149)
        ·
          refine ⟨1081867005084478395314653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5769957360450551441678149 1081867005084478395314653)
          ·
            refine ⟨405700126906679398242995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1081867005084478395314653 405700126906679398242995)
            ·
              refine ⟨608550190360019097364493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405700126906679398242995 608550190360019097364493)
              ·
                refine ⟨228206321385007161511685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608550190360019097364493 228206321385007161511685)
                ·
                  refine ⟨42788685259688842783441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228206321385007161511685 42788685259688842783441)
                  ·
                    rfl

theorem cell20_93747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_93747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93747 prefixEnd_93747 := by exact prefixLift 93747
  have htrace : WordTrace (prefixWord ++ tailWord_93747) baseStart_93747 baseEnd_93747 := by
    simpa [prefixWord, tailWord_93747, baseEnd_93747] using wordTrace_append hprefix tailTrace_93747
  have hstable : (prefixWord ++ tailWord_93747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93747).length < 2 ^ (prefixWord ++ tailWord_93747).sum := by decide
  have hdescent : baseEnd_93747 < baseStart_93747 := by decide
  rcases family_descends (prefixWord ++ tailWord_93747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93754 : List Nat := [3, 1, 1, 1, 3, 2, 2, 7]
def baseStart_93754 : Nat := 118140960795 + 93754 * 2 ^ 59
def prefixEnd_93754 : Nat := 4983230072969 + 3 ^ 40 * 93754 * 2
def baseEnd_93754 : Nat := 14263960083475976516693

theorem tailTrace_93754 : CollatzResearch.WordTrace tailWord_93754 prefixEnd_93754 14263960083475976516693 := by
  unfold tailWord_93754
  simp only [CollatzResearch.WordTrace]
  refine ⟨854872325588186188384079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2279659534901829835690877 854872325588186188384079)
  ·
    refine ⟨1282308488382279282576119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 854872325588186188384079 1282308488382279282576119)
    ·
      refine ⟨1923462732573418923864179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282308488382279282576119 1923462732573418923864179)
      ·
        refine ⟨2885194098860128385796269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923462732573418923864179 2885194098860128385796269)
        ·
          refine ⟨1081947787072548144673601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2885194098860128385796269 1081947787072548144673601)
          ·
            refine ⟨811460840304411108505201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081947787072548144673601 811460840304411108505201)
            ·
              refine ⟨608595630228308331378901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811460840304411108505201 608595630228308331378901)
              ·
                refine ⟨14263960083475976516693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 608595630228308331378901 14263960083475976516693)
                ·
                  rfl

theorem cell20_93754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_93754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93754 prefixEnd_93754 := by exact prefixLift 93754
  have htrace : WordTrace (prefixWord ++ tailWord_93754) baseStart_93754 baseEnd_93754 := by
    simpa [prefixWord, tailWord_93754, baseEnd_93754] using wordTrace_append hprefix tailTrace_93754
  have hstable : (prefixWord ++ tailWord_93754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93754).length < 2 ^ (prefixWord ++ tailWord_93754).sum := by decide
  have hdescent : baseEnd_93754 < baseStart_93754 := by decide
  rcases family_descends (prefixWord ++ tailWord_93754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93767 : List Nat := [1, 1, 4, 1, 6, 1, 2, 4]
def baseStart_93767 : Nat := 118140960795 + 93767 * 2 ^ 59
def prefixEnd_93767 : Nat := 4983230072969 + 3 ^ 40 * 93767 * 2
def baseEnd_93767 : Nat := 14265937934885887372231

theorem tailTrace_93767 : CollatzResearch.WordTrace tailWord_93767 prefixEnd_93767 14265937934885887372231 := by
  unfold tailWord_93767
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419963451305647973759555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2279975634203765315839703 3419963451305647973759555)
  ·
    refine ⟨5129945176958471960639333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3419963451305647973759555 5129945176958471960639333)
    ·
      refine ⟨961864720679713492619875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5129945176958471960639333 961864720679713492619875)
      ·
        refine ⟨1442797081019570238929813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961864720679713492619875 1442797081019570238929813)
        ·
          refine ⟨67631113172792354949835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1442797081019570238929813 67631113172792354949835)
          ·
            refine ⟨101446669759188532424753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67631113172792354949835 101446669759188532424753)
            ·
              refine ⟨76085002319391399318565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101446669759188532424753 76085002319391399318565)
              ·
                refine ⟨14265937934885887372231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76085002319391399318565 14265937934885887372231)
                ·
                  rfl

theorem cell20_93767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4].length) (baseStart_93767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93767 prefixEnd_93767 := by exact prefixLift 93767
  have htrace : WordTrace (prefixWord ++ tailWord_93767) baseStart_93767 baseEnd_93767 := by
    simpa [prefixWord, tailWord_93767, baseEnd_93767] using wordTrace_append hprefix tailTrace_93767
  have hstable : (prefixWord ++ tailWord_93767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93767).length < 2 ^ (prefixWord ++ tailWord_93767).sum := by decide
  have hdescent : baseEnd_93767 < baseStart_93767 := by decide
  rcases family_descends (prefixWord ++ tailWord_93767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93778 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_93778 : Nat := 118140960795 + 93778 * 2 ^ 59
def prefixEnd_93778 : Nat := 4983230072969 + 3 ^ 40 * 93778 * 2
def baseEnd_93778 : Nat := 42802834504390512749981

theorem tailTrace_93778 : CollatzResearch.WordTrace tailWord_93778 prefixEnd_93778 42802834504390512749981 := by
  unfold tailWord_93778
  simp only [CollatzResearch.WordTrace]
  refine ⟨855091163566449213102497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2280243102843864568273325 855091163566449213102497)
  ·
    refine ⟨641318372674836909826873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 855091163566449213102497 641318372674836909826873)
    ·
      refine ⟨480988779506127682370155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 641318372674836909826873 480988779506127682370155)
      ·
        refine ⟨721483169259191523555233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480988779506127682370155 721483169259191523555233)
        ·
          refine ⟨541112376944393642666425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721483169259191523555233 541112376944393642666425)
          ·
            refine ⟨405834282708295231999819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541112376944393642666425 405834282708295231999819)
            ·
              refine ⟨608751424062442847999729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405834282708295231999819 608751424062442847999729)
              ·
                refine ⟨456563568046832135999797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608751424062442847999729 456563568046832135999797)
                ·
                  refine ⟨42802834504390512749981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456563568046832135999797 42802834504390512749981)
                  ·
                    rfl

theorem cell20_93778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_93778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93778 prefixEnd_93778 := by exact prefixLift 93778
  have htrace : WordTrace (prefixWord ++ tailWord_93778) baseStart_93778 baseEnd_93778 := by
    simpa [prefixWord, tailWord_93778, baseEnd_93778] using wordTrace_append hprefix tailTrace_93778
  have hstable : (prefixWord ++ tailWord_93778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93778).length < 2 ^ (prefixWord ++ tailWord_93778).sum := by decide
  have hdescent : baseEnd_93778 < baseStart_93778 := by decide
  rcases family_descends (prefixWord ++ tailWord_93778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93802 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_93802 : Nat := 118140960795 + 93802 * 2 ^ 59
def prefixEnd_93802 : Nat := 4983230072969 + 3 ^ 40 * 93802 * 2
def baseEnd_93802 : Nat := 42813788758353095949883

theorem tailTrace_93802 : CollatzResearch.WordTrace tailWord_93802 prefixEnd_93802 42813788758353095949883 := by
  unfold tailWord_93802
  simp only [CollatzResearch.WordTrace]
  refine ⟨855310001544712237820915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2280826670785899300855773 855310001544712237820915)
  ·
    refine ⟨1282965002317068356731373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 855310001544712237820915 1282965002317068356731373)
    ·
      refine ⟨481111875868900633774265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1282965002317068356731373 481111875868900633774265)
      ·
        refine ⟨360833906901675475330699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481111875868900633774265 360833906901675475330699)
        ·
          refine ⟨541250860352513212996049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360833906901675475330699 541250860352513212996049)
          ·
            refine ⟨405938145264384909747037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541250860352513212996049 405938145264384909747037)
            ·
              refine ⟨152226804474144341155139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405938145264384909747037 152226804474144341155139)
              ·
                refine ⟨228340206711216511732709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152226804474144341155139 228340206711216511732709)
                ·
                  refine ⟨42813788758353095949883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228340206711216511732709 42813788758353095949883)
                  ·
                    rfl

theorem cell20_93802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_93802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93802 prefixEnd_93802 := by exact prefixLift 93802
  have htrace : WordTrace (prefixWord ++ tailWord_93802) baseStart_93802 baseEnd_93802 := by
    simpa [prefixWord, tailWord_93802, baseEnd_93802] using wordTrace_append hprefix tailTrace_93802
  have hstable : (prefixWord ++ tailWord_93802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93802).length < 2 ^ (prefixWord ++ tailWord_93802).sum := by decide
  have hdescent : baseEnd_93802 < baseStart_93802 := by decide
  rcases family_descends (prefixWord ++ tailWord_93802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93857 : List Nat := [1, 2, 3, 3, 2, 2, 1, 4, 2]
def baseStart_93857 : Nat := 118140960795 + 93857 * 2 ^ 59
def prefixEnd_93857 : Nat := 4983230072969 + 3 ^ 40 * 93857 * 2
def baseEnd_93857 : Nat := 42838892257017349116325

theorem tailTrace_93857 : CollatzResearch.WordTrace tailWord_93857 prefixEnd_93857 42838892257017349116325 := by
  unfold tailWord_93857
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423246020979593344535825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2282164013986395563023883 3423246020979593344535825)
  ·
    refine ⟨2567434515734695008401869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3423246020979593344535825 2567434515734695008401869)
    ·
      refine ⟨962787943400510628150701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2567434515734695008401869 962787943400510628150701)
      ·
        refine ⟨361045478775191485556513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 962787943400510628150701 361045478775191485556513)
        ·
          refine ⟨270784109081393614167385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361045478775191485556513 270784109081393614167385)
          ·
            refine ⟨203088081811045210625539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270784109081393614167385 203088081811045210625539)
            ·
              refine ⟨304632122716567815938309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203088081811045210625539 304632122716567815938309)
              ·
                refine ⟨57118523009356465488433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304632122716567815938309 57118523009356465488433)
                ·
                  refine ⟨42838892257017349116325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57118523009356465488433 42838892257017349116325)
                  ·
                    rfl

theorem cell20_93857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_93857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93857 prefixEnd_93857 := by exact prefixLift 93857
  have htrace : WordTrace (prefixWord ++ tailWord_93857) baseStart_93857 baseEnd_93857 := by
    simpa [prefixWord, tailWord_93857, baseEnd_93857] using wordTrace_append hprefix tailTrace_93857
  have hstable : (prefixWord ++ tailWord_93857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93857).length < 2 ^ (prefixWord ++ tailWord_93857).sum := by decide
  have hdescent : baseEnd_93857 < baseStart_93857 := by decide
  rcases family_descends (prefixWord ++ tailWord_93857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93885 : List Nat := [1, 4, 1, 2, 1, 2, 5, 4]
def baseStart_93885 : Nat := 118140960795 + 93885 * 2 ^ 59
def prefixEnd_93885 : Nat := 4983230072969 + 3 ^ 40 * 93885 * 2
def baseEnd_93885 : Nat := 14283890739991232060959

theorem tailTrace_93885 : CollatzResearch.WordTrace tailWord_93885 prefixEnd_93885 14283890739991232060959 := by
  unfold tailWord_93885
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424267264878154126555109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2282844843252102751036739 3424267264878154126555109)
  ·
    refine ⟨642050112164653898729083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3424267264878154126555109 642050112164653898729083)
    ·
      refine ⟨963075168246980848093625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642050112164653898729083 963075168246980848093625)
      ·
        refine ⟨722306376185235636070219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 963075168246980848093625 722306376185235636070219)
        ·
          refine ⟨1083459564277853454105329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722306376185235636070219 1083459564277853454105329)
          ·
            refine ⟨812594673208390090578997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083459564277853454105329 812594673208390090578997)
            ·
              refine ⟨76180750613286570991781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 812594673208390090578997 76180750613286570991781)
              ·
                refine ⟨14283890739991232060959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76180750613286570991781 14283890739991232060959)
                ·
                  rfl

theorem cell20_93885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_93885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93885 prefixEnd_93885 := by exact prefixLift 93885
  have htrace : WordTrace (prefixWord ++ tailWord_93885) baseStart_93885 baseEnd_93885 := by
    simpa [prefixWord, tailWord_93885, baseEnd_93885] using wordTrace_append hprefix tailTrace_93885
  have hstable : (prefixWord ++ tailWord_93885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93885).length < 2 ^ (prefixWord ++ tailWord_93885).sum := by decide
  have hdescent : baseEnd_93885 < baseStart_93885 := by decide
  rcases family_descends (prefixWord ++ tailWord_93885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93892 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_93892 : Nat := 118140960795 + 93892 * 2 ^ 59
def prefixEnd_93892 : Nat := 4983230072969 + 3 ^ 40 * 93892 * 2
def baseEnd_93892 : Nat := 42854867210712782949515

theorem tailTrace_93892 : CollatzResearch.WordTrace tailWord_93892 prefixEnd_93892 42854867210712782949515 := by
  unfold tailWord_93892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712261287926397161029965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2283015050568529548039953 1712261287926397161029965)
  ·
    refine ⟨642097982972398935386237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1712261287926397161029965 642097982972398935386237)
    ·
      refine ⟨240786743614649600769839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 642097982972398935386237 240786743614649600769839)
      ·
        refine ⟨361180115421974401154759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240786743614649600769839 361180115421974401154759)
        ·
          refine ⟨541770173132961601732139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361180115421974401154759 541770173132961601732139)
          ·
            refine ⟨812655259699442402598209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541770173132961601732139 812655259699442402598209)
            ·
              refine ⟨609491444774581801948657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812655259699442402598209 609491444774581801948657)
              ·
                refine ⟨457118583580936351461493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609491444774581801948657 457118583580936351461493)
                ·
                  refine ⟨42854867210712782949515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457118583580936351461493 42854867210712782949515)
                  ·
                    rfl

theorem cell20_93892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_93892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93892 prefixEnd_93892 := by exact prefixLift 93892
  have htrace : WordTrace (prefixWord ++ tailWord_93892) baseStart_93892 baseEnd_93892 := by
    simpa [prefixWord, tailWord_93892, baseEnd_93892] using wordTrace_append hprefix tailTrace_93892
  have hstable : (prefixWord ++ tailWord_93892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93892).length < 2 ^ (prefixWord ++ tailWord_93892).sum := by decide
  have hdescent : baseEnd_93892 < baseStart_93892 := by decide
  rcases family_descends (prefixWord ++ tailWord_93892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93930 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_93930 : Nat := 118140960795 + 93930 * 2 ^ 59
def prefixEnd_93930 : Nat := 4983230072969 + 3 ^ 40 * 93930 * 2
def baseEnd_93930 : Nat := 42872211446153539682693

theorem tailTrace_93930 : CollatzResearch.WordTrace tailWord_93930 prefixEnd_93930 42872211446153539682693 := by
  unfold tailWord_93930
  simp only [CollatzResearch.WordTrace]
  refine ⟨856477137428781702985811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2283939033143417874628829 856477137428781702985811)
  ·
    refine ⟨1284715706143172554478717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 856477137428781702985811 1284715706143172554478717)
    ·
      refine ⟨481768389803689707929519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1284715706143172554478717 481768389803689707929519)
      ·
        refine ⟨722652584705534561894279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481768389803689707929519 722652584705534561894279)
        ·
          refine ⟨1083978877058301842841419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722652584705534561894279 1083978877058301842841419)
          ·
            refine ⟨1625968315587452764262129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083978877058301842841419 1625968315587452764262129)
            ·
              refine ⟨1219476236690589573196597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625968315587452764262129 1219476236690589573196597)
              ·
                refine ⟨114325897189742772487181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1219476236690589573196597 114325897189742772487181)
                ·
                  refine ⟨42872211446153539682693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114325897189742772487181 42872211446153539682693)
                  ·
                    rfl

theorem cell20_93930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_93930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93930 prefixEnd_93930 := by exact prefixLift 93930
  have htrace : WordTrace (prefixWord ++ tailWord_93930) baseStart_93930 baseEnd_93930 := by
    simpa [prefixWord, tailWord_93930, baseEnd_93930] using wordTrace_append hprefix tailTrace_93930
  have hstable : (prefixWord ++ tailWord_93930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93930).length < 2 ^ (prefixWord ++ tailWord_93930).sum := by decide
  have hdescent : baseEnd_93930 < baseStart_93930 := by decide
  rcases family_descends (prefixWord ++ tailWord_93930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93937 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_93937 : Nat := 118140960795 + 93937 * 2 ^ 59
def prefixEnd_93937 : Nat := 4983230072969 + 3 ^ 40 * 93937 * 2
def baseEnd_93937 : Nat := 42875406436892626449331

theorem tailTrace_93937 : CollatzResearch.WordTrace tailWord_93937 prefixEnd_93937 42875406436892626449331 := by
  unfold tailWord_93937
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426163860689767007448065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2284109240459844671632043 3426163860689767007448065)
  ·
    refine ⟨2569622895517325255586049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3426163860689767007448065 2569622895517325255586049)
    ·
      refine ⟨1927217171637993941689537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2569622895517325255586049 1927217171637993941689537)
      ·
        refine ⟨1445412878728495456267153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1927217171637993941689537 1445412878728495456267153)
        ·
          refine ⟨1084059659046371592200365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1445412878728495456267153 1084059659046371592200365)
          ·
            refine ⟨406522372142389347075137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084059659046371592200365 406522372142389347075137)
            ·
              refine ⟨304891779106792010306353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406522372142389347075137 304891779106792010306353)
              ·
                refine ⟨228668834330094007729765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304891779106792010306353 228668834330094007729765)
                ·
                  refine ⟨42875406436892626449331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228668834330094007729765 42875406436892626449331)
                  ·
                    rfl

theorem cell20_93937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_93937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93937 prefixEnd_93937 := by exact prefixLift 93937
  have htrace : WordTrace (prefixWord ++ tailWord_93937) baseStart_93937 baseEnd_93937 := by
    simpa [prefixWord, tailWord_93937, baseEnd_93937] using wordTrace_append hprefix tailTrace_93937
  have hstable : (prefixWord ++ tailWord_93937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93937).length < 2 ^ (prefixWord ++ tailWord_93937).sum := by decide
  have hdescent : baseEnd_93937 < baseStart_93937 := by decide
  rcases family_descends (prefixWord ++ tailWord_93937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93951 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_93951 : Nat := 118140960795 + 93951 * 2 ^ 59
def prefixEnd_93951 : Nat := 4983230072969 + 3 ^ 40 * 93951 * 2
def baseEnd_93951 : Nat := 42881796418370799982607

theorem tailTrace_93951 : CollatzResearch.WordTrace tailWord_93951 prefixEnd_93951 42881796418370799982607 := by
  unfold tailWord_93951
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426674482639047398457707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2284449655092698265638471 3426674482639047398457707)
  ·
    refine ⟨5140011723958571097686561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426674482639047398457707 5140011723958571097686561)
    ·
      refine ⟨3855008792968928323264921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5140011723958571097686561 3855008792968928323264921)
      ·
        refine ⟨2891256594726696242448691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3855008792968928323264921 2891256594726696242448691)
        ·
          refine ⟨4336884892090044363673037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891256594726696242448691 4336884892090044363673037)
          ·
            refine ⟨1626331834533766636377389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4336884892090044363673037 1626331834533766636377389)
            ·
              refine ⟨609874437950162488641521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1626331834533766636377389 609874437950162488641521)
              ·
                refine ⟨457405828462621866481141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609874437950162488641521 457405828462621866481141)
                ·
                  refine ⟨42881796418370799982607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457405828462621866481141 42881796418370799982607)
                  ·
                    rfl

theorem cell20_93951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_93951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93951 prefixEnd_93951 := by exact prefixLift 93951
  have htrace : WordTrace (prefixWord ++ tailWord_93951) baseStart_93951 baseEnd_93951 := by
    simpa [prefixWord, tailWord_93951, baseEnd_93951] using wordTrace_append hprefix tailTrace_93951
  have hstable : (prefixWord ++ tailWord_93951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93951).length < 2 ^ (prefixWord ++ tailWord_93951).sum := by decide
  have hdescent : baseEnd_93951 < baseStart_93951 := by decide
  rcases family_descends (prefixWord ++ tailWord_93951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93985 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 3]
def baseStart_93985 : Nat := 118140960795 + 93985 * 2 ^ 59
def prefixEnd_93985 : Nat := 4983230072969 + 3 ^ 40 * 93985 * 2
def baseEnd_93985 : Nat := 42897314944817792849135

theorem tailTrace_93985 : CollatzResearch.WordTrace tailWord_93985 prefixEnd_93985 42897314944817792849135 := by
  unfold tailWord_93985
  simp only [CollatzResearch.WordTrace]
  refine ⟨3427914564515871205195409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2285276376343914136796939 3427914564515871205195409)
  ·
    refine ⟨2570935923386903403896557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3427914564515871205195409 2570935923386903403896557)
    ·
      refine ⟨964100971270088776461209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2570935923386903403896557 964100971270088776461209)
      ·
        refine ⟨723075728452566582345907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 964100971270088776461209 723075728452566582345907)
        ·
          refine ⟨1084613592678849873518861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723075728452566582345907 1084613592678849873518861)
          ·
            refine ⟨406730097254568702569573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084613592678849873518861 406730097254568702569573)
            ·
              refine ⟨76261893235231631731795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406730097254568702569573 76261893235231631731795)
              ·
                refine ⟨114392839852847447597693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76261893235231631731795 114392839852847447597693)
                ·
                  refine ⟨42897314944817792849135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114392839852847447597693 42897314944817792849135)
                  ·
                    rfl

theorem cell20_93985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_93985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_93985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_93985 prefixEnd_93985 := by exact prefixLift 93985
  have htrace : WordTrace (prefixWord ++ tailWord_93985) baseStart_93985 baseEnd_93985 := by
    simpa [prefixWord, tailWord_93985, baseEnd_93985] using wordTrace_append hprefix tailTrace_93985
  have hstable : (prefixWord ++ tailWord_93985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93985).length < 2 ^ (prefixWord ++ tailWord_93985).sum := by decide
  have hdescent : baseEnd_93985 < baseStart_93985 := by decide
  rcases family_descends (prefixWord ++ tailWord_93985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94020 : List Nat := [2, 3, 4, 11]
def baseStart_94020 : Nat := 118140960795 + 94020 * 2 ^ 59
def prefixEnd_94020 : Nat := 4983230072969 + 3 ^ 40 * 94020 * 2
def baseEnd_94020 : Nat := 176597900816926858775

theorem tailTrace_94020 : CollatzResearch.WordTrace tailWord_94020 prefixEnd_94020 176597900816926858775 := by
  unfold tailWord_94020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714595559694536091359757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2286127412926048121813009 1714595559694536091359757)
  ·
    refine ⟨642973334885451034259909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1714595559694536091359757 642973334885451034259909)
    ·
      refine ⟨120557500291022068923733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 642973334885451034259909 120557500291022068923733)
      ·
        refine ⟨176597900816926858775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 120557500291022068923733 176597900816926858775)
        ·
          rfl

theorem cell20_94020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 11].length) (baseStart_94020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94020 prefixEnd_94020 := by exact prefixLift 94020
  have htrace : WordTrace (prefixWord ++ tailWord_94020) baseStart_94020 baseEnd_94020 := by
    simpa [prefixWord, tailWord_94020, baseEnd_94020] using wordTrace_append hprefix tailTrace_94020
  have hstable : (prefixWord ++ tailWord_94020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94020).length < 2 ^ (prefixWord ++ tailWord_94020).sum := by decide
  have hdescent : baseEnd_94020 < baseStart_94020 := by decide
  rcases family_descends (prefixWord ++ tailWord_94020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94022 : List Nat := [6, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_94022 : Nat := 118140960795 + 94022 * 2 ^ 59
def prefixEnd_94022 : Nat := 4983230072969 + 3 ^ 40 * 94022 * 2
def baseEnd_94022 : Nat := 42914202753010108615651

theorem tailTrace_94022 : CollatzResearch.WordTrace tailWord_94022 prefixEnd_94022 42914202753010108615651 := by
  unfold tailWord_94022
  simp only [CollatzResearch.WordTrace]
  refine ⟨107164502043182078884135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2286176043587884349528213 107164502043182078884135)
  ·
    refine ⟨160746753064773118326203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107164502043182078884135 160746753064773118326203)
    ·
      refine ⟨241120129597159677489305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160746753064773118326203 241120129597159677489305)
      ·
        refine ⟨180840097197869758116979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241120129597159677489305 180840097197869758116979)
        ·
          refine ⟨271260145796804637175469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180840097197869758116979 271260145796804637175469)
          ·
            refine ⟨101722554673801738940801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271260145796804637175469 101722554673801738940801)
            ·
              refine ⟨76291916005351304205601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101722554673801738940801 76291916005351304205601)
              ·
                refine ⟨57218937004013478154201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76291916005351304205601 57218937004013478154201)
                ·
                  refine ⟨42914202753010108615651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57218937004013478154201 42914202753010108615651)
                  ·
                    rfl

theorem cell20_94022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_94022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94022 prefixEnd_94022 := by exact prefixLift 94022
  have htrace : WordTrace (prefixWord ++ tailWord_94022) baseStart_94022 baseEnd_94022 := by
    simpa [prefixWord, tailWord_94022, baseEnd_94022] using wordTrace_append hprefix tailTrace_94022
  have hstable : (prefixWord ++ tailWord_94022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94022).length < 2 ^ (prefixWord ++ tailWord_94022).sum := by decide
  have hdescent : baseEnd_94022 < baseStart_94022 := by decide
  rcases family_descends (prefixWord ++ tailWord_94022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94037 : List Nat := [1, 3, 2, 2, 2, 4, 1, 5]
def baseStart_94037 : Nat := 118140960795 + 94037 * 2 ^ 59
def prefixEnd_94037 : Nat := 4983230072969 + 3 ^ 40 * 94037 * 2
def baseEnd_94037 : Nat := 14307016387245574371863

theorem tailTrace_94037 : CollatzResearch.WordTrace tailWord_94037 prefixEnd_94037 14307016387245574371863 := by
  unfold tailWord_94037
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429811160327484086088365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2286540773551656057392243 3429811160327484086088365)
  ·
    refine ⟨1286179185122806532283137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3429811160327484086088365 1286179185122806532283137)
    ·
      refine ⟨964634388842104899212353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1286179185122806532283137 964634388842104899212353)
      ·
        refine ⟨723475791631578674409265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 964634388842104899212353 723475791631578674409265)
        ·
          refine ⟨542606843723684005806949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723475791631578674409265 542606843723684005806949)
          ·
            refine ⟨101738783198190751088803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 542606843723684005806949 101738783198190751088803)
            ·
              refine ⟨152608174797286126633205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101738783198190751088803 152608174797286126633205)
              ·
                refine ⟨14307016387245574371863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152608174797286126633205 14307016387245574371863)
                ·
                  rfl

theorem cell20_94037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_94037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94037 prefixEnd_94037 := by exact prefixLift 94037
  have htrace : WordTrace (prefixWord ++ tailWord_94037) baseStart_94037 baseEnd_94037 := by
    simpa [prefixWord, tailWord_94037, baseEnd_94037] using wordTrace_append hprefix tailTrace_94037
  have hstable : (prefixWord ++ tailWord_94037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94037).length < 2 ^ (prefixWord ++ tailWord_94037).sum := by decide
  have hdescent : baseEnd_94037 < baseStart_94037 := by decide
  rcases family_descends (prefixWord ++ tailWord_94037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94065 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_94065 : Nat := 118140960795 + 94065 * 2 ^ 59
def prefixEnd_94065 : Nat := 4983230072969 + 3 ^ 40 * 94065 * 2
def baseEnd_94065 : Nat := 42933829124693070182141

theorem tailTrace_94065 : CollatzResearch.WordTrace tailWord_94065 prefixEnd_94065 42933829124693070182141 := by
  unfold tailWord_94065
  simp only [CollatzResearch.WordTrace]
  refine ⟨3430832404226044868107649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2287221602817363245405099 3430832404226044868107649)
  ·
    refine ⟨2573124303169533651080737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3430832404226044868107649 2573124303169533651080737)
    ·
      refine ⟨1929843227377150238310553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2573124303169533651080737 1929843227377150238310553)
      ·
        refine ⟨1447382420532862678732915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1929843227377150238310553 1447382420532862678732915)
        ·
          refine ⟨2171073630799294018099373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1447382420532862678732915 2171073630799294018099373)
          ·
            refine ⟨814152611549735256787265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2171073630799294018099373 814152611549735256787265)
            ·
              refine ⟨610614458662301442590449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814152611549735256787265 610614458662301442590449)
              ·
                refine ⟨457960843996726081942837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610614458662301442590449 457960843996726081942837)
                ·
                  refine ⟨42933829124693070182141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457960843996726081942837 42933829124693070182141)
                  ·
                    rfl

theorem cell20_94065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_94065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94065 prefixEnd_94065 := by exact prefixLift 94065
  have htrace : WordTrace (prefixWord ++ tailWord_94065) baseStart_94065 baseEnd_94065 := by
    simpa [prefixWord, tailWord_94065, baseEnd_94065] using wordTrace_append hprefix tailTrace_94065
  have hstable : (prefixWord ++ tailWord_94065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94065).length < 2 ^ (prefixWord ++ tailWord_94065).sum := by decide
  have hdescent : baseEnd_94065 < baseStart_94065 := by decide
  rcases family_descends (prefixWord ++ tailWord_94065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94078 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_94078 : Nat := 118140960795 + 94078 * 2 ^ 59
def prefixEnd_94078 : Nat := 4983230072969 + 3 ^ 40 * 94078 * 2
def baseEnd_94078 : Nat := 42939762678922802748755

theorem tailTrace_94078 : CollatzResearch.WordTrace tailWord_94078 prefixEnd_94078 42939762678922802748755 := by
  unfold tailWord_94078
  simp only [CollatzResearch.WordTrace]
  refine ⟨428913319147368511041361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2287537702119298725553925 428913319147368511041361)
  ·
    refine ⟨321684989360526383281021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 428913319147368511041361 321684989360526383281021)
    ·
      refine ⟨120631871010197393730383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321684989360526383281021 120631871010197393730383)
      ·
        refine ⟨180947806515296090595575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120631871010197393730383 180947806515296090595575)
        ·
          refine ⟨271421709772944135893363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180947806515296090595575 271421709772944135893363)
          ·
            refine ⟨407132564659416203840045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271421709772944135893363 407132564659416203840045)
            ·
              refine ⟨152674711747281076440017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407132564659416203840045 152674711747281076440017)
              ·
                refine ⟨114506033810460807330013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152674711747281076440017 114506033810460807330013)
                ·
                  refine ⟨42939762678922802748755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114506033810460807330013 42939762678922802748755)
                  ·
                    rfl

theorem cell20_94078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_94078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94078 prefixEnd_94078 := by exact prefixLift 94078
  have htrace : WordTrace (prefixWord ++ tailWord_94078) baseStart_94078 baseEnd_94078 := by
    simpa [prefixWord, tailWord_94078, baseEnd_94078] using wordTrace_append hprefix tailTrace_94078
  have hstable : (prefixWord ++ tailWord_94078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94078).length < 2 ^ (prefixWord ++ tailWord_94078).sum := by decide
  have hdescent : baseEnd_94078 < baseStart_94078 := by decide
  rcases family_descends (prefixWord ++ tailWord_94078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94089 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_94089 : Nat := 118140960795 + 94089 * 2 ^ 59
def prefixEnd_94089 : Nat := 4983230072969 + 3 ^ 40 * 94089 * 2
def baseEnd_94089 : Nat := 42944783378655653382043

theorem tailTrace_94089 : CollatzResearch.WordTrace tailWord_94089 prefixEnd_94089 42944783378655653382043 := by
  unfold tailWord_94089
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431707756139096966981321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2287805170759397977987547 3431707756139096966981321)
  ·
    refine ⟨2573780817104322725235991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3431707756139096966981321 2573780817104322725235991)
    ·
      refine ⟨3860671225656484087853987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573780817104322725235991 3860671225656484087853987)
      ·
        refine ⟨5791006838484726131780981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3860671225656484087853987 5791006838484726131780981)
        ·
          refine ⟨542906891107943074854467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5791006838484726131780981 542906891107943074854467)
          ·
            refine ⟨814360336661914612281701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542906891107943074854467 814360336661914612281701)
            ·
              refine ⟨152692563124108989802819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 814360336661914612281701 152692563124108989802819)
              ·
                refine ⟨229038844686163484704229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152692563124108989802819 229038844686163484704229)
                ·
                  refine ⟨42944783378655653382043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229038844686163484704229 42944783378655653382043)
                  ·
                    rfl

theorem cell20_94089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_94089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94089 prefixEnd_94089 := by exact prefixLift 94089
  have htrace : WordTrace (prefixWord ++ tailWord_94089) baseStart_94089 baseEnd_94089 := by
    simpa [prefixWord, tailWord_94089, baseEnd_94089] using wordTrace_append hprefix tailTrace_94089
  have hstable : (prefixWord ++ tailWord_94089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94089).length < 2 ^ (prefixWord ++ tailWord_94089).sum := by decide
  have hdescent : baseEnd_94089 < baseStart_94089 := by decide
  rcases family_descends (prefixWord ++ tailWord_94089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94113 : List Nat := [1, 2, 3, 4, 2, 1, 1, 6]
def baseStart_94113 : Nat := 118140960795 + 94113 * 2 ^ 59
def prefixEnd_94113 : Nat := 4983230072969 + 3 ^ 40 * 94113 * 2
def baseEnd_94113 : Nat := 14318579210872745527315

theorem tailTrace_94113 : CollatzResearch.WordTrace tailWord_94113 prefixEnd_94113 14318579210872745527315 := by
  unfold tailWord_94113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3432583108052149065854993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2288388738701432710569995 3432583108052149065854993)
  ·
    refine ⟨2574437331039111799391245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3432583108052149065854993 2574437331039111799391245)
    ·
      refine ⟨965413999139666924771717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2574437331039111799391245 965413999139666924771717)
      ·
        refine ⟨181015124838687548394697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 965413999139666924771717 181015124838687548394697)
        ·
          refine ⟨135761343629015661296023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181015124838687548394697 135761343629015661296023)
          ·
            refine ⟨203642015443523491944035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135761343629015661296023 203642015443523491944035)
            ·
              refine ⟨305463023165285237916053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203642015443523491944035 305463023165285237916053)
              ·
                refine ⟨14318579210872745527315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 305463023165285237916053 14318579210872745527315)
                ·
                  rfl

theorem cell20_94113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_94113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94113 prefixEnd_94113 := by exact prefixLift 94113
  have htrace : WordTrace (prefixWord ++ tailWord_94113) baseStart_94113 baseEnd_94113 := by
    simpa [prefixWord, tailWord_94113, baseEnd_94113] using wordTrace_append hprefix tailTrace_94113
  have hstable : (prefixWord ++ tailWord_94113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94113).length < 2 ^ (prefixWord ++ tailWord_94113).sum := by decide
  have hdescent : baseEnd_94113 < baseStart_94113 := by decide
  rcases family_descends (prefixWord ++ tailWord_94113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94126 : List Nat := [4, 1, 5, 1, 2, 1, 6]
def baseStart_94126 : Nat := 118140960795 + 94126 * 2 ^ 59
def prefixEnd_94126 : Nat := 4983230072969 + 3 ^ 40 * 94126 * 2
def baseEnd_94126 : Nat := 4773519020760885460951

theorem tailTrace_94126 : CollatzResearch.WordTrace tailWord_94126 prefixEnd_94126 4773519020760885460951 := by
  unfold tailWord_94126
  simp only [CollatzResearch.WordTrace]
  refine ⟨429132157125631535759779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2288704838003368190718821 429132157125631535759779)
  ·
    refine ⟨643698235688447303639669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429132157125631535759779 643698235688447303639669)
    ·
      refine ⟨60346709595791934716219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 643698235688447303639669 60346709595791934716219)
      ·
        refine ⟨90520064393687902074329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60346709595791934716219 90520064393687902074329)
        ·
          refine ⟨67890048295265926555747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90520064393687902074329 67890048295265926555747)
          ·
            refine ⟨101835072442898889833621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67890048295265926555747 101835072442898889833621)
            ·
              refine ⟨4773519020760885460951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101835072442898889833621 4773519020760885460951)
              ·
                rfl

theorem cell20_94126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 6].length) (baseStart_94126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94126 prefixEnd_94126 := by exact prefixLift 94126
  have htrace : WordTrace (prefixWord ++ tailWord_94126) baseStart_94126 baseEnd_94126 := by
    simpa [prefixWord, tailWord_94126, baseEnd_94126] using wordTrace_append hprefix tailTrace_94126
  have hstable : (prefixWord ++ tailWord_94126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94126).length < 2 ^ (prefixWord ++ tailWord_94126).sum := by decide
  have hdescent : baseEnd_94126 < baseStart_94126 := by decide
  rcases family_descends (prefixWord ++ tailWord_94126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94140 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 4]
def baseStart_94140 : Nat := 118140960795 + 94140 * 2 ^ 59
def prefixEnd_94140 : Nat := 4983230072969 + 3 ^ 40 * 94140 * 2
def baseEnd_94140 : Nat := 42968061168326142681835

theorem tailTrace_94140 : CollatzResearch.WordTrace tailWord_94140 prefixEnd_94140 42968061168326142681835 := by
  unfold tailWord_94140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716783939477166338543937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2289045252636221784725249 1716783939477166338543937)
  ·
    refine ⟨1287587954607874753907953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1716783939477166338543937 1287587954607874753907953)
    ·
      refine ⟨965690965955906065430965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1287587954607874753907953 965690965955906065430965)
      ·
        refine ⟨90533528058366193634153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 965690965955906065430965 90533528058366193634153)
        ·
          refine ⟨67900146043774645225615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90533528058366193634153 67900146043774645225615)
          ·
            refine ⟨101850219065661967838423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67900146043774645225615 101850219065661967838423)
            ·
              refine ⟨152775328598492951757635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101850219065661967838423 152775328598492951757635)
              ·
                refine ⟨229162992897739427636453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152775328598492951757635 229162992897739427636453)
                ·
                  refine ⟨42968061168326142681835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229162992897739427636453 42968061168326142681835)
                  ·
                    rfl

theorem cell20_94140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_94140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94140 prefixEnd_94140 := by exact prefixLift 94140
  have htrace : WordTrace (prefixWord ++ tailWord_94140) baseStart_94140 baseEnd_94140 := by
    simpa [prefixWord, tailWord_94140, baseEnd_94140] using wordTrace_append hprefix tailTrace_94140
  have hstable : (prefixWord ++ tailWord_94140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94140).length < 2 ^ (prefixWord ++ tailWord_94140).sum := by decide
  have hdescent : baseEnd_94140 < baseStart_94140 := by decide
  rcases family_descends (prefixWord ++ tailWord_94140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94158 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_94158 : Nat := 118140960795 + 94158 * 2 ^ 59
def prefixEnd_94158 : Nat := 4983230072969 + 3 ^ 40 * 94158 * 2
def baseEnd_94158 : Nat := 42976276858798080081761

theorem tailTrace_94158 : CollatzResearch.WordTrace tailWord_94158 prefixEnd_94158 42976276858798080081761 := by
  unfold tailWord_94158
  simp only [CollatzResearch.WordTrace]
  refine ⟨429278049111140218905391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2289482928592747834162085 429278049111140218905391)
  ·
    refine ⟨643917073666710328358087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429278049111140218905391 643917073666710328358087)
    ·
      refine ⟨965875610500065492537131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643917073666710328358087 965875610500065492537131)
      ·
        refine ⟨1448813415750098238805697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965875610500065492537131 1448813415750098238805697)
        ·
          refine ⟨1086610061812573679104273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1448813415750098238805697 1086610061812573679104273)
          ·
            refine ⟨814957546359430259328205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086610061812573679104273 814957546359430259328205)
            ·
              refine ⟨305609079884786347248077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 814957546359430259328205 305609079884786347248077)
              ·
                refine ⟨114603404956794880218029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305609079884786347248077 114603404956794880218029)
                ·
                  refine ⟨42976276858798080081761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114603404956794880218029 42976276858798080081761)
                  ·
                    rfl

theorem cell20_94158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_94158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94158 prefixEnd_94158 := by exact prefixLift 94158
  have htrace : WordTrace (prefixWord ++ tailWord_94158) baseStart_94158 baseEnd_94158 := by
    simpa [prefixWord, tailWord_94158, baseEnd_94158] using wordTrace_append hprefix tailTrace_94158
  have hstable : (prefixWord ++ tailWord_94158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94158).length < 2 ^ (prefixWord ++ tailWord_94158).sum := by decide
  have hdescent : baseEnd_94158 < baseStart_94158 := by decide
  rcases family_descends (prefixWord ++ tailWord_94158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94189 : List Nat := [1, 5, 1, 4, 1, 8]
def baseStart_94189 : Nat := 118140960795 + 94189 * 2 ^ 59
def prefixEnd_94189 : Nat := 4983230072969 + 3 ^ 40 * 94189 * 2
def baseEnd_94189 : Nat := 1592238003833324075863

theorem tailTrace_94189 : CollatzResearch.WordTrace tailWord_94189 prefixEnd_94189 1592238003833324075863 := by
  unfold tailWord_94189
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435355055776814045621621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2290236703851209363747747 3435355055776814045621621)
  ·
    refine ⟨322064536479076316777027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3435355055776814045621621 322064536479076316777027)
    ·
      refine ⟨483096804718614475165541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322064536479076316777027 483096804718614475165541)
      ·
        refine ⟨90580650884740214093539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 483096804718614475165541 90580650884740214093539)
        ·
          refine ⟨135870976327110321140309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90580650884740214093539 135870976327110321140309)
          ·
            refine ⟨1592238003833324075863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 135870976327110321140309 1592238003833324075863)
            ·
              rfl

theorem cell20_94189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 8].length) (baseStart_94189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94189 prefixEnd_94189 := by exact prefixLift 94189
  have htrace : WordTrace (prefixWord ++ tailWord_94189) baseStart_94189 baseEnd_94189 := by
    simpa [prefixWord, tailWord_94189, baseEnd_94189] using wordTrace_append hprefix tailTrace_94189
  have hstable : (prefixWord ++ tailWord_94189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94189).length < 2 ^ (prefixWord ++ tailWord_94189).sum := by decide
  have hdescent : baseEnd_94189 < baseStart_94189 := by decide
  rcases family_descends (prefixWord ++ tailWord_94189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94193 : List Nat := [1, 2, 2, 2, 13]
def baseStart_94193 : Nat := 118140960795 + 94193 * 2 ^ 59
def prefixEnd_94193 : Nat := 4983230072969 + 3 ^ 40 * 94193 * 2
def baseEnd_94193 : Nat := 530768540894981653271

theorem tailTrace_94193 : CollatzResearch.WordTrace tailWord_94193 prefixEnd_94193 530768540894981653271 := by
  unfold tailWord_94193
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435500947762322728767233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2290333965174881819178155 3435500947762322728767233)
  ·
    refine ⟨2576625710821742046575425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3435500947762322728767233 2576625710821742046575425)
    ·
      refine ⟨1932469283116306534931569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576625710821742046575425 1932469283116306534931569)
      ·
        refine ⟨1449351962337229901198677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1932469283116306534931569 1449351962337229901198677)
        ·
          refine ⟨530768540894981653271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1449351962337229901198677 530768540894981653271)
          ·
            rfl

theorem cell20_94193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 13].length) (baseStart_94193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94193 prefixEnd_94193 := by exact prefixLift 94193
  have htrace : WordTrace (prefixWord ++ tailWord_94193) baseStart_94193 baseEnd_94193 := by
    simpa [prefixWord, tailWord_94193, baseEnd_94193] using wordTrace_append hprefix tailTrace_94193
  have hstable : (prefixWord ++ tailWord_94193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94193).length < 2 ^ (prefixWord ++ tailWord_94193).sum := by decide
  have hdescent : baseEnd_94193 < baseStart_94193 := by decide
  rcases family_descends (prefixWord ++ tailWord_94193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94206 : List Nat := [4, 2, 2, 2, 1, 3, 1, 5]
def baseStart_94206 : Nat := 118140960795 + 94206 * 2 ^ 59
def prefixEnd_94206 : Nat := 4983230072969 + 3 ^ 40 * 94206 * 2
def baseEnd_94206 : Nat := 14332728455574415493855

theorem tailTrace_94206 : CollatzResearch.WordTrace tailWord_94206 prefixEnd_94206 14332728455574415493855 := by
  unfold tailWord_94206
  simp only [CollatzResearch.WordTrace]
  refine ⟨429496887089403243623809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2290650064476817299326981 429496887089403243623809)
  ·
    refine ⟨322122665317052432717857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 429496887089403243623809 322122665317052432717857)
    ·
      refine ⟨241591998987789324538393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322122665317052432717857 241591998987789324538393)
      ·
        refine ⟨181193999240841993403795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241591998987789324538393 181193999240841993403795)
        ·
          refine ⟨271790998861262990105693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181193999240841993403795 271790998861262990105693)
          ·
            refine ⟨101921624572973621289635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271790998861262990105693 101921624572973621289635)
            ·
              refine ⟨152882436859460431934453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101921624572973621289635 152882436859460431934453)
              ·
                refine ⟨14332728455574415493855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152882436859460431934453 14332728455574415493855)
                ·
                  rfl

theorem cell20_94206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_94206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94206 prefixEnd_94206 := by exact prefixLift 94206
  have htrace : WordTrace (prefixWord ++ tailWord_94206) baseStart_94206 baseEnd_94206 := by
    simpa [prefixWord, tailWord_94206, baseEnd_94206] using wordTrace_append hprefix tailTrace_94206
  have hstable : (prefixWord ++ tailWord_94206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94206).length < 2 ^ (prefixWord ++ tailWord_94206).sum := by decide
  have hdescent : baseEnd_94206 < baseStart_94206 := by decide
  rcases family_descends (prefixWord ++ tailWord_94206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94224 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_94224 : Nat := 118140960795 + 94224 * 2 ^ 59
def prefixEnd_94224 : Nat := 4983230072969 + 3 ^ 40 * 94224 * 2
def baseEnd_94224 : Nat := 43006401057195183881491

theorem tailTrace_94224 : CollatzResearch.WordTrace tailWord_94224 prefixEnd_94224 43006401057195183881491 := by
  unfold tailWord_94224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1718315805325007511572863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2291087740433343348763817 1718315805325007511572863)
  ·
    refine ⟨2577473707987511267359295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1718315805325007511572863 2577473707987511267359295)
    ·
      refine ⟨3866210561981266901038943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577473707987511267359295 3866210561981266901038943)
      ·
        refine ⟨5799315842971900351558415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866210561981266901038943 5799315842971900351558415)
        ·
          refine ⟨8698973764457850527337623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799315842971900351558415 8698973764457850527337623)
          ·
            refine ⟨13048460646686775791006435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698973764457850527337623 13048460646686775791006435)
            ·
              refine ⟨19572690970030163686509653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13048460646686775791006435 19572690970030163686509653)
              ·
                refine ⟨229367472305040980701285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19572690970030163686509653 229367472305040980701285)
                ·
                  refine ⟨43006401057195183881491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229367472305040980701285 43006401057195183881491)
                  ·
                    rfl

theorem cell20_94224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_94224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94224 prefixEnd_94224 := by exact prefixLift 94224
  have htrace : WordTrace (prefixWord ++ tailWord_94224) baseStart_94224 baseEnd_94224 := by
    simpa [prefixWord, tailWord_94224, baseEnd_94224] using wordTrace_append hprefix tailTrace_94224
  have hstable : (prefixWord ++ tailWord_94224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94224).length < 2 ^ (prefixWord ++ tailWord_94224).sum := by decide
  have hdescent : baseEnd_94224 < baseStart_94224 := by decide
  rcases family_descends (prefixWord ++ tailWord_94224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94237 : List Nat := [1, 4, 2, 2, 2, 2, 2, 3, 2]
def baseStart_94237 : Nat := 118140960795 + 94237 * 2 ^ 59
def prefixEnd_94237 : Nat := 4983230072969 + 3 ^ 40 * 94237 * 2
def baseEnd_94237 : Nat := 43012334611424916448105

theorem tailTrace_94237 : CollatzResearch.WordTrace tailWord_94237 prefixEnd_94237 43012334611424916448105 := by
  unfold tailWord_94237
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437105759602918243368965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2291403839735278828912643 3437105759602918243368965)
  ·
    refine ⟨644457329925547170631681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3437105759602918243368965 644457329925547170631681)
    ·
      refine ⟨483342997444160377973761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 644457329925547170631681 483342997444160377973761)
      ·
        refine ⟨362507248083120283480321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483342997444160377973761 362507248083120283480321)
        ·
          refine ⟨271880436062340212610241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362507248083120283480321 271880436062340212610241)
          ·
            refine ⟨203910327046755159457681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271880436062340212610241 203910327046755159457681)
            ·
              refine ⟨152932745285066369593261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203910327046755159457681 152932745285066369593261)
              ·
                refine ⟨57349779481899888597473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152932745285066369593261 57349779481899888597473)
                ·
                  refine ⟨43012334611424916448105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57349779481899888597473 43012334611424916448105)
                  ·
                    rfl

theorem cell20_94237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_94237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94237 prefixEnd_94237 := by exact prefixLift 94237
  have htrace : WordTrace (prefixWord ++ tailWord_94237) baseStart_94237 baseEnd_94237 := by
    simpa [prefixWord, tailWord_94237, baseEnd_94237] using wordTrace_append hprefix tailTrace_94237
  have hstable : (prefixWord ++ tailWord_94237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94237).length < 2 ^ (prefixWord ++ tailWord_94237).sum := by decide
  have hdescent : baseEnd_94237 < baseStart_94237 := by decide
  rcases family_descends (prefixWord ++ tailWord_94237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94247 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 3]
def baseStart_94247 : Nat := 118140960795 + 94247 * 2 ^ 59
def prefixEnd_94247 : Nat := 4983230072969 + 3 ^ 40 * 94247 * 2
def baseEnd_94247 : Nat := 43016898883909326114731

theorem tailTrace_94247 : CollatzResearch.WordTrace tailWord_94247 prefixEnd_94247 43016898883909326114731 := by
  unfold tailWord_94247
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437470489566689951232995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2291646993044459967488663 3437470489566689951232995)
  ·
    refine ⟨5156205734350034926849493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3437470489566689951232995 5156205734350034926849493)
    ·
      refine ⟨120848571898828943598035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5156205734350034926849493 120848571898828943598035)
      ·
        refine ⟨181272857848243415397053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120848571898828943598035 181272857848243415397053)
        ·
          refine ⟨67977321693091280773895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181272857848243415397053 67977321693091280773895)
          ·
            refine ⟨101965982539636921160843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67977321693091280773895 101965982539636921160843)
            ·
              refine ⟨152948973809455381741265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101965982539636921160843 152948973809455381741265)
              ·
                refine ⟨114711730357091536305949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152948973809455381741265 114711730357091536305949)
                ·
                  refine ⟨43016898883909326114731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114711730357091536305949 43016898883909326114731)
                  ·
                    rfl

theorem cell20_94247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 3].length) (baseStart_94247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94247 prefixEnd_94247 := by exact prefixLift 94247
  have htrace : WordTrace (prefixWord ++ tailWord_94247) baseStart_94247 baseEnd_94247 := by
    simpa [prefixWord, tailWord_94247, baseEnd_94247] using wordTrace_append hprefix tailTrace_94247
  have hstable : (prefixWord ++ tailWord_94247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94247).length < 2 ^ (prefixWord ++ tailWord_94247).sum := by decide
  have hdescent : baseEnd_94247 < baseStart_94247 := by decide
  rcases family_descends (prefixWord ++ tailWord_94247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94255 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 3]
def baseStart_94255 : Nat := 118140960795 + 94255 * 2 ^ 59
def prefixEnd_94255 : Nat := 4983230072969 + 3 ^ 40 * 94255 * 2
def baseEnd_94255 : Nat := 43020550301896853848031

theorem tailTrace_94255 : CollatzResearch.WordTrace tailWord_94255 prefixEnd_94255 43020550301896853848031 := by
  unfold tailWord_94255
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437762273537707317524219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2291841515691804878349479 3437762273537707317524219)
  ·
    refine ⟨5156643410306560976286329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3437762273537707317524219 5156643410306560976286329)
    ·
      refine ⟨3867482557729920732214747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5156643410306560976286329 3867482557729920732214747)
      ·
        refine ⟨5801223836594881098322121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3867482557729920732214747 5801223836594881098322121)
        ·
          refine ⟨4350917877446160823741591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5801223836594881098322121 4350917877446160823741591)
          ·
            refine ⟨6526376816169241235612387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350917877446160823741591 6526376816169241235612387)
            ·
              refine ⟨9789565224253861853418581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6526376816169241235612387 9789565224253861853418581)
              ·
                refine ⟨114721467471724943594749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9789565224253861853418581 114721467471724943594749)
                ·
                  refine ⟨43020550301896853848031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114721467471724943594749 43020550301896853848031)
                  ·
                    rfl

theorem cell20_94255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_94255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94255 prefixEnd_94255 := by exact prefixLift 94255
  have htrace : WordTrace (prefixWord ++ tailWord_94255) baseStart_94255 baseEnd_94255 := by
    simpa [prefixWord, tailWord_94255, baseEnd_94255] using wordTrace_append hprefix tailTrace_94255
  have hstable : (prefixWord ++ tailWord_94255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94255).length < 2 ^ (prefixWord ++ tailWord_94255).sum := by decide
  have hdescent : baseEnd_94255 < baseStart_94255 := by decide
  rcases family_descends (prefixWord ++ tailWord_94255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94258 : List Nat := [3, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_94258 : Nat := 118140960795 + 94258 * 2 ^ 59
def prefixEnd_94258 : Nat := 4983230072969 + 3 ^ 40 * 94258 * 2
def baseEnd_94258 : Nat := 43021919583642176748019

theorem tailTrace_94258 : CollatzResearch.WordTrace tailWord_94258 prefixEnd_94258 43021919583642176748019 := by
  unfold tailWord_94258
  simp only [CollatzResearch.WordTrace]
  refine ⟨859467923131709707470857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2291914461684559219922285 859467923131709707470857)
  ·
    refine ⟨644600942348782280603143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 859467923131709707470857 644600942348782280603143)
    ·
      refine ⟨966901413523173420904715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644600942348782280603143 966901413523173420904715)
      ·
        refine ⟨1450352120284760131357073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966901413523173420904715 1450352120284760131357073)
        ·
          refine ⟨1087764090213570098517805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1450352120284760131357073 1087764090213570098517805)
          ·
            refine ⟨407911533830088786944177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1087764090213570098517805 407911533830088786944177)
            ·
              refine ⟨305933650372566590208133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407911533830088786944177 305933650372566590208133)
              ·
                refine ⟨57362559444856235664025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305933650372566590208133 57362559444856235664025)
                ·
                  refine ⟨43021919583642176748019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57362559444856235664025 43021919583642176748019)
                  ·
                    rfl

theorem cell20_94258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_94258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94258 prefixEnd_94258 := by exact prefixLift 94258
  have htrace : WordTrace (prefixWord ++ tailWord_94258) baseStart_94258 baseEnd_94258 := by
    simpa [prefixWord, tailWord_94258, baseEnd_94258] using wordTrace_append hprefix tailTrace_94258
  have hstable : (prefixWord ++ tailWord_94258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94258).length < 2 ^ (prefixWord ++ tailWord_94258).sum := by decide
  have hdescent : baseEnd_94258 < baseStart_94258 := by decide
  rcases family_descends (prefixWord ++ tailWord_94258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94286 : List Nat := [4, 1, 1, 1, 1, 5, 1, 6]
def baseStart_94286 : Nat := 118140960795 + 94286 * 2 ^ 59
def prefixEnd_94286 : Nat := 4983230072969 + 3 ^ 40 * 94286 * 2
def baseEnd_94286 : Nat := 14344899848866174604857

theorem tailTrace_94286 : CollatzResearch.WordTrace tailWord_94286 prefixEnd_94286 14344899848866174604857 := by
  unfold tailWord_94286
  simp only [CollatzResearch.WordTrace]
  refine ⟨429861617053174951487839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2292595290950266407935141 429861617053174951487839)
  ·
    refine ⟨644792425579762427231759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429861617053174951487839 644792425579762427231759)
    ·
      refine ⟨967188638369643640847639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644792425579762427231759 967188638369643640847639)
      ·
        refine ⟨1450782957554465461271459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967188638369643640847639 1450782957554465461271459)
        ·
          refine ⟨2176174436331698191907189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450782957554465461271459 2176174436331698191907189)
          ·
            refine ⟨204016353406096705491299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2176174436331698191907189 204016353406096705491299)
            ·
              refine ⟨306024530109145058236949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204016353406096705491299 306024530109145058236949)
              ·
                refine ⟨14344899848866174604857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 306024530109145058236949 14344899848866174604857)
                ·
                  rfl

theorem cell20_94286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_94286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94286 prefixEnd_94286 := by exact prefixLift 94286
  have htrace : WordTrace (prefixWord ++ tailWord_94286) baseStart_94286 baseEnd_94286 := by
    simpa [prefixWord, tailWord_94286, baseEnd_94286] using wordTrace_append hprefix tailTrace_94286
  have hstable : (prefixWord ++ tailWord_94286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94286).length < 2 ^ (prefixWord ++ tailWord_94286).sum := by decide
  have hdescent : baseEnd_94286 < baseStart_94286 := by decide
  rcases family_descends (prefixWord ++ tailWord_94286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94293 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_94293 : Nat := 118140960795 + 94293 * 2 ^ 59
def prefixEnd_94293 : Nat := 4983230072969 + 3 ^ 40 * 94293 * 2
def baseEnd_94293 : Nat := 43037894537337610581209

theorem tailTrace_94293 : CollatzResearch.WordTrace tailWord_94293 prefixEnd_94293 43037894537337610581209 := by
  unfold tailWord_94293
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439148247400039807407533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2292765498266693204938355 3439148247400039807407533)
  ·
    refine ⟨1289680592775014927777825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3439148247400039807407533 1289680592775014927777825)
    ·
      refine ⟨967260444581261195833369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1289680592775014927777825 967260444581261195833369)
      ·
        refine ⟨725445333435945896875027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967260444581261195833369 725445333435945896875027)
        ·
          refine ⟨1088168000153918845312541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725445333435945896875027 1088168000153918845312541)
          ·
            refine ⟨408063000057719566992203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1088168000153918845312541 408063000057719566992203)
            ·
              refine ⟨612094500086579350488305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408063000057719566992203 612094500086579350488305)
              ·
                refine ⟨459070875064934512866229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612094500086579350488305 459070875064934512866229)
                ·
                  refine ⟨43037894537337610581209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459070875064934512866229 43037894537337610581209)
                  ·
                    rfl

theorem cell20_94293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_94293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94293 prefixEnd_94293 := by exact prefixLift 94293
  have htrace : WordTrace (prefixWord ++ tailWord_94293) baseStart_94293 baseEnd_94293 := by
    simpa [prefixWord, tailWord_94293, baseEnd_94293] using wordTrace_append hprefix tailTrace_94293
  have hstable : (prefixWord ++ tailWord_94293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94293).length < 2 ^ (prefixWord ++ tailWord_94293).sum := by decide
  have hdescent : baseEnd_94293 < baseStart_94293 := by decide
  rcases family_descends (prefixWord ++ tailWord_94293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94296 : List Nat := [2, 1, 2, 2, 1, 4, 3, 3, 2]
def baseStart_94296 : Nat := 118140960795 + 94296 * 2 ^ 59
def prefixEnd_94296 : Nat := 4983230072969 + 3 ^ 40 * 94296 * 2
def baseEnd_94296 : Nat := 43039263819082933481197

theorem tailTrace_94296 : CollatzResearch.WordTrace tailWord_94296 prefixEnd_94296 43039263819082933481197 := by
  unfold tailWord_94296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719628833194585659883371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2292838444259447546511161 1719628833194585659883371)
  ·
    refine ⟨2579443249791878489825057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1719628833194585659883371 2579443249791878489825057)
    ·
      refine ⟨1934582437343908867368793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2579443249791878489825057 1934582437343908867368793)
      ·
        refine ⟨1450936828007931650526595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1934582437343908867368793 1450936828007931650526595)
        ·
          refine ⟨2176405242011897475789893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450936828007931650526595 2176405242011897475789893)
          ·
            refine ⟨408075982877230776710605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2176405242011897475789893 408075982877230776710605)
            ·
              refine ⟨153028493578961541266477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408075982877230776710605 153028493578961541266477)
              ·
                refine ⟨57385685092110577974929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153028493578961541266477 57385685092110577974929)
                ·
                  refine ⟨43039263819082933481197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57385685092110577974929 43039263819082933481197)
                  ·
                    rfl

theorem cell20_94296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_94296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94296 prefixEnd_94296 := by exact prefixLift 94296
  have htrace : WordTrace (prefixWord ++ tailWord_94296) baseStart_94296 baseEnd_94296 := by
    simpa [prefixWord, tailWord_94296, baseEnd_94296] using wordTrace_append hprefix tailTrace_94296
  have hstable : (prefixWord ++ tailWord_94296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94296).length < 2 ^ (prefixWord ++ tailWord_94296).sum := by decide
  have hdescent : baseEnd_94296 < baseStart_94296 := by decide
  rcases family_descends (prefixWord ++ tailWord_94296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94307 : List Nat := [1, 1, 1, 5, 1, 1, 10]
def baseStart_94307 : Nat := 118140960795 + 94307 * 2 ^ 59
def prefixEnd_94307 : Nat := 4983230072969 + 3 ^ 40 * 94307 * 2
def baseEnd_94307 : Nat := 4782698279868420457165

theorem tailTrace_94307 : CollatzResearch.WordTrace tailWord_94307 prefixEnd_94307 4782698279868420457165 := by
  unfold tailWord_94307
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439658869349320198417175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2293105912899546798944783 3439658869349320198417175)
  ·
    refine ⟨5159488304023980297625763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3439658869349320198417175 5159488304023980297625763)
    ·
      refine ⟨7739232456035970446438645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5159488304023980297625763 7739232456035970446438645)
      ·
        refine ⟨725553042753372229353623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7739232456035970446438645 725553042753372229353623)
        ·
          refine ⟨1088329564130058344030435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725553042753372229353623 1088329564130058344030435)
          ·
            refine ⟨1632494346195087516045653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088329564130058344030435 1632494346195087516045653)
            ·
              refine ⟨4782698279868420457165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1632494346195087516045653 4782698279868420457165)
              ·
                rfl

theorem cell20_94307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_94307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94307 prefixEnd_94307 := by exact prefixLift 94307
  have htrace : WordTrace (prefixWord ++ tailWord_94307) baseStart_94307 baseEnd_94307 := by
    simpa [prefixWord, tailWord_94307, baseEnd_94307] using wordTrace_append hprefix tailTrace_94307
  have hstable : (prefixWord ++ tailWord_94307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94307).length < 2 ^ (prefixWord ++ tailWord_94307).sum := by decide
  have hdescent : baseEnd_94307 < baseStart_94307 := by decide
  rcases family_descends (prefixWord ++ tailWord_94307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94327 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 3]
def baseStart_94327 : Nat := 118140960795 + 94327 * 2 ^ 59
def prefixEnd_94327 : Nat := 4983230072969 + 3 ^ 40 * 94327 * 2
def baseEnd_94327 : Nat := 43053413063784603447737

theorem tailTrace_94327 : CollatzResearch.WordTrace tailWord_94327 prefixEnd_94327 43053413063784603447737 := by
  unfold tailWord_94327
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440388329276863614145235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2293592219517909076096823 3440388329276863614145235)
  ·
    refine ⟨5160582493915295421217853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3440388329276863614145235 5160582493915295421217853)
    ·
      refine ⟨1935218435218235782956695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5160582493915295421217853 1935218435218235782956695)
      ·
        refine ⟨2902827652827353674435043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935218435218235782956695 2902827652827353674435043)
        ·
          refine ⟨4354241479241030511652565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902827652827353674435043 4354241479241030511652565)
          ·
            refine ⟨102052534669711652616857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4354241479241030511652565 102052534669711652616857)
            ·
              refine ⟨76539401002283739462643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102052534669711652616857 76539401002283739462643)
              ·
                refine ⟨114809101503425609193965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76539401002283739462643 114809101503425609193965)
                ·
                  refine ⟨43053413063784603447737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114809101503425609193965 43053413063784603447737)
                  ·
                    rfl

theorem cell20_94327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 3].length) (baseStart_94327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94327 prefixEnd_94327 := by exact prefixLift 94327
  have htrace : WordTrace (prefixWord ++ tailWord_94327) baseStart_94327 baseEnd_94327 := by
    simpa [prefixWord, tailWord_94327, baseEnd_94327] using wordTrace_append hprefix tailTrace_94327
  have hstable : (prefixWord ++ tailWord_94327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94327).length < 2 ^ (prefixWord ++ tailWord_94327).sum := by decide
  have hdescent : baseEnd_94327 < baseStart_94327 := by decide
  rcases family_descends (prefixWord ++ tailWord_94327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94345 : List Nat := [1, 2, 1, 1, 4, 2, 1, 8]
def baseStart_94345 : Nat := 118140960795 + 94345 * 2 ^ 59
def prefixEnd_94345 : Nat := 4983230072969 + 3 ^ 40 * 94345 * 2
def baseEnd_94345 : Nat := 14353876251418846949221

theorem tailTrace_94345 : CollatzResearch.WordTrace tailWord_94345 prefixEnd_94345 14353876251418846949221 := by
  unfold tailWord_94345
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441044843211652688300489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2294029895474435125533659 3441044843211652688300489)
  ·
    refine ⟨2580783632408739516225367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3441044843211652688300489 2580783632408739516225367)
    ·
      refine ⟨3871175448613109274338051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580783632408739516225367 3871175448613109274338051)
      ·
        refine ⟨5806763172919663911507077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3871175448613109274338051 5806763172919663911507077)
        ·
          refine ⟨1088768094922436983407577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5806763172919663911507077 1088768094922436983407577)
          ·
            refine ⟨816576071191827737555683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088768094922436983407577 816576071191827737555683)
            ·
              refine ⟨1224864106787741606333525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816576071191827737555683 1224864106787741606333525)
              ·
                refine ⟨14353876251418846949221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1224864106787741606333525 14353876251418846949221)
                ·
                  rfl

theorem cell20_94345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_94345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94345 prefixEnd_94345 := by exact prefixLift 94345
  have htrace : WordTrace (prefixWord ++ tailWord_94345) baseStart_94345 baseEnd_94345 := by
    simpa [prefixWord, tailWord_94345, baseEnd_94345] using wordTrace_append hprefix tailTrace_94345
  have hstable : (prefixWord ++ tailWord_94345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94345).length < 2 ^ (prefixWord ++ tailWord_94345).sum := by decide
  have hdescent : baseEnd_94345 < baseStart_94345 := by decide
  rcases family_descends (prefixWord ++ tailWord_94345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94355 : List Nat := [1, 1, 1, 2, 1, 2, 3, 7, 2]
def baseStart_94355 : Nat := 118140960795 + 94355 * 2 ^ 59
def prefixEnd_94355 : Nat := 4983230072969 + 3 ^ 40 * 94355 * 2
def baseEnd_94355 : Nat := 43066193026740950514289

theorem tailTrace_94355 : CollatzResearch.WordTrace tailWord_94355 prefixEnd_94355 43066193026740950514289 := by
  unfold tailWord_94355
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441409573175424396164519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2294273048783616264109679 3441409573175424396164519)
  ·
    refine ⟨5162114359763136594246779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3441409573175424396164519 5162114359763136594246779)
    ·
      refine ⟨7743171539644704891370169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5162114359763136594246779 7743171539644704891370169)
      ·
        refine ⟨5807378654733528668527627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7743171539644704891370169 5807378654733528668527627)
        ·
          refine ⟨8711067982100293002791441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5807378654733528668527627 8711067982100293002791441)
          ·
            refine ⟨6533300986575219752093581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8711067982100293002791441 6533300986575219752093581)
            ·
              refine ⟨2449987869965707407035093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6533300986575219752093581 2449987869965707407035093)
              ·
                refine ⟨57421590702321267352385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2449987869965707407035093 57421590702321267352385)
                ·
                  refine ⟨43066193026740950514289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57421590702321267352385 43066193026740950514289)
                  ·
                    rfl

theorem cell20_94355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 2].length) (baseStart_94355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94355 prefixEnd_94355 := by exact prefixLift 94355
  have htrace : WordTrace (prefixWord ++ tailWord_94355) baseStart_94355 baseEnd_94355 := by
    simpa [prefixWord, tailWord_94355, baseEnd_94355] using wordTrace_append hprefix tailTrace_94355
  have hstable : (prefixWord ++ tailWord_94355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94355).length < 2 ^ (prefixWord ++ tailWord_94355).sum := by decide
  have hdescent : baseEnd_94355 < baseStart_94355 := by decide
  rcases family_descends (prefixWord ++ tailWord_94355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94362 : List Nat := [3, 1, 1, 5, 2, 8]
def baseStart_94362 : Nat := 118140960795 + 94362 * 2 ^ 59
def prefixEnd_94362 : Nat := 4983230072969 + 3 ^ 40 * 94362 * 2
def baseEnd_94362 : Nat := 1595162519165927306701

theorem tailTrace_94362 : CollatzResearch.WordTrace tailWord_94362 prefixEnd_94362 1595162519165927306701 := by
  unfold tailWord_94362
  simp only [CollatzResearch.WordTrace]
  refine ⟨860416221037516147917335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2294443256100043061112893 860416221037516147917335)
  ·
    refine ⟨1290624331556274221876003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 860416221037516147917335 1290624331556274221876003)
    ·
      refine ⟨1935936497334411332814005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1290624331556274221876003 1935936497334411332814005)
      ·
        refine ⟨181494046625101062451313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1935936497334411332814005 181494046625101062451313)
        ·
          refine ⟨136120534968825796838485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181494046625101062451313 136120534968825796838485)
          ·
            refine ⟨1595162519165927306701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 136120534968825796838485 1595162519165927306701)
            ·
              rfl

theorem cell20_94362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 8].length) (baseStart_94362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94362 prefixEnd_94362 := by exact prefixLift 94362
  have htrace : WordTrace (prefixWord ++ tailWord_94362) baseStart_94362 baseEnd_94362 := by
    simpa [prefixWord, tailWord_94362, baseEnd_94362] using wordTrace_append hprefix tailTrace_94362
  have hstable : (prefixWord ++ tailWord_94362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94362).length < 2 ^ (prefixWord ++ tailWord_94362).sum := by decide
  have hdescent : baseEnd_94362 < baseStart_94362 := by decide
  rcases family_descends (prefixWord ++ tailWord_94362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94410 : List Nat := [3, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_94410 : Nat := 118140960795 + 94410 * 2 ^ 59
def prefixEnd_94410 : Nat := 4983230072969 + 3 ^ 40 * 94410 * 2
def baseEnd_94410 : Nat := 43091296525405203680731

theorem tailTrace_94410 : CollatzResearch.WordTrace tailWord_94410 prefixEnd_94410 43091296525405203680731 := by
  unfold tailWord_94410
  simp only [CollatzResearch.WordTrace]
  refine ⟨860853896994042197354171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2295610391984112526277789 860853896994042197354171)
  ·
    refine ⟨1291280845491063296031257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 860853896994042197354171 1291280845491063296031257)
    ·
      refine ⟨968460634118297472023443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1291280845491063296031257 968460634118297472023443)
      ·
        refine ⟨1452690951177446208035165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968460634118297472023443 1452690951177446208035165)
        ·
          refine ⟨544759106691542328013187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1452690951177446208035165 544759106691542328013187)
          ·
            refine ⟨817138660037313492019781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544759106691542328013187 817138660037313492019781)
            ·
              refine ⟨153213498756996279753709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 817138660037313492019781 153213498756996279753709)
              ·
                refine ⟨57455062033873604907641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153213498756996279753709 57455062033873604907641)
                ·
                  refine ⟨43091296525405203680731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57455062033873604907641 43091296525405203680731)
                  ·
                    rfl

theorem cell20_94410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_94410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94410 prefixEnd_94410 := by exact prefixLift 94410
  have htrace : WordTrace (prefixWord ++ tailWord_94410) baseStart_94410 baseEnd_94410 := by
    simpa [prefixWord, tailWord_94410, baseEnd_94410] using wordTrace_append hprefix tailTrace_94410
  have hstable : (prefixWord ++ tailWord_94410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94410).length < 2 ^ (prefixWord ++ tailWord_94410).sum := by decide
  have hdescent : baseEnd_94410 < baseStart_94410 := by decide
  rcases family_descends (prefixWord ++ tailWord_94410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94424 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_94424 : Nat := 118140960795 + 94424 * 2 ^ 59
def prefixEnd_94424 : Nat := 4983230072969 + 3 ^ 40 * 94424 * 2
def baseEnd_94424 : Nat := 43097686506883377214007

theorem tailTrace_94424 : CollatzResearch.WordTrace tailWord_94424 prefixEnd_94424 43097686506883377214007 := by
  unfold tailWord_94424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721963104962724590213163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2295950806616966120284217 1721963104962724590213163)
  ·
    refine ⟨2582944657444086885319745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721963104962724590213163 2582944657444086885319745)
    ·
      refine ⟨1937208493083065163989809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2582944657444086885319745 1937208493083065163989809)
      ·
        refine ⟨1452906369812298872992357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1937208493083065163989809 1452906369812298872992357)
        ·
          refine ⟨272419944339806038686067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1452906369812298872992357 272419944339806038686067)
          ·
            refine ⟨408629916509709058029101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272419944339806038686067 408629916509709058029101)
            ·
              refine ⟨153236218691140896760913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408629916509709058029101 153236218691140896760913)
              ·
                refine ⟨114927164018355672570685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153236218691140896760913 114927164018355672570685)
                ·
                  refine ⟨43097686506883377214007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114927164018355672570685 43097686506883377214007)
                  ·
                    rfl

theorem cell20_94424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_94424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94424 prefixEnd_94424 := by exact prefixLift 94424
  have htrace : WordTrace (prefixWord ++ tailWord_94424) baseStart_94424 baseEnd_94424 := by
    simpa [prefixWord, tailWord_94424, baseEnd_94424] using wordTrace_append hprefix tailTrace_94424
  have hstable : (prefixWord ++ tailWord_94424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94424).length < 2 ^ (prefixWord ++ tailWord_94424).sum := by decide
  have hdescent : baseEnd_94424 < baseStart_94424 := by decide
  rcases family_descends (prefixWord ++ tailWord_94424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94469 : List Nat := [1, 3, 1, 1, 2, 1, 2, 7, 2]
def baseStart_94469 : Nat := 118140960795 + 94469 * 2 ^ 59
def prefixEnd_94469 : Nat := 4983230072969 + 3 ^ 40 * 94469 * 2
def baseEnd_94469 : Nat := 43118225733063220713823

theorem tailTrace_94469 : CollatzResearch.WordTrace tailWord_94469 prefixEnd_94469 43118225733063220713823 := by
  unfold tailWord_94469
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445567494762421865814461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2297044996508281243876307 3445567494762421865814461)
  ·
    refine ⟨1292087810535908199680423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3445567494762421865814461 1292087810535908199680423)
    ·
      refine ⟨1938131715803862299520635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292087810535908199680423 1938131715803862299520635)
      ·
        refine ⟨2907197573705793449280953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938131715803862299520635 2907197573705793449280953)
        ·
          refine ⟨2180398180279345086960715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907197573705793449280953 2180398180279345086960715)
          ·
            refine ⟨3270597270419017630441073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180398180279345086960715 3270597270419017630441073)
            ·
              refine ⟨2452947952814263222830805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3270597270419017630441073 2452947952814263222830805)
              ·
                refine ⟨57490967644084294285097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2452947952814263222830805 57490967644084294285097)
                ·
                  refine ⟨43118225733063220713823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57490967644084294285097 43118225733063220713823)
                  ·
                    rfl

theorem cell20_94469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_94469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94469 prefixEnd_94469 := by exact prefixLift 94469
  have htrace : WordTrace (prefixWord ++ tailWord_94469) baseStart_94469 baseEnd_94469 := by
    simpa [prefixWord, tailWord_94469, baseEnd_94469] using wordTrace_append hprefix tailTrace_94469
  have hstable : (prefixWord ++ tailWord_94469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94469).length < 2 ^ (prefixWord ++ tailWord_94469).sum := by decide
  have hdescent : baseEnd_94469 < baseStart_94469 := by decide
  rcases family_descends (prefixWord ++ tailWord_94469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94493 : List Nat := [1, 4, 2, 3, 2, 1, 2, 5]
def baseStart_94493 : Nat := 118140960795 + 94493 * 2 ^ 59
def prefixEnd_94493 : Nat := 4983230072969 + 3 ^ 40 * 94493 * 2
def baseEnd_94493 : Nat := 14376393329008601304575

theorem tailTrace_94493 : CollatzResearch.WordTrace tailWord_94493 prefixEnd_94493 14376393329008601304575 := by
  unfold tailWord_94493
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446442846675473964688133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2297628564450315976458755 3446442846675473964688133)
  ·
    refine ⟨646208033751651368379025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3446442846675473964688133 646208033751651368379025)
    ·
      refine ⟨484656025313738526284269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 646208033751651368379025 484656025313738526284269)
      ·
        refine ⟨181746009492651947356601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 484656025313738526284269 181746009492651947356601)
        ·
          refine ⟨136309507119488960517451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181746009492651947356601 136309507119488960517451)
          ·
            refine ⟨204464260679233440776177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136309507119488960517451 204464260679233440776177)
            ·
              refine ⟨153348195509425080582133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204464260679233440776177 153348195509425080582133)
              ·
                refine ⟨14376393329008601304575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153348195509425080582133 14376393329008601304575)
                ·
                  rfl

theorem cell20_94493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_94493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94493 prefixEnd_94493 := by exact prefixLift 94493
  have htrace : WordTrace (prefixWord ++ tailWord_94493) baseStart_94493 baseEnd_94493 := by
    simpa [prefixWord, tailWord_94493, baseEnd_94493] using wordTrace_append hprefix tailTrace_94493
  have hstable : (prefixWord ++ tailWord_94493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94493).length < 2 ^ (prefixWord ++ tailWord_94493).sum := by decide
  have hdescent : baseEnd_94493 < baseStart_94493 := by decide
  rcases family_descends (prefixWord ++ tailWord_94493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94497 : List Nat := [1, 2, 3, 2, 1, 1, 3, 7]
def baseStart_94497 : Nat := 118140960795 + 94497 * 2 ^ 59
def prefixEnd_94497 : Nat := 4983230072969 + 3 ^ 40 * 94497 * 2
def baseEnd_94497 : Nat := 14377001898673189260125

theorem tailTrace_94497 : CollatzResearch.WordTrace tailWord_94497 prefixEnd_94497 14377001898673189260125 := by
  unfold tailWord_94497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446588738660982647833745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2297725825773988431889163 3446588738660982647833745)
  ·
    refine ⟨2584941553995736985875309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3446588738660982647833745 2584941553995736985875309)
    ·
      refine ⟨969353082748401369703241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2584941553995736985875309 969353082748401369703241)
      ·
        refine ⟨727014812061301027277431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969353082748401369703241 727014812061301027277431)
        ·
          refine ⟨1090522218091951540916147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727014812061301027277431 1090522218091951540916147)
          ·
            refine ⟨1635783327137927311374221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090522218091951540916147 1635783327137927311374221)
            ·
              refine ⟨613418747676722741765333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1635783327137927311374221 613418747676722741765333)
              ·
                refine ⟨14377001898673189260125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 613418747676722741765333 14377001898673189260125)
                ·
                  rfl

theorem cell20_94497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_94497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94497 prefixEnd_94497 := by exact prefixLift 94497
  have htrace : WordTrace (prefixWord ++ tailWord_94497) baseStart_94497 baseEnd_94497 := by
    simpa [prefixWord, tailWord_94497, baseEnd_94497] using wordTrace_append hprefix tailTrace_94497
  have hstable : (prefixWord ++ tailWord_94497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94497).length < 2 ^ (prefixWord ++ tailWord_94497).sum := by decide
  have hdescent : baseEnd_94497 < baseStart_94497 := by decide
  rcases family_descends (prefixWord ++ tailWord_94497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94500 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_94500 : Nat := 118140960795 + 94500 * 2 ^ 59
def prefixEnd_94500 : Nat := 4983230072969 + 3 ^ 40 * 94500 * 2
def baseEnd_94500 : Nat := 43132374977764890680363

theorem tailTrace_94500 : CollatzResearch.WordTrace tailWord_94500 prefixEnd_94500 43132374977764890680363 := by
  unfold tailWord_94500
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723349078825057080096477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2297798771766742773461969 1723349078825057080096477)
  ·
    refine ⟨646255904559396405036179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1723349078825057080096477 646255904559396405036179)
    ·
      refine ⟨969383856839094607554269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646255904559396405036179 969383856839094607554269)
      ·
        refine ⟨363518946314660477832851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 969383856839094607554269 363518946314660477832851)
        ·
          refine ⟨545278419471990716749277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363518946314660477832851 545278419471990716749277)
          ·
            refine ⟨204479407301996518780979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 545278419471990716749277 204479407301996518780979)
            ·
              refine ⟨306719110952994778171469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204479407301996518780979 306719110952994778171469)
              ·
                refine ⟨115019666607373041814301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306719110952994778171469 115019666607373041814301)
                ·
                  refine ⟨43132374977764890680363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115019666607373041814301 43132374977764890680363)
                  ·
                    rfl

theorem cell20_94500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_94500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94500 prefixEnd_94500 := by exact prefixLift 94500
  have htrace : WordTrace (prefixWord ++ tailWord_94500) baseStart_94500 baseEnd_94500 := by
    simpa [prefixWord, tailWord_94500, baseEnd_94500] using wordTrace_append hprefix tailTrace_94500
  have hstable : (prefixWord ++ tailWord_94500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94500).length < 2 ^ (prefixWord ++ tailWord_94500).sum := by decide
  have hdescent : baseEnd_94500 < baseStart_94500 := by decide
  rcases family_descends (prefixWord ++ tailWord_94500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94559 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 3]
def baseStart_94559 : Nat := 118140960795 + 94559 * 2 ^ 59
def prefixEnd_94559 : Nat := 4983230072969 + 3 ^ 40 * 94559 * 2
def baseEnd_94559 : Nat := 43159304185422907713455

theorem tailTrace_94559 : CollatzResearch.WordTrace tailWord_94559 prefixEnd_94559 43159304185422907713455 := by
  unfold tailWord_94559
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448850064436367236590731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2299233376290911491060487 3448850064436367236590731)
  ·
    refine ⟨5173275096654550854886097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3448850064436367236590731 5173275096654550854886097)
    ·
      refine ⟨3879956322490913141164573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5173275096654550854886097 3879956322490913141164573)
      ·
        refine ⟨1454983620934092427936715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3879956322490913141164573 1454983620934092427936715)
        ·
          refine ⟨2182475431401138641905073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454983620934092427936715 2182475431401138641905073)
          ·
            refine ⟨1636856573550853981428805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2182475431401138641905073 1636856573550853981428805)
            ·
              refine ⟨306910607540785121517901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1636856573550853981428805 306910607540785121517901)
              ·
                refine ⟨115091477827794420569213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306910607540785121517901 115091477827794420569213)
                ·
                  refine ⟨43159304185422907713455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115091477827794420569213 43159304185422907713455)
                  ·
                    rfl

theorem cell20_94559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_94559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94559 prefixEnd_94559 := by exact prefixLift 94559
  have htrace : WordTrace (prefixWord ++ tailWord_94559) baseStart_94559 baseEnd_94559 := by
    simpa [prefixWord, tailWord_94559, baseEnd_94559] using wordTrace_append hprefix tailTrace_94559
  have hstable : (prefixWord ++ tailWord_94559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94559).length < 2 ^ (prefixWord ++ tailWord_94559).sum := by decide
  have hdescent : baseEnd_94559 < baseStart_94559 := by decide
  rcases family_descends (prefixWord ++ tailWord_94559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94593 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 3]
def baseStart_94593 : Nat := 118140960795 + 94593 * 2 ^ 59
def prefixEnd_94593 : Nat := 4983230072969 + 3 ^ 40 * 94593 * 2
def baseEnd_94593 : Nat := 43174822711869900579983

theorem tailTrace_94593 : CollatzResearch.WordTrace tailWord_94593 prefixEnd_94593 43174822711869900579983 := by
  unfold tailWord_94593
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450090146313191043328433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2300060097542127362218955 3450090146313191043328433)
  ·
    refine ⟨2587567609734893282496325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3450090146313191043328433 2587567609734893282496325)
    ·
      refine ⟨485168926825292490468061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2587567609734893282496325 485168926825292490468061)
      ·
        refine ⟨181938347559484683925523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485168926825292490468061 181938347559484683925523)
        ·
          refine ⟨272907521339227025888285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181938347559484683925523 272907521339227025888285)
          ·
            refine ⟨102340320502210134708107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272907521339227025888285 102340320502210134708107)
            ·
              refine ⟨153510480753315202062161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102340320502210134708107 153510480753315202062161)
              ·
                refine ⟨115132860564986401546621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153510480753315202062161 115132860564986401546621)
                ·
                  refine ⟨43174822711869900579983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115132860564986401546621 43174822711869900579983)
                  ·
                    rfl

theorem cell20_94593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_94593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94593 prefixEnd_94593 := by exact prefixLift 94593
  have htrace : WordTrace (prefixWord ++ tailWord_94593) baseStart_94593 baseEnd_94593 := by
    simpa [prefixWord, tailWord_94593, baseEnd_94593] using wordTrace_append hprefix tailTrace_94593
  have hstable : (prefixWord ++ tailWord_94593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94593).length < 2 ^ (prefixWord ++ tailWord_94593).sum := by decide
  have hdescent : baseEnd_94593 < baseStart_94593 := by decide
  rcases family_descends (prefixWord ++ tailWord_94593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94604 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_94604 : Nat := 118140960795 + 94604 * 2 ^ 59
def prefixEnd_94604 : Nat := 4983230072969 + 3 ^ 40 * 94604 * 2
def baseEnd_94604 : Nat := 43179843411602751213271

theorem tailTrace_94604 : CollatzResearch.WordTrace tailWord_94604 prefixEnd_94604 43179843411602751213271 := by
  unfold tailWord_94604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725245674636669960989433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2300327566182226614652577 1725245674636669960989433)
  ·
    refine ⟨1293934255977502470742075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1725245674636669960989433 1293934255977502470742075)
    ·
      refine ⟨1940901383966253706113113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293934255977502470742075 1940901383966253706113113)
      ·
        refine ⟨1455676037974690279584835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1940901383966253706113113 1455676037974690279584835)
        ·
          refine ⟨2183514056962035419377253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455676037974690279584835 2183514056962035419377253)
          ·
            refine ⟨409408885680381641133235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2183514056962035419377253 409408885680381641133235)
            ·
              refine ⟨614113328520572461699853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409408885680381641133235 614113328520572461699853)
              ·
                refine ⟨230292498195214673137445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 614113328520572461699853 230292498195214673137445)
                ·
                  refine ⟨43179843411602751213271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230292498195214673137445 43179843411602751213271)
                  ·
                    rfl

theorem cell20_94604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_94604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94604 prefixEnd_94604 := by exact prefixLift 94604
  have htrace : WordTrace (prefixWord ++ tailWord_94604) baseStart_94604 baseEnd_94604 := by
    simpa [prefixWord, tailWord_94604, baseEnd_94604] using wordTrace_append hprefix tailTrace_94604
  have hstable : (prefixWord ++ tailWord_94604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94604).length < 2 ^ (prefixWord ++ tailWord_94604).sum := by decide
  have hdescent : baseEnd_94604 < baseStart_94604 := by decide
  rcases family_descends (prefixWord ++ tailWord_94604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94628 : List Nat := [2, 3, 1, 2, 1, 1, 6, 4]
def baseStart_94628 : Nat := 118140960795 + 94628 * 2 ^ 59
def prefixEnd_94628 : Nat := 4983230072969 + 3 ^ 40 * 94628 * 2
def baseEnd_94628 : Nat := 14396932555188444804391

theorem tailTrace_94628 : CollatzResearch.WordTrace tailWord_94628 prefixEnd_94628 14396932555188444804391 := by
  unfold tailWord_94628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725683350593196010426269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2300911134124261347235025 1725683350593196010426269)
  ·
    refine ⟨647131256472448503909851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1725683350593196010426269 647131256472448503909851)
    ·
      refine ⟨970696884708672755864777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647131256472448503909851 970696884708672755864777)
      ·
        refine ⟨728022663531504566898583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 970696884708672755864777 728022663531504566898583)
        ·
          refine ⟨1092033995297256850347875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728022663531504566898583 1092033995297256850347875)
          ·
            refine ⟨1638050992945885275521813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092033995297256850347875 1638050992945885275521813)
            ·
              refine ⟨76783640294338372290085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1638050992945885275521813 76783640294338372290085)
              ·
                refine ⟨14396932555188444804391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76783640294338372290085 14396932555188444804391)
                ·
                  rfl

theorem cell20_94628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_94628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94628 prefixEnd_94628 := by exact prefixLift 94628
  have htrace : WordTrace (prefixWord ++ tailWord_94628) baseStart_94628 baseEnd_94628 := by
    simpa [prefixWord, tailWord_94628, baseEnd_94628] using wordTrace_append hprefix tailTrace_94628
  have hstable : (prefixWord ++ tailWord_94628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94628).length < 2 ^ (prefixWord ++ tailWord_94628).sum := by decide
  have hdescent : baseEnd_94628 < baseStart_94628 := by decide
  rcases family_descends (prefixWord ++ tailWord_94628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94645 : List Nat := [1, 3, 3, 2, 4, 1, 6]
def baseStart_94645 : Nat := 118140960795 + 94645 * 2 ^ 59
def prefixEnd_94645 : Nat := 4983230072969 + 3 ^ 40 * 94645 * 2
def baseEnd_94645 : Nat := 4799839658754314538493

theorem tailTrace_94645 : CollatzResearch.WordTrace tailWord_94645 prefixEnd_94645 4799839658754314538493 := by
  unfold tailWord_94645
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451986742124803924221389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2301324494749869282814259 3451986742124803924221389)
  ·
    refine ⟨1294495028296801471583021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3451986742124803924221389 1294495028296801471583021)
    ·
      refine ⟨485435635611300551843633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1294495028296801471583021 485435635611300551843633)
      ·
        refine ⟨364076726708475413882725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485435635611300551843633 364076726708475413882725)
        ·
          refine ⟨68264386257839140103011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364076726708475413882725 68264386257839140103011)
          ·
            refine ⟨102396579386758710154517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68264386257839140103011 102396579386758710154517)
            ·
              refine ⟨4799839658754314538493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102396579386758710154517 4799839658754314538493)
              ·
                rfl

theorem cell20_94645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 6].length) (baseStart_94645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94645 prefixEnd_94645 := by exact prefixLift 94645
  have htrace : WordTrace (prefixWord ++ tailWord_94645) baseStart_94645 baseEnd_94645 := by
    simpa [prefixWord, tailWord_94645, baseEnd_94645] using wordTrace_append hprefix tailTrace_94645
  have hstable : (prefixWord ++ tailWord_94645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94645).length < 2 ^ (prefixWord ++ tailWord_94645).sum := by decide
  have hdescent : baseEnd_94645 < baseStart_94645 := by decide
  rcases family_descends (prefixWord ++ tailWord_94645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94649 : List Nat := [1, 2, 1, 4, 3, 1, 8]
def baseStart_94649 : Nat := 118140960795 + 94649 * 2 ^ 59
def prefixEnd_94649 : Nat := 4983230072969 + 3 ^ 40 * 94649 * 2
def baseEnd_94649 : Nat := 4800042515309177190343

theorem tailTrace_94649 : CollatzResearch.WordTrace tailWord_94649 prefixEnd_94649 4800042515309177190343 := by
  unfold tailWord_94649
  simp only [CollatzResearch.WordTrace]
  refine ⟨3452132634110312607367001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2301421756073541738244667 3452132634110312607367001)
  ·
    refine ⟨2589099475582734455525251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3452132634110312607367001 2589099475582734455525251)
    ·
      refine ⟨3883649213374101683287877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2589099475582734455525251 3883649213374101683287877)
      ·
        refine ⟨728184227507644065616477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3883649213374101683287877 728184227507644065616477)
        ·
          refine ⟨273069085315366524606179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 728184227507644065616477 273069085315366524606179)
          ·
            refine ⟨409603627973049786909269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273069085315366524606179 409603627973049786909269)
            ·
              refine ⟨4800042515309177190343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 409603627973049786909269 4800042515309177190343)
              ·
                rfl

theorem cell20_94649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_94649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94649 prefixEnd_94649 := by exact prefixLift 94649
  have htrace : WordTrace (prefixWord ++ tailWord_94649) baseStart_94649 baseEnd_94649 := by
    simpa [prefixWord, tailWord_94649, baseEnd_94649] using wordTrace_append hprefix tailTrace_94649
  have hstable : (prefixWord ++ tailWord_94649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94649).length < 2 ^ (prefixWord ++ tailWord_94649).sum := by decide
  have hdescent : baseEnd_94649 < baseStart_94649 := by decide
  rcases family_descends (prefixWord ++ tailWord_94649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94687 : List Nat := [1, 1, 2, 3, 3, 2, 2, 6]
def baseStart_94687 : Nat := 118140960795 + 94687 * 2 ^ 59
def prefixEnd_94687 : Nat := 4983230072969 + 3 ^ 40 * 94687 * 2
def baseEnd_94687 : Nat := 14405908957741117148755

theorem tailTrace_94687 : CollatzResearch.WordTrace tailWord_94687 prefixEnd_94687 14405908957741117148755 := by
  unfold tailWord_94687
  simp only [CollatzResearch.WordTrace]
  refine ⟨3453518607972645097250315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2302345738648430064833543 3453518607972645097250315)
  ·
    refine ⟨5180277911958967645875473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3453518607972645097250315 5180277911958967645875473)
    ·
      refine ⟨3885208433969225734406605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5180277911958967645875473 3885208433969225734406605)
      ·
        refine ⟨1456953162738459650402477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3885208433969225734406605 1456953162738459650402477)
        ·
          refine ⟨546357436026922368900929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1456953162738459650402477 546357436026922368900929)
          ·
            refine ⟨409768077020191776675697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546357436026922368900929 409768077020191776675697)
            ·
              refine ⟨307326057765143832506773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409768077020191776675697 307326057765143832506773)
              ·
                refine ⟨14405908957741117148755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 307326057765143832506773 14405908957741117148755)
                ·
                  rfl

theorem cell20_94687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_94687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94687 prefixEnd_94687 := by exact prefixLift 94687
  have htrace : WordTrace (prefixWord ++ tailWord_94687) baseStart_94687 baseEnd_94687 := by
    simpa [prefixWord, tailWord_94687, baseEnd_94687] using wordTrace_append hprefix tailTrace_94687
  have hstable : (prefixWord ++ tailWord_94687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94687).length < 2 ^ (prefixWord ++ tailWord_94687).sum := by decide
  have hdescent : baseEnd_94687 < baseStart_94687 := by decide
  rcases family_descends (prefixWord ++ tailWord_94687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94725 : List Nat := [1, 3, 1, 1, 2, 2, 5, 5]
def baseStart_94725 : Nat := 118140960795 + 94725 * 2 ^ 59
def prefixEnd_94725 : Nat := 4983230072969 + 3 ^ 40 * 94725 * 2
def baseEnd_94725 : Nat := 14411690369554702726481

theorem tailTrace_94725 : CollatzResearch.WordTrace tailWord_94725 prefixEnd_94725 14411690369554702726481 := by
  unfold tailWord_94725
  simp only [CollatzResearch.WordTrace]
  refine ⟨3454904581834977587133629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2303269721223318391422419 3454904581834977587133629)
  ·
    refine ⟨1295589218188116595175111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3454904581834977587133629 1295589218188116595175111)
    ·
      refine ⟨1943383827282174892762667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295589218188116595175111 1943383827282174892762667)
      ·
        refine ⟨2915075740923262339144001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943383827282174892762667 2915075740923262339144001)
        ·
          refine ⟨2186306805692446754358001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2915075740923262339144001 2186306805692446754358001)
          ·
            refine ⟨1639730104269335065768501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186306805692446754358001 1639730104269335065768501)
            ·
              refine ⟨153724697275250162415797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1639730104269335065768501 153724697275250162415797)
              ·
                refine ⟨14411690369554702726481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153724697275250162415797 14411690369554702726481)
                ·
                  rfl

theorem cell20_94725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_94725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94725 prefixEnd_94725 := by exact prefixLift 94725
  have htrace : WordTrace (prefixWord ++ tailWord_94725) baseStart_94725 baseEnd_94725 := by
    simpa [prefixWord, tailWord_94725, baseEnd_94725] using wordTrace_append hprefix tailTrace_94725
  have hstable : (prefixWord ++ tailWord_94725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94725).length < 2 ^ (prefixWord ++ tailWord_94725).sum := by decide
  have hdescent : baseEnd_94725 < baseStart_94725 := by decide
  rcases family_descends (prefixWord ++ tailWord_94725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94759 : List Nat := [1, 1, 7, 2, 1, 1, 7]
def baseStart_94759 : Nat := 118140960795 + 94759 * 2 ^ 59
def prefixEnd_94759 : Nat := 4983230072969 + 3 ^ 40 * 94759 * 2
def baseEnd_94759 : Nat := 4805621070567900116219

theorem tailTrace_94759 : CollatzResearch.WordTrace tailWord_94759 prefixEnd_94759 4805621070567900116219 := by
  unfold tailWord_94759
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456144663711801393871331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2304096442474534262580887 3456144663711801393871331)
  ·
    refine ⟨5184216995567702090806997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3456144663711801393871331 5184216995567702090806997)
    ·
      refine ⟨121505085833618017753289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5184216995567702090806997 121505085833618017753289)
      ·
        refine ⟨91128814375213513314967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121505085833618017753289 91128814375213513314967)
        ·
          refine ⟨136693221562820269972451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91128814375213513314967 136693221562820269972451)
          ·
            refine ⟨205039832344230404958677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136693221562820269972451 205039832344230404958677)
            ·
              refine ⟨4805621070567900116219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 205039832344230404958677 4805621070567900116219)
              ·
                rfl

theorem cell20_94759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 7].length) (baseStart_94759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94759 prefixEnd_94759 := by exact prefixLift 94759
  have htrace : WordTrace (prefixWord ++ tailWord_94759) baseStart_94759 baseEnd_94759 := by
    simpa [prefixWord, tailWord_94759, baseEnd_94759] using wordTrace_append hprefix tailTrace_94759
  have hstable : (prefixWord ++ tailWord_94759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94759).length < 2 ^ (prefixWord ++ tailWord_94759).sum := by decide
  have hdescent : baseEnd_94759 < baseStart_94759 := by decide
  rcases family_descends (prefixWord ++ tailWord_94759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94766 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_94766 : Nat := 118140960795 + 94766 * 2 ^ 59
def prefixEnd_94766 : Nat := 4983230072969 + 3 ^ 40 * 94766 * 2
def baseEnd_94766 : Nat := 43253784625850187812609

theorem tailTrace_94766 : CollatzResearch.WordTrace tailWord_94766 prefixEnd_94766 43253784625850187812609 := by
  unfold tailWord_94766
  simp only [CollatzResearch.WordTrace]
  refine ⟨432049996835805198672019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2304266649790961059584101 432049996835805198672019)
  ·
    refine ⟨648074995253707798008029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 432049996835805198672019 648074995253707798008029)
    ·
      refine ⟨243028123220140424253011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 648074995253707798008029 243028123220140424253011)
      ·
        refine ⟨364542184830210636379517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243028123220140424253011 364542184830210636379517)
        ·
          refine ⟨136703319311328988642319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364542184830210636379517 136703319311328988642319)
          ·
            refine ⟨205054978966993482963479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136703319311328988642319 205054978966993482963479)
            ·
              refine ⟨307582468450490224445219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205054978966993482963479 307582468450490224445219)
              ·
                refine ⟨461373702675735336667829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307582468450490224445219 461373702675735336667829)
                ·
                  refine ⟨43253784625850187812609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 461373702675735336667829 43253784625850187812609)
                  ·
                    rfl

theorem cell20_94766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_94766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94766 prefixEnd_94766 := by exact prefixLift 94766
  have htrace : WordTrace (prefixWord ++ tailWord_94766) baseStart_94766 baseEnd_94766 := by
    simpa [prefixWord, tailWord_94766, baseEnd_94766] using wordTrace_append hprefix tailTrace_94766
  have hstable : (prefixWord ++ tailWord_94766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94766).length < 2 ^ (prefixWord ++ tailWord_94766).sum := by decide
  have hdescent : baseEnd_94766 < baseStart_94766 := by decide
  rcases family_descends (prefixWord ++ tailWord_94766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94773 : List Nat := [1, 3, 3, 1, 1, 2, 1, 6, 2]
def baseStart_94773 : Nat := 118140960795 + 94773 * 2 ^ 59
def prefixEnd_94773 : Nat := 4983230072969 + 3 ^ 40 * 94773 * 2
def baseEnd_94773 : Nat := 43256979616589274579247

theorem tailTrace_94773 : CollatzResearch.WordTrace tailWord_94773 prefixEnd_94773 43256979616589274579247 := by
  unfold tailWord_94773
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456655285661081784880973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2304436857107387856587315 3456655285661081784880973)
  ·
    refine ⟨1296245732122905669330365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3456655285661081784880973 1296245732122905669330365)
    ·
      refine ⟨486092149546089625998887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1296245732122905669330365 486092149546089625998887)
      ·
        refine ⟨729138224319134438998331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486092149546089625998887 729138224319134438998331)
        ·
          refine ⟨1093707336478701658497497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729138224319134438998331 1093707336478701658497497)
          ·
            refine ⟨820280502359026243873123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1093707336478701658497497 820280502359026243873123)
            ·
              refine ⟨1230420753538539365809685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820280502359026243873123 1230420753538539365809685)
              ·
                refine ⟨57675972822119032772329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1230420753538539365809685 57675972822119032772329)
                ·
                  refine ⟨43256979616589274579247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57675972822119032772329 43256979616589274579247)
                  ·
                    rfl

theorem cell20_94773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_94773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94773 prefixEnd_94773 := by exact prefixLift 94773
  have htrace : WordTrace (prefixWord ++ tailWord_94773) baseStart_94773 baseEnd_94773 := by
    simpa [prefixWord, tailWord_94773, baseEnd_94773] using wordTrace_append hprefix tailTrace_94773
  have hstable : (prefixWord ++ tailWord_94773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94773).length < 2 ^ (prefixWord ++ tailWord_94773).sum := by decide
  have hdescent : baseEnd_94773 < baseStart_94773 := by decide
  rcases family_descends (prefixWord ++ tailWord_94773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94790 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_94790 : Nat := 118140960795 + 94790 * 2 ^ 59
def prefixEnd_94790 : Nat := 4983230072969 + 3 ^ 40 * 94790 * 2
def baseEnd_94790 : Nat := 43264738879812771012511

theorem tailTrace_94790 : CollatzResearch.WordTrace tailWord_94790 prefixEnd_94790 43264738879812771012511 := by
  unfold tailWord_94790
  simp only [CollatzResearch.WordTrace]
  refine ⟨108039853956234177757807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2304850217732995792166549 108039853956234177757807)
  ·
    refine ⟨162059780934351266636711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108039853956234177757807 162059780934351266636711)
    ·
      refine ⟨243089671401526899955067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162059780934351266636711 243089671401526899955067)
      ·
        refine ⟨364634507102290349932601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243089671401526899955067 364634507102290349932601)
        ·
          refine ⟨273475880326717762449451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364634507102290349932601 273475880326717762449451)
          ·
            refine ⟨410213820490076643674177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273475880326717762449451 410213820490076643674177)
            ·
              refine ⟨307660365367557482755633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410213820490076643674177 307660365367557482755633)
              ·
                refine ⟨230745274025668112066725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307660365367557482755633 230745274025668112066725)
                ·
                  refine ⟨43264738879812771012511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230745274025668112066725 43264738879812771012511)
                  ·
                    rfl

theorem cell20_94790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_94790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94790 prefixEnd_94790 := by exact prefixLift 94790
  have htrace : WordTrace (prefixWord ++ tailWord_94790) baseStart_94790 baseEnd_94790 := by
    simpa [prefixWord, tailWord_94790, baseEnd_94790] using wordTrace_append hprefix tailTrace_94790
  have hstable : (prefixWord ++ tailWord_94790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94790).length < 2 ^ (prefixWord ++ tailWord_94790).sum := by decide
  have hdescent : baseEnd_94790 < baseStart_94790 := by decide
  rcases family_descends (prefixWord ++ tailWord_94790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94794 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_94794 : Nat := 118140960795 + 94794 * 2 ^ 59
def prefixEnd_94794 : Nat := 4983230072969 + 3 ^ 40 * 94794 * 2
def baseEnd_94794 : Nat := 43266564588806534879161

theorem tailTrace_94794 : CollatzResearch.WordTrace tailWord_94794 prefixEnd_94794 43266564588806534879161 := by
  unfold tailWord_94794
  simp only [CollatzResearch.WordTrace]
  refine ⟨864355304646250592848859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2304947479056668247596957 864355304646250592848859)
  ·
    refine ⟨1296532956969375889273289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864355304646250592848859 1296532956969375889273289)
    ·
      refine ⟨972399717727031916954967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1296532956969375889273289 972399717727031916954967)
      ·
        refine ⟨1458599576590547875432451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972399717727031916954967 1458599576590547875432451)
        ·
          refine ⟨2187899364885821813148677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458599576590547875432451 2187899364885821813148677)
          ·
            refine ⟨410231130916091589965377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2187899364885821813148677 410231130916091589965377)
            ·
              refine ⟨307673348187068692474033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410231130916091589965377 307673348187068692474033)
              ·
                refine ⟨230755011140301519355525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307673348187068692474033 230755011140301519355525)
                ·
                  refine ⟨43266564588806534879161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230755011140301519355525 43266564588806534879161)
                  ·
                    rfl

theorem cell20_94794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_94794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94794 prefixEnd_94794 := by exact prefixLift 94794
  have htrace : WordTrace (prefixWord ++ tailWord_94794) baseStart_94794 baseEnd_94794 := by
    simpa [prefixWord, tailWord_94794, baseEnd_94794] using wordTrace_append hprefix tailTrace_94794
  have hstable : (prefixWord ++ tailWord_94794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94794).length < 2 ^ (prefixWord ++ tailWord_94794).sum := by decide
  have hdescent : baseEnd_94794 < baseStart_94794 := by decide
  rcases family_descends (prefixWord ++ tailWord_94794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94797 : List Nat := [1, 6, 1, 1, 2, 1, 4, 4]
def baseStart_94797 : Nat := 118140960795 + 94797 * 2 ^ 59
def prefixEnd_94797 : Nat := 4983230072969 + 3 ^ 40 * 94797 * 2
def baseEnd_94797 : Nat := 14422644623517285926383

theorem tailTrace_94797 : CollatzResearch.WordTrace tailWord_94797 prefixEnd_94797 14422644623517285926383 := by
  unfold tailWord_94797
  simp only [CollatzResearch.WordTrace]
  refine ⟨3457530637574133883754645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2305020425049422589169763 3457530637574133883754645)
  ·
    refine ⟨162071748636287525800999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3457530637574133883754645 162071748636287525800999)
    ·
      refine ⟨243107622954431288701499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162071748636287525800999 243107622954431288701499)
      ·
        refine ⟨364661434431646933052249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243107622954431288701499 364661434431646933052249)
        ·
          refine ⟨273496075823735199789187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364661434431646933052249 273496075823735199789187)
          ·
            refine ⟨410244113735602799683781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273496075823735199789187 410244113735602799683781)
            ·
              refine ⟨76920771325425524940709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 410244113735602799683781 76920771325425524940709)
              ·
                refine ⟨14422644623517285926383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76920771325425524940709 14422644623517285926383)
                ·
                  rfl

theorem cell20_94797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_94797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94797 prefixEnd_94797 := by exact prefixLift 94797
  have htrace : WordTrace (prefixWord ++ tailWord_94797) baseStart_94797 baseEnd_94797 := by
    simpa [prefixWord, tailWord_94797, baseEnd_94797] using wordTrace_append hprefix tailTrace_94797
  have hstable : (prefixWord ++ tailWord_94797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94797).length < 2 ^ (prefixWord ++ tailWord_94797).sum := by decide
  have hdescent : baseEnd_94797 < baseStart_94797 := by decide
  rcases family_descends (prefixWord ++ tailWord_94797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94801 : List Nat := [1, 2, 2, 1, 3, 4, 1, 6]
def baseStart_94801 : Nat := 118140960795 + 94801 * 2 ^ 59
def prefixEnd_94801 : Nat := 4983230072969 + 3 ^ 40 * 94801 * 2
def baseEnd_94801 : Nat := 14423253193181873881933

theorem tailTrace_94801 : CollatzResearch.WordTrace tailWord_94801 prefixEnd_94801 14423253193181873881933 := by
  unfold tailWord_94801
  simp only [CollatzResearch.WordTrace]
  refine ⟨3457676529559642566900257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2305117686373095044600171 3457676529559642566900257)
  ·
    refine ⟨2593257397169731925175193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3457676529559642566900257 2593257397169731925175193)
    ·
      refine ⟨1944943047877298943881395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2593257397169731925175193 1944943047877298943881395)
      ·
        refine ⟨2917414571815948415822093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944943047877298943881395 2917414571815948415822093)
        ·
          refine ⟨1094030464430980655933285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2917414571815948415822093 1094030464430980655933285)
          ·
            refine ⟨205130712080808872987491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1094030464430980655933285 205130712080808872987491)
            ·
              refine ⟨307696068121213309481237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205130712080808872987491 307696068121213309481237)
              ·
                refine ⟨14423253193181873881933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 307696068121213309481237 14423253193181873881933)
                ·
                  rfl

theorem cell20_94801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_94801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94801 prefixEnd_94801 := by exact prefixLift 94801
  have htrace : WordTrace (prefixWord ++ tailWord_94801) baseStart_94801 baseEnd_94801 := by
    simpa [prefixWord, tailWord_94801, baseEnd_94801] using wordTrace_append hprefix tailTrace_94801
  have hstable : (prefixWord ++ tailWord_94801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94801).length < 2 ^ (prefixWord ++ tailWord_94801).sum := by decide
  have hdescent : baseEnd_94801 < baseStart_94801 := by decide
  rcases family_descends (prefixWord ++ tailWord_94801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94808 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_94808 : Nat := 118140960795 + 94808 * 2 ^ 59
def prefixEnd_94808 : Nat := 4983230072969 + 3 ^ 40 * 94808 * 2
def baseEnd_94808 : Nat := 43272954570284708412437

theorem tailTrace_94808 : CollatzResearch.WordTrace tailWord_94808 prefixEnd_94808 43272954570284708412437 := by
  unfold tailWord_94808
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728965920267141381202539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2305287893689521841603385 1728965920267141381202539)
  ·
    refine ⟨2593448880400712071803809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1728965920267141381202539 2593448880400712071803809)
    ·
      refine ⟨1945086660300534053852857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2593448880400712071803809 1945086660300534053852857)
      ·
        refine ⟨1458814995225400540389643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1945086660300534053852857 1458814995225400540389643)
        ·
          refine ⟨2188222492838100810584465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458814995225400540389643 2188222492838100810584465)
          ·
            refine ⟨1641166869628575607938349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188222492838100810584465 1641166869628575607938349)
            ·
              refine ⟨615437576110715852976881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1641166869628575607938349 615437576110715852976881)
              ·
                refine ⟨461578182083036889732661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615437576110715852976881 461578182083036889732661)
                ·
                  refine ⟨43272954570284708412437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 461578182083036889732661 43272954570284708412437)
                  ·
                    rfl

theorem cell20_94808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_94808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94808 prefixEnd_94808 := by exact prefixLift 94808
  have htrace : WordTrace (prefixWord ++ tailWord_94808) baseStart_94808 baseEnd_94808 := by
    simpa [prefixWord, tailWord_94808, baseEnd_94808] using wordTrace_append hprefix tailTrace_94808
  have hstable : (prefixWord ++ tailWord_94808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94808).length < 2 ^ (prefixWord ++ tailWord_94808).sum := by decide
  have hdescent : baseEnd_94808 < baseStart_94808 := by decide
  rcases family_descends (prefixWord ++ tailWord_94808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94815 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_94815 : Nat := 118140960795 + 94815 * 2 ^ 59
def prefixEnd_94815 : Nat := 4983230072969 + 3 ^ 40 * 94815 * 2
def baseEnd_94815 : Nat := 43276149561023795179075

theorem tailTrace_94815 : CollatzResearch.WordTrace tailWord_94815 prefixEnd_94815 43276149561023795179075 := by
  unfold tailWord_94815
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458187151508922957909899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2305458101005948638606599 3458187151508922957909899)
  ·
    refine ⟨5187280727263384436864849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3458187151508922957909899 5187280727263384436864849)
    ·
      refine ⟨3890460545447538327648637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5187280727263384436864849 3890460545447538327648637)
      ·
        refine ⟨1458922704542826872868239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3890460545447538327648637 1458922704542826872868239)
        ·
          refine ⟨2188384056814240309302359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458922704542826872868239 2188384056814240309302359)
          ·
            refine ⟨3282576085221360463953539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188384056814240309302359 3282576085221360463953539)
            ·
              refine ⟨4923864127832040695930309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282576085221360463953539 4923864127832040695930309)
              ·
                refine ⟨923224523968507630486933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4923864127832040695930309 923224523968507630486933)
                ·
                  refine ⟨43276149561023795179075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 923224523968507630486933 43276149561023795179075)
                  ·
                    rfl

theorem cell20_94815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_94815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94815 prefixEnd_94815 := by exact prefixLift 94815
  have htrace : WordTrace (prefixWord ++ tailWord_94815) baseStart_94815 baseEnd_94815 := by
    simpa [prefixWord, tailWord_94815, baseEnd_94815] using wordTrace_append hprefix tailTrace_94815
  have hstable : (prefixWord ++ tailWord_94815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94815).length < 2 ^ (prefixWord ++ tailWord_94815).sum := by decide
  have hdescent : baseEnd_94815 < baseStart_94815 := by decide
  rcases family_descends (prefixWord ++ tailWord_94815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94838 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_94838 : Nat := 118140960795 + 94838 * 2 ^ 59
def prefixEnd_94838 : Nat := 4983230072969 + 3 ^ 40 * 94838 * 2
def baseEnd_94838 : Nat := 43286647387737937412315

theorem tailTrace_94838 : CollatzResearch.WordTrace tailWord_94838 prefixEnd_94838 43286647387737937412315 := by
  unfold tailWord_94838
  simp only [CollatzResearch.WordTrace]
  refine ⟨216189126901599867874823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2306017353617065257331445 216189126901599867874823)
  ·
    refine ⟨324283690352399801812235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216189126901599867874823 324283690352399801812235)
    ·
      refine ⟨486425535528599702718353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324283690352399801812235 486425535528599702718353)
      ·
        refine ⟨364819151646449777038765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486425535528599702718353 364819151646449777038765)
        ·
          refine ⟨136807181867418666389537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364819151646449777038765 136807181867418666389537)
          ·
            refine ⟨102605386400563999792153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136807181867418666389537 102605386400563999792153)
            ·
              refine ⟨76954039800422999844115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102605386400563999792153 76954039800422999844115)
              ·
                refine ⟨115431059700634499766173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76954039800422999844115 115431059700634499766173)
                ·
                  refine ⟨43286647387737937412315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115431059700634499766173 43286647387737937412315)
                  ·
                    rfl

theorem cell20_94838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_94838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94838 prefixEnd_94838 := by exact prefixLift 94838
  have htrace : WordTrace (prefixWord ++ tailWord_94838) baseStart_94838 baseEnd_94838 := by
    simpa [prefixWord, tailWord_94838, baseEnd_94838] using wordTrace_append hprefix tailTrace_94838
  have hstable : (prefixWord ++ tailWord_94838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94838).length < 2 ^ (prefixWord ++ tailWord_94838).sum := by decide
  have hdescent : baseEnd_94838 < baseStart_94838 := by decide
  rcases family_descends (prefixWord ++ tailWord_94838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94880 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_94880 : Nat := 118140960795 + 94880 * 2 ^ 59
def prefixEnd_94880 : Nat := 4983230072969 + 3 ^ 40 * 94880 * 2
def baseEnd_94880 : Nat := 43305817332172458012143

theorem tailTrace_94880 : CollatzResearch.WordTrace tailWord_94880 prefixEnd_94880 43305817332172458012143 := by
  unfold tailWord_94880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730278948136719529513047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2307038597515626039350729 1730278948136719529513047)
  ·
    refine ⟨2595418422205079294269571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1730278948136719529513047 2595418422205079294269571)
    ·
      refine ⟨3893127633307618941404357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595418422205079294269571 3893127633307618941404357)
      ·
        refine ⟨729961431245178551513317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3893127633307618941404357 729961431245178551513317)
        ·
          refine ⟨136867768358470978408747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 729961431245178551513317 136867768358470978408747)
          ·
            refine ⟨205301652537706467613121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136867768358470978408747 205301652537706467613121)
            ·
              refine ⟨153976239403279850709841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205301652537706467613121 153976239403279850709841)
              ·
                refine ⟨115482179552459888032381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153976239403279850709841 115482179552459888032381)
                ·
                  refine ⟨43305817332172458012143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115482179552459888032381 43305817332172458012143)
                  ·
                    rfl

theorem cell20_94880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_94880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94880 prefixEnd_94880 := by exact prefixLift 94880
  have htrace : WordTrace (prefixWord ++ tailWord_94880) baseStart_94880 baseEnd_94880 := by
    simpa [prefixWord, tailWord_94880, baseEnd_94880] using wordTrace_append hprefix tailTrace_94880
  have hstable : (prefixWord ++ tailWord_94880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94880).length < 2 ^ (prefixWord ++ tailWord_94880).sum := by decide
  have hdescent : baseEnd_94880 < baseStart_94880 := by decide
  rcases family_descends (prefixWord ++ tailWord_94880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94890 : List Nat := [3, 1, 5, 2, 1, 2, 1, 5]
def baseStart_94890 : Nat := 118140960795 + 94890 * 2 ^ 59
def prefixEnd_94890 : Nat := 4983230072969 + 3 ^ 40 * 94890 * 2
def baseEnd_94890 : Nat := 14436793868218955892923

theorem tailTrace_94890 : CollatzResearch.WordTrace tailWord_94890 prefixEnd_94890 14436793868218955892923 := by
  unfold tailWord_94890
  simp only [CollatzResearch.WordTrace]
  refine ⟨865230656559302691722531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2307281750824807177926749 865230656559302691722531)
  ·
    refine ⟨1297845984838954037583797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 865230656559302691722531 1297845984838954037583797)
    ·
      refine ⟨121673061078651941023481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1297845984838954037583797 121673061078651941023481)
      ·
        refine ⟨91254795808988955767611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121673061078651941023481 91254795808988955767611)
        ·
          refine ⟨136882193713483433651417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91254795808988955767611 136882193713483433651417)
          ·
            refine ⟨102661645285112575238563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136882193713483433651417 102661645285112575238563)
            ·
              refine ⟨153992467927668862857845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102661645285112575238563 153992467927668862857845)
              ·
                refine ⟨14436793868218955892923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153992467927668862857845 14436793868218955892923)
                ·
                  rfl

theorem cell20_94890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_94890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94890 prefixEnd_94890 := by exact prefixLift 94890
  have htrace : WordTrace (prefixWord ++ tailWord_94890) baseStart_94890 baseEnd_94890 := by
    simpa [prefixWord, tailWord_94890, baseEnd_94890] using wordTrace_append hprefix tailTrace_94890
  have hstable : (prefixWord ++ tailWord_94890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94890).length < 2 ^ (prefixWord ++ tailWord_94890).sum := by decide
  have hdescent : baseEnd_94890 < baseStart_94890 := by decide
  rcases family_descends (prefixWord ++ tailWord_94890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94908 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_94908 : Nat := 118140960795 + 94908 * 2 ^ 59
def prefixEnd_94908 : Nat := 4983230072969 + 3 ^ 40 * 94908 * 2
def baseEnd_94908 : Nat := 43318597295128805078695

theorem tailTrace_94908 : CollatzResearch.WordTrace tailWord_94908 prefixEnd_94908 43318597295128805078695 := by
  unfold tailWord_94908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730789570085999920522689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2307719426781333227363585 1730789570085999920522689)
  ·
    refine ⟨1298092177564499940392017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1730789570085999920522689 1298092177564499940392017)
    ·
      refine ⟨973569133173374955294013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1298092177564499940392017 973569133173374955294013)
      ·
        refine ⟨365088424940015608235255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 973569133173374955294013 365088424940015608235255)
        ·
          refine ⟨547632637410023412352883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365088424940015608235255 547632637410023412352883)
          ·
            refine ⟨821448956115035118529325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547632637410023412352883 821448956115035118529325)
            ·
              refine ⟨308043358543138169448497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 821448956115035118529325 308043358543138169448497)
              ·
                refine ⟨231032518907353627086373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308043358543138169448497 231032518907353627086373)
                ·
                  refine ⟨43318597295128805078695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231032518907353627086373 43318597295128805078695)
                  ·
                    rfl

theorem cell20_94908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_94908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94908 prefixEnd_94908 := by exact prefixLift 94908
  have htrace : WordTrace (prefixWord ++ tailWord_94908) baseStart_94908 baseEnd_94908 := by
    simpa [prefixWord, tailWord_94908, baseEnd_94908] using wordTrace_append hprefix tailTrace_94908
  have hstable : (prefixWord ++ tailWord_94908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94908).length < 2 ^ (prefixWord ++ tailWord_94908).sum := by decide
  have hdescent : baseEnd_94908 < baseStart_94908 := by decide
  rcases family_descends (prefixWord ++ tailWord_94908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94929 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_94929 : Nat := 118140960795 + 94929 * 2 ^ 59
def prefixEnd_94929 : Nat := 4983230072969 + 3 ^ 40 * 94929 * 2
def baseEnd_94929 : Nat := 43328182267346065378609

theorem tailTrace_94929 : CollatzResearch.WordTrace tailWord_94929 prefixEnd_94929 43328182267346065378609 := by
  unfold tailWord_94929
  simp only [CollatzResearch.WordTrace]
  refine ⟨3462345073095920427559841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2308230048730613618373227 3462345073095920427559841)
  ·
    refine ⟨2596758804821940320669881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3462345073095920427559841 2596758804821940320669881)
    ·
      refine ⟨1947569103616455240502411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2596758804821940320669881 1947569103616455240502411)
      ·
        refine ⟨2921353655424682860753617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947569103616455240502411 2921353655424682860753617)
        ·
          refine ⟨2191015241568512145565213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921353655424682860753617 2191015241568512145565213)
          ·
            refine ⟨821630715588192054586955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2191015241568512145565213 821630715588192054586955)
            ·
              refine ⟨1232446073382288081880433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821630715588192054586955 1232446073382288081880433)
              ·
                refine ⟨924334555036716061410325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232446073382288081880433 924334555036716061410325)
                ·
                  refine ⟨43328182267346065378609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 924334555036716061410325 43328182267346065378609)
                  ·
                    rfl

theorem cell20_94929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_94929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94929 prefixEnd_94929 := by exact prefixLift 94929
  have htrace : WordTrace (prefixWord ++ tailWord_94929) baseStart_94929 baseEnd_94929 := by
    simpa [prefixWord, tailWord_94929, baseEnd_94929] using wordTrace_append hprefix tailTrace_94929
  have hstable : (prefixWord ++ tailWord_94929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94929).length < 2 ^ (prefixWord ++ tailWord_94929).sum := by decide
  have hdescent : baseEnd_94929 < baseStart_94929 := by decide
  rcases family_descends (prefixWord ++ tailWord_94929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94932 : List Nat := [2, 4, 1, 3, 2, 1, 7]
def baseStart_94932 : Nat := 118140960795 + 94932 * 2 ^ 59
def prefixEnd_94932 : Nat := 4983230072969 + 3 ^ 40 * 94932 * 2
def baseEnd_94932 : Nat := 4814394616565709808733

theorem tailTrace_94932 : CollatzResearch.WordTrace tailWord_94932 prefixEnd_94932 4814394616565709808733 := by
  unfold tailWord_94932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731227246042525969959525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2308302994723367959946033 1731227246042525969959525)
  ·
    refine ⟨324605108632973619367411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1731227246042525969959525 324605108632973619367411)
    ·
      refine ⟨486907662949460429051117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324605108632973619367411 486907662949460429051117)
      ·
        refine ⟨182590373606047660894169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 486907662949460429051117 182590373606047660894169)
        ·
          refine ⟨136942780204535745670627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182590373606047660894169 136942780204535745670627)
          ·
            refine ⟨205414170306803618505941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136942780204535745670627 205414170306803618505941)
            ·
              refine ⟨4814394616565709808733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 205414170306803618505941 4814394616565709808733)
              ·
                rfl

theorem cell20_94932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 7].length) (baseStart_94932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_94932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_94932 prefixEnd_94932 := by exact prefixLift 94932
  have htrace : WordTrace (prefixWord ++ tailWord_94932) baseStart_94932 baseEnd_94932 := by
    simpa [prefixWord, tailWord_94932, baseEnd_94932] using wordTrace_append hprefix tailTrace_94932
  have hstable : (prefixWord ++ tailWord_94932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94932).length < 2 ^ (prefixWord ++ tailWord_94932).sum := by decide
  have hdescent : baseEnd_94932 < baseStart_94932 := by decide
  rcases family_descends (prefixWord ++ tailWord_94932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95029 : List Nat := [1, 3, 3, 1, 3, 1, 2, 6]
def baseStart_95029 : Nat := 118140960795 + 95029 * 2 ^ 59
def prefixEnd_95029 : Nat := 4983230072969 + 3 ^ 40 * 95029 * 2
def baseEnd_95029 : Nat := 14457941664063387348289

theorem tailTrace_95029 : CollatzResearch.WordTrace tailWord_95029 prefixEnd_95029 14457941664063387348289 := by
  unfold tailWord_95029
  simp only [CollatzResearch.WordTrace]
  refine ⟨3465992372733637506200141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2310661581822425004133427 3465992372733637506200141)
  ·
    refine ⟨1299747139775114064825053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3465992372733637506200141 1299747139775114064825053)
    ·
      refine ⟨487405177415667774309395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1299747139775114064825053 487405177415667774309395)
      ·
        refine ⟨731107766123501661464093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487405177415667774309395 731107766123501661464093)
        ·
          refine ⟨274165412296313123049035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 731107766123501661464093 274165412296313123049035)
          ·
            refine ⟨411248118444469684573553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274165412296313123049035 411248118444469684573553)
            ·
              refine ⟨308436088833352263430165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411248118444469684573553 308436088833352263430165)
              ·
                refine ⟨14457941664063387348289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 308436088833352263430165 14457941664063387348289)
                ·
                  rfl

theorem cell20_95029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_95029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95029 prefixEnd_95029 := by exact prefixLift 95029
  have htrace : WordTrace (prefixWord ++ tailWord_95029) baseStart_95029 baseEnd_95029 := by
    simpa [prefixWord, tailWord_95029, baseEnd_95029] using wordTrace_append hprefix tailTrace_95029
  have hstable : (prefixWord ++ tailWord_95029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95029).length < 2 ^ (prefixWord ++ tailWord_95029).sum := by decide
  have hdescent : baseEnd_95029 < baseStart_95029 := by decide
  rcases family_descends (prefixWord ++ tailWord_95029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95046 : List Nat := [6, 1, 1, 2, 10]
def baseStart_95046 : Nat := 118140960795 + 95046 * 2 ^ 59
def prefixEnd_95046 : Nat := 4983230072969 + 3 ^ 40 * 95046 * 2
def baseEnd_95046 : Nat := 535575114264366154051

theorem tailTrace_95046 : CollatzResearch.WordTrace tailWord_95046 prefixEnd_95046 535575114264366154051 := by
  unfold tailWord_95046
  simp only [CollatzResearch.WordTrace]
  refine ⟨108331637927251544049031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2311074942448032939712661 108331637927251544049031)
  ·
    refine ⟨162497456890877316073547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108331637927251544049031 162497456890877316073547)
    ·
      refine ⟨243746185336315974110321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162497456890877316073547 243746185336315974110321)
      ·
        refine ⟨182809639002236980582741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243746185336315974110321 182809639002236980582741)
        ·
          refine ⟨535575114264366154051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 182809639002236980582741 535575114264366154051)
          ·
            rfl

theorem cell20_95046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 10].length) (baseStart_95046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95046 prefixEnd_95046 := by exact prefixLift 95046
  have htrace : WordTrace (prefixWord ++ tailWord_95046) baseStart_95046 baseEnd_95046 := by
    simpa [prefixWord, tailWord_95046, baseEnd_95046] using wordTrace_append hprefix tailTrace_95046
  have hstable : (prefixWord ++ tailWord_95046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95046).length < 2 ^ (prefixWord ++ tailWord_95046).sum := by decide
  have hdescent : baseEnd_95046 < baseStart_95046 := by decide
  rcases family_descends (prefixWord ++ tailWord_95046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95088 : List Nat := [2, 1, 1, 1, 4, 1, 2, 8]
def baseStart_95088 : Nat := 118140960795 + 95088 * 2 ^ 59
def prefixEnd_95088 : Nat := 4983230072969 + 3 ^ 40 * 95088 * 2
def baseEnd_95088 : Nat := 14466918066616059692653

theorem tailTrace_95088 : CollatzResearch.WordTrace tailWord_95088 prefixEnd_95088 14466918066616059692653 := by
  unfold tailWord_95088
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734072139759945291298959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2312096186346593721731945 1734072139759945291298959)
  ·
    refine ⟨2601108209639917936948439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1734072139759945291298959 2601108209639917936948439)
    ·
      refine ⟨3901662314459876905422659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2601108209639917936948439 3901662314459876905422659)
      ·
        refine ⟨5852493471689815358133989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901662314459876905422659 5852493471689815358133989)
        ·
          refine ⟨1097342525941840379650123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5852493471689815358133989 1097342525941840379650123)
          ·
            refine ⟨1646013788912760569475185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097342525941840379650123 1646013788912760569475185)
            ·
              refine ⟨1234510341684570427106389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646013788912760569475185 1234510341684570427106389)
              ·
                refine ⟨14466918066616059692653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1234510341684570427106389 14466918066616059692653)
                ·
                  rfl

theorem cell20_95088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_95088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95088 prefixEnd_95088 := by exact prefixLift 95088
  have htrace : WordTrace (prefixWord ++ tailWord_95088) baseStart_95088 baseEnd_95088 := by
    simpa [prefixWord, tailWord_95088, baseEnd_95088] using wordTrace_append hprefix tailTrace_95088
  have hstable : (prefixWord ++ tailWord_95088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95088).length < 2 ^ (prefixWord ++ tailWord_95088).sum := by decide
  have hdescent : baseEnd_95088 < baseStart_95088 := by decide
  rcases family_descends (prefixWord ++ tailWord_95088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95094 : List Nat := [5, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_95094 : Nat := 118140960795 + 95094 * 2 ^ 59
def prefixEnd_95094 : Nat := 4983230072969 + 3 ^ 40 * 95094 * 2
def baseEnd_95094 : Nat := 43403492763338824877935

theorem tailTrace_95094 : CollatzResearch.WordTrace tailWord_95094 prefixEnd_95094 43403492763338824877935 := by
  unfold tailWord_95094
  simp only [CollatzResearch.WordTrace]
  refine ⟨216772694843634600457271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2312242078332102404877557 216772694843634600457271)
  ·
    refine ⟨325159042265451900685907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216772694843634600457271 325159042265451900685907)
    ·
      refine ⟨487738563398177851028861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325159042265451900685907 487738563398177851028861)
      ·
        refine ⟨182901961274316694135823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487738563398177851028861 182901961274316694135823)
        ·
          refine ⟨274352941911475041203735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182901961274316694135823 274352941911475041203735)
          ·
            refine ⟨411529412867212561805603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274352941911475041203735 411529412867212561805603)
            ·
              refine ⟨617294119300818842708405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411529412867212561805603 617294119300818842708405)
              ·
                refine ⟨57871323684451766503913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617294119300818842708405 57871323684451766503913)
                ·
                  refine ⟨43403492763338824877935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57871323684451766503913 43403492763338824877935)
                  ·
                    rfl

theorem cell20_95094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_95094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95094 prefixEnd_95094 := by exact prefixLift 95094
  have htrace : WordTrace (prefixWord ++ tailWord_95094) baseStart_95094 baseEnd_95094 := by
    simpa [prefixWord, tailWord_95094, baseEnd_95094] using wordTrace_append hprefix tailTrace_95094
  have hstable : (prefixWord ++ tailWord_95094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95094).length < 2 ^ (prefixWord ++ tailWord_95094).sum := by decide
  have hdescent : baseEnd_95094 < baseStart_95094 := by decide
  rcases family_descends (prefixWord ++ tailWord_95094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95221 : List Nat := [1, 3, 5, 2, 2, 1, 2, 2, 2]
def baseStart_95221 : Nat := 118140960795 + 95221 * 2 ^ 59
def prefixEnd_95221 : Nat := 4983230072969 + 3 ^ 40 * 95221 * 2
def baseEnd_95221 : Nat := 43461459023890827644083

theorem tailTrace_95221 : CollatzResearch.WordTrace tailWord_95221 prefixEnd_95221 43461459023890827644083 := by
  unfold tailWord_95221
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472995188038054297189517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2315330125358702864793011 3472995188038054297189517)
  ·
    refine ⟨1302373195514270361446069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3472995188038054297189517 1302373195514270361446069)
    ·
      refine ⟨122097487079462846385569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1302373195514270361446069 122097487079462846385569)
      ·
        refine ⟨91573115309597134789177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122097487079462846385569 91573115309597134789177)
        ·
          refine ⟨68679836482197851091883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91573115309597134789177 68679836482197851091883)
          ·
            refine ⟨103019754723296776637825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68679836482197851091883 103019754723296776637825)
            ·
              refine ⟨77264816042472582478369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103019754723296776637825 77264816042472582478369)
              ·
                refine ⟨57948612031854436858777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77264816042472582478369 57948612031854436858777)
                ·
                  refine ⟨43461459023890827644083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57948612031854436858777 43461459023890827644083)
                  ·
                    rfl

theorem cell20_95221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_95221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95221 prefixEnd_95221 := by exact prefixLift 95221
  have htrace : WordTrace (prefixWord ++ tailWord_95221) baseStart_95221 baseEnd_95221 := by
    simpa [prefixWord, tailWord_95221, baseEnd_95221] using wordTrace_append hprefix tailTrace_95221
  have hstable : (prefixWord ++ tailWord_95221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95221).length < 2 ^ (prefixWord ++ tailWord_95221).sum := by decide
  have hdescent : baseEnd_95221 < baseStart_95221 := by decide
  rcases family_descends (prefixWord ++ tailWord_95221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95222 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_95222 : Nat := 118140960795 + 95222 * 2 ^ 59
def prefixEnd_95222 : Nat := 4983230072969 + 3 ^ 40 * 95222 * 2
def baseEnd_95222 : Nat := 43461915451139268610745

theorem tailTrace_95222 : CollatzResearch.WordTrace tailWord_95222 prefixEnd_95222 43461915451139268610745 := by
  unfold tailWord_95222
  simp only [CollatzResearch.WordTrace]
  refine ⟨217064478814651966748495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2315354440689620978650613 217064478814651966748495)
  ·
    refine ⟨325596718221977950122743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217064478814651966748495 325596718221977950122743)
    ·
      refine ⟨488395077332966925184115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325596718221977950122743 488395077332966925184115)
      ·
        refine ⟨732592615999450387776173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488395077332966925184115 732592615999450387776173)
        ·
          refine ⟨274722230999793895416065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732592615999450387776173 274722230999793895416065)
          ·
            refine ⟨206041673249845421562049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274722230999793895416065 206041673249845421562049)
            ·
              refine ⟨154531254937384066171537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206041673249845421562049 154531254937384066171537)
              ·
                refine ⟨115898441203038049628653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154531254937384066171537 115898441203038049628653)
                ·
                  refine ⟨43461915451139268610745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115898441203038049628653 43461915451139268610745)
                  ·
                    rfl

theorem cell20_95222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_95222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95222 prefixEnd_95222 := by exact prefixLift 95222
  have htrace : WordTrace (prefixWord ++ tailWord_95222) baseStart_95222 baseEnd_95222 := by
    simpa [prefixWord, tailWord_95222, baseEnd_95222] using wordTrace_append hprefix tailTrace_95222
  have hstable : (prefixWord ++ tailWord_95222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95222).length < 2 ^ (prefixWord ++ tailWord_95222).sum := by decide
  have hdescent : baseEnd_95222 < baseStart_95222 := by decide
  rcases family_descends (prefixWord ++ tailWord_95222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95267 : List Nat := [1, 1, 1, 4, 3, 3, 2, 3, 2]
def baseStart_95267 : Nat := 118140960795 + 95267 * 2 ^ 59
def prefixEnd_95267 : Nat := 4983230072969 + 3 ^ 40 * 95267 * 2
def baseEnd_95267 : Nat := 43482454677319112110561

theorem tailTrace_95267 : CollatzResearch.WordTrace tailWord_95267 prefixEnd_95267 43482454677319112110561 := by
  unfold tailWord_95267
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474672945871404153364055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2316448630580936102242703 3474672945871404153364055)
  ·
    refine ⟨5212009418807106230046083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3474672945871404153364055 5212009418807106230046083)
    ·
      refine ⟨7818014128210659345069125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5212009418807106230046083 7818014128210659345069125)
      ·
        refine ⟨1465877649039498627200461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7818014128210659345069125 1465877649039498627200461)
        ·
          refine ⟨549704118389811985200173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1465877649039498627200461 549704118389811985200173)
          ·
            refine ⟨206139044396179494450065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549704118389811985200173 206139044396179494450065)
            ·
              refine ⟨154604283297134620837549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206139044396179494450065 154604283297134620837549)
              ·
                refine ⟨57976606236425482814081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154604283297134620837549 57976606236425482814081)
                ·
                  refine ⟨43482454677319112110561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57976606236425482814081 43482454677319112110561)
                  ·
                    rfl

theorem cell20_95267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 2].length) (baseStart_95267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95267 prefixEnd_95267 := by exact prefixLift 95267
  have htrace : WordTrace (prefixWord ++ tailWord_95267) baseStart_95267 baseEnd_95267 := by
    simpa [prefixWord, tailWord_95267, baseEnd_95267] using wordTrace_append hprefix tailTrace_95267
  have hstable : (prefixWord ++ tailWord_95267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95267).length < 2 ^ (prefixWord ++ tailWord_95267).sum := by decide
  have hdescent : baseEnd_95267 < baseStart_95267 := by decide
  rcases family_descends (prefixWord ++ tailWord_95267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95284 : List Nat := [2, 5, 1, 2, 1, 1, 2, 4, 2]
def baseStart_95284 : Nat := 118140960795 + 95284 * 2 ^ 59
def prefixEnd_95284 : Nat := 4983230072969 + 3 ^ 40 * 95284 * 2
def baseEnd_95284 : Nat := 43490213940542608543825

theorem tailTrace_95284 : CollatzResearch.WordTrace tailWord_95284 prefixEnd_95284 43490213940542608543825 := by
  unfold tailWord_95284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737646493404908028366453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2316861991206544037821937 1737646493404908028366453)
  ·
    refine ⟨162904358756710127659355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1737646493404908028366453 162904358756710127659355)
    ·
      refine ⟨244356538135065191489033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162904358756710127659355 244356538135065191489033)
      ·
        refine ⟨183267403601298893616775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244356538135065191489033 183267403601298893616775)
        ·
          refine ⟨274901105401948340425163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183267403601298893616775 274901105401948340425163)
          ·
            refine ⟨412351658102922510637745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274901105401948340425163 412351658102922510637745)
            ·
              refine ⟨309263743577191882978309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412351658102922510637745 309263743577191882978309)
              ·
                refine ⟨57986951920723478058433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 309263743577191882978309 57986951920723478058433)
                ·
                  refine ⟨43490213940542608543825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57986951920723478058433 43490213940542608543825)
                  ·
                    rfl

theorem cell20_95284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_95284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95284 prefixEnd_95284 := by exact prefixLift 95284
  have htrace : WordTrace (prefixWord ++ tailWord_95284) baseStart_95284 baseEnd_95284 := by
    simpa [prefixWord, tailWord_95284, baseEnd_95284] using wordTrace_append hprefix tailTrace_95284
  have hstable : (prefixWord ++ tailWord_95284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95284).length < 2 ^ (prefixWord ++ tailWord_95284).sum := by decide
  have hdescent : baseEnd_95284 < baseStart_95284 := by decide
  rcases family_descends (prefixWord ++ tailWord_95284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95288 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_95288 : Nat := 118140960795 + 95288 * 2 ^ 59
def prefixEnd_95288 : Nat := 4983230072969 + 3 ^ 40 * 95288 * 2
def baseEnd_95288 : Nat := 43492039649536372410475

theorem tailTrace_95288 : CollatzResearch.WordTrace tailWord_95288 prefixEnd_95288 43492039649536372410475 := by
  unfold tailWord_95288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737719439397662369939259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2316959252530216493252345 1737719439397662369939259)
  ·
    refine ⟨2606579159096493554908889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737719439397662369939259 2606579159096493554908889)
    ·
      refine ⟨1954934369322370166181667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2606579159096493554908889 1954934369322370166181667)
      ·
        refine ⟨2932401553983555249272501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954934369322370166181667 2932401553983555249272501)
        ·
          refine ⟨274912645685958304619297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2932401553983555249272501 274912645685958304619297)
          ·
            refine ⟨206184484264468728464473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274912645685958304619297 206184484264468728464473)
            ·
              refine ⟨154638363198351546348355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206184484264468728464473 154638363198351546348355)
              ·
                refine ⟨231957544797527319522533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154638363198351546348355 231957544797527319522533)
                ·
                  refine ⟨43492039649536372410475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231957544797527319522533 43492039649536372410475)
                  ·
                    rfl

theorem cell20_95288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_95288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95288 prefixEnd_95288 := by exact prefixLift 95288
  have htrace : WordTrace (prefixWord ++ tailWord_95288) baseStart_95288 baseEnd_95288 := by
    simpa [prefixWord, tailWord_95288, baseEnd_95288] using wordTrace_append hprefix tailTrace_95288
  have hstable : (prefixWord ++ tailWord_95288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95288).length < 2 ^ (prefixWord ++ tailWord_95288).sum := by decide
  have hdescent : baseEnd_95288 < baseStart_95288 := by decide
  rcases family_descends (prefixWord ++ tailWord_95288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95318 : List Nat := [5, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_95318 : Nat := 118140960795 + 95318 * 2 ^ 59
def prefixEnd_95318 : Nat := 4983230072969 + 3 ^ 40 * 95318 * 2
def baseEnd_95318 : Nat := 43505732466989601410353

theorem tailTrace_95318 : CollatzResearch.WordTrace tailWord_95318 prefixEnd_95318 43505732466989601410353 := by
  unfold tailWord_95318
  simp only [CollatzResearch.WordTrace]
  refine ⟨217283316792914991466913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2317688712457759908980405 217283316792914991466913)
  ·
    refine ⟨162962487594686243600185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217283316792914991466913 162962487594686243600185)
    ·
      refine ⟨122221865696014682700139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162962487594686243600185 122221865696014682700139)
      ·
        refine ⟨183332798544022024050209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122221865696014682700139 183332798544022024050209)
        ·
          refine ⟨137499598908016518037657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183332798544022024050209 137499598908016518037657)
          ·
            refine ⟨103124699181012388528243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137499598908016518037657 103124699181012388528243)
            ·
              refine ⟨154687048771518582792365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103124699181012388528243 154687048771518582792365)
              ·
                refine ⟨58007643289319468547137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154687048771518582792365 58007643289319468547137)
                ·
                  refine ⟨43505732466989601410353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58007643289319468547137 43505732466989601410353)
                  ·
                    rfl

theorem cell20_95318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_95318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95318 prefixEnd_95318 := by exact prefixLift 95318
  have htrace : WordTrace (prefixWord ++ tailWord_95318) baseStart_95318 baseEnd_95318 := by
    simpa [prefixWord, tailWord_95318, baseEnd_95318] using wordTrace_append hprefix tailTrace_95318
  have hstable : (prefixWord ++ tailWord_95318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95318).length < 2 ^ (prefixWord ++ tailWord_95318).sum := by decide
  have hdescent : baseEnd_95318 < baseStart_95318 := by decide
  rcases family_descends (prefixWord ++ tailWord_95318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95340 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_95340 : Nat := 118140960795 + 95340 * 2 ^ 59
def prefixEnd_95340 : Nat := 4983230072969 + 3 ^ 40 * 95340 * 2
def baseEnd_95340 : Nat := 43515773866455302676929

theorem tailTrace_95340 : CollatzResearch.WordTrace tailWord_95340 prefixEnd_95340 43515773866455302676929 := by
  unfold tailWord_95340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738667737303468810385737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2318223649737958413847649 1738667737303468810385737)
  ·
    refine ⟨1304000802977601607789303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1738667737303468810385737 1304000802977601607789303)
    ·
      refine ⟨1956001204466402411683955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1304000802977601607789303 1956001204466402411683955)
      ·
        refine ⟨2934001806699603617525933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956001204466402411683955 2934001806699603617525933)
        ·
          refine ⟨1100250677512351356572225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2934001806699603617525933 1100250677512351356572225)
          ·
            refine ⟨825188008134263517429169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100250677512351356572225 825188008134263517429169)
            ·
              refine ⟨618891006100697638071877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825188008134263517429169 618891006100697638071877)
              ·
                refine ⟨116042063643880807138477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 618891006100697638071877 116042063643880807138477)
                ·
                  refine ⟨43515773866455302676929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116042063643880807138477 43515773866455302676929)
                  ·
                    rfl

theorem cell20_95340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_95340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95340 prefixEnd_95340 := by exact prefixLift 95340
  have htrace : WordTrace (prefixWord ++ tailWord_95340) baseStart_95340 baseEnd_95340 := by
    simpa [prefixWord, tailWord_95340, baseEnd_95340] using wordTrace_append hprefix tailTrace_95340
  have hstable : (prefixWord ++ tailWord_95340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95340).length < 2 ^ (prefixWord ++ tailWord_95340).sum := by decide
  have hdescent : baseEnd_95340 < baseStart_95340 := by decide
  rcases family_descends (prefixWord ++ tailWord_95340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95343 : List Nat := [1, 1, 2, 1, 3, 3, 5, 2, 2]
def baseStart_95343 : Nat := 118140960795 + 95343 * 2 ^ 59
def prefixEnd_95343 : Nat := 4983230072969 + 3 ^ 40 * 95343 * 2
def baseEnd_95343 : Nat := 43517143148200625576917

theorem tailTrace_95343 : CollatzResearch.WordTrace tailWord_95343 prefixEnd_95343 43517143148200625576917 := by
  unfold tailWord_95343
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477444893596069133130683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2318296595730712755420455 3477444893596069133130683)
  ·
    refine ⟨5216167340394103699696025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3477444893596069133130683 5216167340394103699696025)
    ·
      refine ⟨3912125505295577774772019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5216167340394103699696025 3912125505295577774772019)
      ·
        refine ⟨5868188257943366662158029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3912125505295577774772019 5868188257943366662158029)
        ·
          refine ⟨2200570596728762498309261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5868188257943366662158029 2200570596728762498309261)
          ·
            refine ⟨825213973773285936865973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2200570596728762498309261 825213973773285936865973)
            ·
              refine ⟨77363810041245556581185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 825213973773285936865973 77363810041245556581185)
              ·
                refine ⟨58022857530934167435889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77363810041245556581185 58022857530934167435889)
                ·
                  refine ⟨43517143148200625576917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58022857530934167435889 43517143148200625576917)
                  ·
                    rfl

theorem cell20_95343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 2].length) (baseStart_95343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95343 prefixEnd_95343 := by exact prefixLift 95343
  have htrace : WordTrace (prefixWord ++ tailWord_95343) baseStart_95343 baseEnd_95343 := by
    simpa [prefixWord, tailWord_95343, baseEnd_95343] using wordTrace_append hprefix tailTrace_95343
  have hstable : (prefixWord ++ tailWord_95343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95343).length < 2 ^ (prefixWord ++ tailWord_95343).sum := by decide
  have hdescent : baseEnd_95343 < baseStart_95343 := by decide
  rcases family_descends (prefixWord ++ tailWord_95343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95353 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 3]
def baseStart_95353 : Nat := 118140960795 + 95353 * 2 ^ 59
def prefixEnd_95353 : Nat := 4983230072969 + 3 ^ 40 * 95353 * 2
def baseEnd_95353 : Nat := 43521707420685035243543

theorem tailTrace_95353 : CollatzResearch.WordTrace tailWord_95353 prefixEnd_95353 43521707420685035243543 := by
  unfold tailWord_95353
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477809623559840840994713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2318539749039893893996475 3477809623559840840994713)
  ·
    refine ⟨2608357217669880630746035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3477809623559840840994713 2608357217669880630746035)
    ·
      refine ⟨3912535826504820946119053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2608357217669880630746035 3912535826504820946119053)
      ·
        refine ⟨1467200934939307854794645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3912535826504820946119053 1467200934939307854794645)
        ·
          refine ⟨68775043825280055693499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1467200934939307854794645 68775043825280055693499)
          ·
            refine ⟨103162565737920083540249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68775043825280055693499 103162565737920083540249)
            ·
              refine ⟨77371924303440062655187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103162565737920083540249 77371924303440062655187)
              ·
                refine ⟨116057886455160093982781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77371924303440062655187 116057886455160093982781)
                ·
                  refine ⟨43521707420685035243543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116057886455160093982781 43521707420685035243543)
                  ·
                    rfl

theorem cell20_95353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_95353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95353 prefixEnd_95353 := by exact prefixLift 95353
  have htrace : WordTrace (prefixWord ++ tailWord_95353) baseStart_95353 baseEnd_95353 := by
    simpa [prefixWord, tailWord_95353, baseEnd_95353] using wordTrace_append hprefix tailTrace_95353
  have hstable : (prefixWord ++ tailWord_95353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95353).length < 2 ^ (prefixWord ++ tailWord_95353).sum := by decide
  have hdescent : baseEnd_95353 < baseStart_95353 := by decide
  rcases family_descends (prefixWord ++ tailWord_95353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95394 : List Nat := [3, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_95394 : Nat := 118140960795 + 95394 * 2 ^ 59
def prefixEnd_95394 : Nat := 4983230072969 + 3 ^ 40 * 95394 * 2
def baseEnd_95394 : Nat := 43540420937871114876709

theorem tailTrace_95394 : CollatzResearch.WordTrace tailWord_95394 prefixEnd_95394 43540420937871114876709 := by
  unfold tailWord_95394
  simp only [CollatzResearch.WordTrace]
  refine ⟨869826254102826210809309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2319536677607536562158157 869826254102826210809309)
  ·
    refine ⟨326184845288559829053491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 869826254102826210809309 326184845288559829053491)
    ·
      refine ⟨489277267932839743580237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326184845288559829053491 489277267932839743580237)
      ·
        refine ⟨183478975474814903842589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489277267932839743580237 183478975474814903842589)
        ·
          refine ⟨68804615803055588940971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183478975474814903842589 68804615803055588940971)
          ·
            refine ⟨103206923704583383411457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68804615803055588940971 103206923704583383411457)
            ·
              refine ⟨77405192778437537558593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103206923704583383411457 77405192778437537558593)
              ·
                refine ⟨58053894583828153168945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77405192778437537558593 58053894583828153168945)
                ·
                  refine ⟨43540420937871114876709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58053894583828153168945 43540420937871114876709)
                  ·
                    rfl

theorem cell20_95394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_95394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95394 prefixEnd_95394 := by exact prefixLift 95394
  have htrace : WordTrace (prefixWord ++ tailWord_95394) baseStart_95394 baseEnd_95394 := by
    simpa [prefixWord, tailWord_95394, baseEnd_95394] using wordTrace_append hprefix tailTrace_95394
  have hstable : (prefixWord ++ tailWord_95394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95394).length < 2 ^ (prefixWord ++ tailWord_95394).sum := by decide
  have hdescent : baseEnd_95394 < baseStart_95394 := by decide
  rcases family_descends (prefixWord ++ tailWord_95394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95405 : List Nat := [1, 5, 2, 1, 4, 1, 1, 5]
def baseStart_95405 : Nat := 118140960795 + 95405 * 2 ^ 59
def prefixEnd_95405 : Nat := 4983230072969 + 3 ^ 40 * 95405 * 2
def baseEnd_95405 : Nat := 14515147212534655169999

theorem tailTrace_95405 : CollatzResearch.WordTrace tailWord_95405 prefixEnd_95405 14515147212534655169999 := by
  unfold tailWord_95405
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479706219371453721887669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2319804146247635814591779 3479706219371453721887669)
  ·
    refine ⟨326222458066073786426969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3479706219371453721887669 326222458066073786426969)
    ·
      refine ⟨244666843549555339820227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326222458066073786426969 244666843549555339820227)
      ·
        refine ⟨367000265324333009730341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244666843549555339820227 367000265324333009730341)
        ·
          refine ⟨68812549748312439324439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367000265324333009730341 68812549748312439324439)
          ·
            refine ⟨103218824622468658986659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68812549748312439324439 103218824622468658986659)
            ·
              refine ⟨154828236933702988479989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103218824622468658986659 154828236933702988479989)
              ·
                refine ⟨14515147212534655169999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154828236933702988479989 14515147212534655169999)
                ·
                  rfl

theorem cell20_95405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5].length) (baseStart_95405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95405 prefixEnd_95405 := by exact prefixLift 95405
  have htrace : WordTrace (prefixWord ++ tailWord_95405) baseStart_95405 baseEnd_95405 := by
    simpa [prefixWord, tailWord_95405, baseEnd_95405] using wordTrace_append hprefix tailTrace_95405
  have hstable : (prefixWord ++ tailWord_95405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95405).length < 2 ^ (prefixWord ++ tailWord_95405).sum := by decide
  have hdescent : baseEnd_95405 < baseStart_95405 := by decide
  rcases family_descends (prefixWord ++ tailWord_95405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95409 : List Nat := [1, 2, 2, 5, 1, 1, 3, 5]
def baseStart_95409 : Nat := 118140960795 + 95409 * 2 ^ 59
def prefixEnd_95409 : Nat := 4983230072969 + 3 ^ 40 * 95409 * 2
def baseEnd_95409 : Nat := 14515755782199243125549

theorem tailTrace_95409 : CollatzResearch.WordTrace tailWord_95409 prefixEnd_95409 14515755782199243125549 := by
  unfold tailWord_95409
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479852111356962405033281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2319901407571308270022187 3479852111356962405033281)
  ·
    refine ⟨2609889083517721803774961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3479852111356962405033281 2609889083517721803774961)
    ·
      refine ⟨1957416812638291352831221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2609889083517721803774961 1957416812638291352831221)
      ·
        refine ⟨183507826184839814327927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1957416812638291352831221 183507826184839814327927)
        ·
          refine ⟨275261739277259721491891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183507826184839814327927 275261739277259721491891)
          ·
            refine ⟨412892608915889582237837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275261739277259721491891 412892608915889582237837)
            ·
              refine ⟨154834728343458593339189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412892608915889582237837 154834728343458593339189)
              ·
                refine ⟨14515755782199243125549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154834728343458593339189 14515755782199243125549)
                ·
                  rfl

theorem cell20_95409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_95409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95409 prefixEnd_95409 := by exact prefixLift 95409
  have htrace : WordTrace (prefixWord ++ tailWord_95409) baseStart_95409 baseEnd_95409 := by
    simpa [prefixWord, tailWord_95409, baseEnd_95409] using wordTrace_append hprefix tailTrace_95409
  have hstable : (prefixWord ++ tailWord_95409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95409).length < 2 ^ (prefixWord ++ tailWord_95409).sum := by decide
  have hdescent : baseEnd_95409 < baseStart_95409 := by decide
  rcases family_descends (prefixWord ++ tailWord_95409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95446 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_95446 : Nat := 118140960795 + 95446 * 2 ^ 59
def prefixEnd_95446 : Nat := 4983230072969 + 3 ^ 40 * 95446 * 2
def baseEnd_95446 : Nat := 43564155154790045143163

theorem tailTrace_95446 : CollatzResearch.WordTrace tailWord_95446 prefixEnd_95446 43564155154790045143163 := by
  unfold tailWord_95446
  simp only [CollatzResearch.WordTrace]
  refine ⟨217575100763932357758137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2320801074815278482753461 217575100763932357758137)
  ·
    refine ⟨163181325572949268318603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217575100763932357758137 163181325572949268318603)
    ·
      refine ⟨244771988359423902477905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163181325572949268318603 244771988359423902477905)
      ·
        refine ⟨183578991269567926858429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244771988359423902477905 183578991269567926858429)
        ·
          refine ⟨68842121726087972571911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183578991269567926858429 68842121726087972571911)
          ·
            refine ⟨103263182589131958857867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68842121726087972571911 103263182589131958857867)
            ·
              refine ⟨154894773883697938286801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103263182589131958857867 154894773883697938286801)
              ·
                refine ⟨116171080412773453715101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154894773883697938286801 116171080412773453715101)
                ·
                  refine ⟨43564155154790045143163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116171080412773453715101 43564155154790045143163)
                  ·
                    rfl

theorem cell20_95446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_95446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95446 prefixEnd_95446 := by exact prefixLift 95446
  have htrace : WordTrace (prefixWord ++ tailWord_95446) baseStart_95446 baseEnd_95446 := by
    simpa [prefixWord, tailWord_95446, baseEnd_95446] using wordTrace_append hprefix tailTrace_95446
  have hstable : (prefixWord ++ tailWord_95446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95446).length < 2 ^ (prefixWord ++ tailWord_95446).sum := by decide
  have hdescent : baseEnd_95446 < baseStart_95446 := by decide
  rcases family_descends (prefixWord ++ tailWord_95446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95492 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_95492 : Nat := 118140960795 + 95492 * 2 ^ 59
def prefixEnd_95492 : Nat := 4983230072969 + 3 ^ 40 * 95492 * 2
def baseEnd_95492 : Nat := 43585150808218329609641

theorem tailTrace_95492 : CollatzResearch.WordTrace tailWord_95492 prefixEnd_95492 43585150808218329609641 := by
  unfold tailWord_95492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1741439685028133790152365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2321919580037511720203153 1741439685028133790152365)
  ·
    refine ⟨653039881885550171307137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1741439685028133790152365 653039881885550171307137)
    ·
      refine ⟨489779911414162628480353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 653039881885550171307137 489779911414162628480353)
      ·
        refine ⟨367334933560621971360265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489779911414162628480353 367334933560621971360265)
        ·
          refine ⟨275501200170466478520199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367334933560621971360265 275501200170466478520199)
          ·
            refine ⟨413251800255699717780299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275501200170466478520199 413251800255699717780299)
            ·
              refine ⟨619877700383549576670449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413251800255699717780299 619877700383549576670449)
              ·
                refine ⟨464908275287662182502837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619877700383549576670449 464908275287662182502837)
                ·
                  refine ⟨43585150808218329609641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464908275287662182502837 43585150808218329609641)
                  ·
                    rfl

theorem cell20_95492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_95492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95492 prefixEnd_95492 := by exact prefixLift 95492
  have htrace : WordTrace (prefixWord ++ tailWord_95492) baseStart_95492 baseEnd_95492 := by
    simpa [prefixWord, tailWord_95492, baseEnd_95492] using wordTrace_append hprefix tailTrace_95492
  have hstable : (prefixWord ++ tailWord_95492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95492).length < 2 ^ (prefixWord ++ tailWord_95492).sum := by decide
  have hdescent : baseEnd_95492 < baseStart_95492 := by decide
  rcases family_descends (prefixWord ++ tailWord_95492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95516 : List Nat := [2, 2, 3, 1, 1, 1, 2, 6, 2]
def baseStart_95516 : Nat := 118140960795 + 95516 * 2 ^ 59
def prefixEnd_95516 : Nat := 4983230072969 + 3 ^ 40 * 95516 * 2
def baseEnd_95516 : Nat := 43596105062180912809543

theorem tailTrace_95516 : CollatzResearch.WordTrace tailWord_95516 prefixEnd_95516 43596105062180912809543 := by
  unfold tailWord_95516
  simp only [CollatzResearch.WordTrace]
  refine ⟨1741877360984659839589201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2322503147979546452785601 1741877360984659839589201)
  ·
    refine ⟨1306408020738494879691901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1741877360984659839589201 1306408020738494879691901)
    ·
      refine ⟨489903007776935579884463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1306408020738494879691901 489903007776935579884463)
      ·
        refine ⟨734854511665403369826695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489903007776935579884463 734854511665403369826695)
        ·
          refine ⟨1102281767498105054740043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734854511665403369826695 1102281767498105054740043)
          ·
            refine ⟨1653422651247157582110065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102281767498105054740043 1653422651247157582110065)
            ·
              refine ⟨1240066988435368186582549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653422651247157582110065 1240066988435368186582549)
              ·
                refine ⟨58128140082907883746057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1240066988435368186582549 58128140082907883746057)
                ·
                  refine ⟨43596105062180912809543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58128140082907883746057 43596105062180912809543)
                  ·
                    rfl

theorem cell20_95516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_95516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95516 prefixEnd_95516 := by exact prefixLift 95516
  have htrace : WordTrace (prefixWord ++ tailWord_95516) baseStart_95516 baseEnd_95516 := by
    simpa [prefixWord, tailWord_95516, baseEnd_95516] using wordTrace_append hprefix tailTrace_95516
  have hstable : (prefixWord ++ tailWord_95516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95516).length < 2 ^ (prefixWord ++ tailWord_95516).sum := by decide
  have hdescent : baseEnd_95516 < baseStart_95516 := by decide
  rcases family_descends (prefixWord ++ tailWord_95516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95568 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_95568 : Nat := 118140960795 + 95568 * 2 ^ 59
def prefixEnd_95568 : Nat := 4983230072969 + 3 ^ 40 * 95568 * 2
def baseEnd_95568 : Nat := 43619839279099843075997

theorem tailTrace_95568 : CollatzResearch.WordTrace tailWord_95568 prefixEnd_95568 43619839279099843075997 := by
  unfold tailWord_95568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1742825658890466280035679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2323767545187288373380905 1742825658890466280035679)
  ·
    refine ⟨2614238488335699420053519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1742825658890466280035679 2614238488335699420053519)
    ·
      refine ⟨3921357732503549130080279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614238488335699420053519 3921357732503549130080279)
      ·
        refine ⟨5882036598755323695120419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921357732503549130080279 5882036598755323695120419)
        ·
          refine ⟨8823054898132985542680629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5882036598755323695120419 8823054898132985542680629)
          ·
            refine ⟨827161396699967394626309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8823054898132985542680629 827161396699967394626309)
            ·
              refine ⟨155092761881243886492433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 827161396699967394626309 155092761881243886492433)
              ·
                refine ⟨116319571410932914869325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155092761881243886492433 116319571410932914869325)
                ·
                  refine ⟨43619839279099843075997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116319571410932914869325 43619839279099843075997)
                  ·
                    rfl

theorem cell20_95568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_95568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95568 prefixEnd_95568 := by exact prefixLift 95568
  have htrace : WordTrace (prefixWord ++ tailWord_95568) baseStart_95568 baseEnd_95568 := by
    simpa [prefixWord, tailWord_95568, baseEnd_95568] using wordTrace_append hprefix tailTrace_95568
  have hstable : (prefixWord ++ tailWord_95568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95568).length < 2 ^ (prefixWord ++ tailWord_95568).sum := by decide
  have hdescent : baseEnd_95568 < baseStart_95568 := by decide
  rcases family_descends (prefixWord ++ tailWord_95568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95592 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_95592 : Nat := 118140960795 + 95592 * 2 ^ 59
def prefixEnd_95592 : Nat := 4983230072969 + 3 ^ 40 * 95592 * 2
def baseEnd_95592 : Nat := 43630793533062426275899

theorem tailTrace_95592 : CollatzResearch.WordTrace tailWord_95592 prefixEnd_95592 43630793533062426275899 := by
  unfold tailWord_95592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743263334846992329472515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2324351113129323105963353 1743263334846992329472515)
  ·
    refine ⟨2614895002270488494208773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743263334846992329472515 2614895002270488494208773)
    ·
      refine ⟨490292812925716592664145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2614895002270488494208773 490292812925716592664145)
      ·
        refine ⟨367719609694287444498109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490292812925716592664145 367719609694287444498109)
        ·
          refine ⟨137894853635357791686791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367719609694287444498109 137894853635357791686791)
          ·
            refine ⟨206842280453036687530187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137894853635357791686791 206842280453036687530187)
            ·
              refine ⟨310263420679555031295281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206842280453036687530187 310263420679555031295281)
              ·
                refine ⟨232697565509666273471461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310263420679555031295281 232697565509666273471461)
                ·
                  refine ⟨43630793533062426275899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232697565509666273471461 43630793533062426275899)
                  ·
                    rfl

theorem cell20_95592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_95592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95592 prefixEnd_95592 := by exact prefixLift 95592
  have htrace : WordTrace (prefixWord ++ tailWord_95592) baseStart_95592 baseEnd_95592 := by
    simpa [prefixWord, tailWord_95592, baseEnd_95592] using wordTrace_append hprefix tailTrace_95592
  have hstable : (prefixWord ++ tailWord_95592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95592).length < 2 ^ (prefixWord ++ tailWord_95592).sum := by decide
  have hdescent : baseEnd_95592 < baseStart_95592 := by decide
  rcases family_descends (prefixWord ++ tailWord_95592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95620 : List Nat := [2, 3, 2, 1, 1, 4, 7]
def baseStart_95620 : Nat := 118140960795 + 95620 * 2 ^ 59
def prefixEnd_95620 : Nat := 4983230072969 + 3 ^ 40 * 95620 * 2
def baseEnd_95620 : Nat := 4849285944002085926939

theorem tailTrace_95620 : CollatzResearch.WordTrace tailWord_95620 prefixEnd_95620 4849285944002085926939 := by
  unfold tailWord_95620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743773956796272720482157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2325031942395030293976209 1743773956796272720482157)
  ·
    refine ⟨653915233798602270180809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1743773956796272720482157 653915233798602270180809)
    ·
      refine ⟨490436425348951702635607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 653915233798602270180809 490436425348951702635607)
      ·
        refine ⟨735654638023427553953411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490436425348951702635607 735654638023427553953411)
        ·
          refine ⟨1103481957035141330930117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735654638023427553953411 1103481957035141330930117)
          ·
            refine ⟨206902866944088999549397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1103481957035141330930117 206902866944088999549397)
            ·
              refine ⟨4849285944002085926939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 206902866944088999549397 4849285944002085926939)
              ·
                rfl

theorem cell20_95620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 7].length) (baseStart_95620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95620 prefixEnd_95620 := by exact prefixLift 95620
  have htrace : WordTrace (prefixWord ++ tailWord_95620) baseStart_95620 baseEnd_95620 := by
    simpa [prefixWord, tailWord_95620, baseEnd_95620] using wordTrace_append hprefix tailTrace_95620
  have hstable : (prefixWord ++ tailWord_95620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95620).length < 2 ^ (prefixWord ++ tailWord_95620).sum := by decide
  have hdescent : baseEnd_95620 < baseStart_95620 := by decide
  rcases family_descends (prefixWord ++ tailWord_95620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95623 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 3]
def baseStart_95623 : Nat := 118140960795 + 95623 * 2 ^ 59
def prefixEnd_95623 : Nat := 4983230072969 + 3 ^ 40 * 95623 * 2
def baseEnd_95623 : Nat := 43644942777764096242439

theorem tailTrace_95623 : CollatzResearch.WordTrace tailWord_95623 prefixEnd_95623 43644942777764096242439 := by
  unfold tailWord_95623
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487657332581676953323523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2325104888387784635549015 3487657332581676953323523)
  ·
    refine ⟨5231485998872515429985285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3487657332581676953323523 5231485998872515429985285)
    ·
      refine ⟨980903624788596643122241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5231485998872515429985285 980903624788596643122241)
      ·
        refine ⟨735677718591447482341681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 980903624788596643122241 735677718591447482341681)
        ·
          refine ⟨551758288943585611756261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735677718591447482341681 551758288943585611756261)
          ·
            refine ⟨103454679176922302204299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 551758288943585611756261 103454679176922302204299)
            ·
              refine ⟨155182018765383453306449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103454679176922302204299 155182018765383453306449)
              ·
                refine ⟨116386514074037589979837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155182018765383453306449 116386514074037589979837)
                ·
                  refine ⟨43644942777764096242439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116386514074037589979837 43644942777764096242439)
                  ·
                    rfl

theorem cell20_95623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_95623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95623 prefixEnd_95623 := by exact prefixLift 95623
  have htrace : WordTrace (prefixWord ++ tailWord_95623) baseStart_95623 baseEnd_95623 := by
    simpa [prefixWord, tailWord_95623, baseEnd_95623] using wordTrace_append hprefix tailTrace_95623
  have hstable : (prefixWord ++ tailWord_95623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95623).length < 2 ^ (prefixWord ++ tailWord_95623).sum := by decide
  have hdescent : baseEnd_95623 < baseStart_95623 := by decide
  rcases family_descends (prefixWord ++ tailWord_95623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95627 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_95627 : Nat := 118140960795 + 95627 * 2 ^ 59
def prefixEnd_95627 : Nat := 4983230072969 + 3 ^ 40 * 95627 * 2
def baseEnd_95627 : Nat := 43646768486757860109089

theorem tailTrace_95627 : CollatzResearch.WordTrace tailWord_95627 prefixEnd_95627 43646768486757860109089 := by
  unfold tailWord_95627
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487803224567185636469135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2325202149711457090979423 3487803224567185636469135)
  ·
    refine ⟨5231704836850778454703703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3487803224567185636469135 5231704836850778454703703)
    ·
      refine ⟨7847557255276167682055555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5231704836850778454703703 7847557255276167682055555)
      ·
        refine ⟨11771335882914251523083333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7847557255276167682055555 11771335882914251523083333)
        ·
          refine ⟨2207125478046422160578125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11771335882914251523083333 2207125478046422160578125)
          ·
            refine ⟨827672054267408310216797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2207125478046422160578125 827672054267408310216797)
            ·
              refine ⟨310377020350278116331299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 827672054267408310216797 310377020350278116331299)
              ·
                refine ⟨465565530525417174496949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310377020350278116331299 465565530525417174496949)
                ·
                  refine ⟨43646768486757860109089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465565530525417174496949 43646768486757860109089)
                  ·
                    rfl

theorem cell20_95627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_95627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95627 prefixEnd_95627 := by exact prefixLift 95627
  have htrace : WordTrace (prefixWord ++ tailWord_95627) baseStart_95627 baseEnd_95627 := by
    simpa [prefixWord, tailWord_95627, baseEnd_95627] using wordTrace_append hprefix tailTrace_95627
  have hstable : (prefixWord ++ tailWord_95627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95627).length < 2 ^ (prefixWord ++ tailWord_95627).sum := by decide
  have hdescent : baseEnd_95627 < baseStart_95627 := by decide
  rcases family_descends (prefixWord ++ tailWord_95627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95640 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_95640 : Nat := 118140960795 + 95640 * 2 ^ 59
def prefixEnd_95640 : Nat := 4983230072969 + 3 ^ 40 * 95640 * 2
def baseEnd_95640 : Nat := 43652702040987592675703

theorem tailTrace_95640 : CollatzResearch.WordTrace tailWord_95640 prefixEnd_95640 43652702040987592675703 := by
  unfold tailWord_95640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744138686760044428346187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2325518249013392571128249 1744138686760044428346187)
  ·
    refine ⟨2616208030140066642519281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1744138686760044428346187 2616208030140066642519281)
    ·
      refine ⟨1962156022605049981889461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2616208030140066642519281 1962156022605049981889461)
      ·
        refine ⟨183952127119223435802137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1962156022605049981889461 183952127119223435802137)
        ·
          refine ⟨137964095339417576851603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183952127119223435802137 137964095339417576851603)
          ·
            refine ⟨206946143009126365277405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137964095339417576851603 206946143009126365277405)
            ·
              refine ⟨77604803628422386979027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206946143009126365277405 77604803628422386979027)
              ·
                refine ⟨116407205442633580468541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77604803628422386979027 116407205442633580468541)
                ·
                  refine ⟨43652702040987592675703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116407205442633580468541 43652702040987592675703)
                  ·
                    rfl

theorem cell20_95640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_95640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95640 prefixEnd_95640 := by exact prefixLift 95640
  have htrace : WordTrace (prefixWord ++ tailWord_95640) baseStart_95640 baseEnd_95640 := by
    simpa [prefixWord, tailWord_95640, baseEnd_95640] using wordTrace_append hprefix tailTrace_95640
  have hstable : (prefixWord ++ tailWord_95640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95640).length < 2 ^ (prefixWord ++ tailWord_95640).sum := by decide
  have hdescent : baseEnd_95640 < baseStart_95640 := by decide
  rcases family_descends (prefixWord ++ tailWord_95640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95665 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_95665 : Nat := 118140960795 + 95665 * 2 ^ 59
def prefixEnd_95665 : Nat := 4983230072969 + 3 ^ 40 * 95665 * 2
def baseEnd_95665 : Nat := 43664112722198616842267

theorem tailTrace_95665 : CollatzResearch.WordTrace tailWord_95665 prefixEnd_95665 43664112722198616842267 := by
  unfold tailWord_95665
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489189198429518126352449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2326126132286345417568299 3489189198429518126352449)
  ·
    refine ⟨2616891898822138594764337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3489189198429518126352449 2616891898822138594764337)
    ·
      refine ⟨1962668924116603946073253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2616891898822138594764337 1962668924116603946073253)
      ·
        refine ⟨368000423271863239888735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1962668924116603946073253 368000423271863239888735)
        ·
          refine ⟨552000634907794859833103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368000423271863239888735 552000634907794859833103)
          ·
            refine ⟨828000952361692289749655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552000634907794859833103 828000952361692289749655)
            ·
              refine ⟨1242001428542538434624483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828000952361692289749655 1242001428542538434624483)
              ·
                refine ⟨1863002142813807651936725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242001428542538434624483 1863002142813807651936725)
                ·
                  refine ⟨43664112722198616842267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1863002142813807651936725 43664112722198616842267)
                  ·
                    rfl

theorem cell20_95665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_95665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95665 prefixEnd_95665 := by exact prefixLift 95665
  have htrace : WordTrace (prefixWord ++ tailWord_95665) baseStart_95665 baseEnd_95665 := by
    simpa [prefixWord, tailWord_95665, baseEnd_95665] using wordTrace_append hprefix tailTrace_95665
  have hstable : (prefixWord ++ tailWord_95665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95665).length < 2 ^ (prefixWord ++ tailWord_95665).sum := by decide
  have hdescent : baseEnd_95665 < baseStart_95665 := by decide
  rcases family_descends (prefixWord ++ tailWord_95665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95672 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_95672 : Nat := 118140960795 + 95672 * 2 ^ 59
def prefixEnd_95672 : Nat := 4983230072969 + 3 ^ 40 * 95672 * 2
def baseEnd_95672 : Nat := 43667307712937703608905

theorem tailTrace_95672 : CollatzResearch.WordTrace tailWord_95672 prefixEnd_95672 43667307712937703608905 := by
  unfold tailWord_95672
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744722254702079160928635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2326296339602772214571513 1744722254702079160928635)
  ·
    refine ⟨2617083382053118741392953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1744722254702079160928635 2617083382053118741392953)
    ·
      refine ⟨1962812536539839056044715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2617083382053118741392953 1962812536539839056044715)
      ·
        refine ⟨2944218804809758584067073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962812536539839056044715 2944218804809758584067073)
        ·
          refine ⟨2208164103607318938050305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944218804809758584067073 2208164103607318938050305)
          ·
            refine ⟨1656123077705489203537729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208164103607318938050305 1656123077705489203537729)
            ·
              refine ⟨1242092308279116902653297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656123077705489203537729 1242092308279116902653297)
              ·
                refine ⟨931569231209337676989973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242092308279116902653297 931569231209337676989973)
                ·
                  refine ⟨43667307712937703608905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 931569231209337676989973 43667307712937703608905)
                  ·
                    rfl

theorem cell20_95672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_95672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95672 prefixEnd_95672 := by exact prefixLift 95672
  have htrace : WordTrace (prefixWord ++ tailWord_95672) baseStart_95672 baseEnd_95672 := by
    simpa [prefixWord, tailWord_95672, baseEnd_95672] using wordTrace_append hprefix tailTrace_95672
  have hstable : (prefixWord ++ tailWord_95672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95672).length < 2 ^ (prefixWord ++ tailWord_95672).sum := by decide
  have hdescent : baseEnd_95672 < baseStart_95672 := by decide
  rcases family_descends (prefixWord ++ tailWord_95672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95734 : List Nat := [5, 1, 1, 1, 2, 10]
def baseStart_95734 : Nat := 118140960795 + 95734 * 2 ^ 59
def prefixEnd_95734 : Nat := 4983230072969 + 3 ^ 40 * 95734 * 2
def baseEnd_95734 : Nat := 1618355785271890501555

theorem tailTrace_95734 : CollatzResearch.WordTrace tailWord_95734 prefixEnd_95734 1618355785271890501555 := by
  unfold tailWord_95734
  simp only [CollatzResearch.WordTrace]
  refine ⟨218231614698721431913391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2327803890119695273742837 218231614698721431913391)
  ·
    refine ⟨327347422048082147870087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218231614698721431913391 327347422048082147870087)
    ·
      refine ⟨491021133072123221805131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327347422048082147870087 491021133072123221805131)
      ·
        refine ⟨736531699608184832707697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491021133072123221805131 736531699608184832707697)
        ·
          refine ⟨552398774706138624530773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736531699608184832707697 552398774706138624530773)
          ·
            refine ⟨1618355785271890501555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 552398774706138624530773 1618355785271890501555)
            ·
              rfl

theorem cell20_95734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 10].length) (baseStart_95734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95734 prefixEnd_95734 := by exact prefixLift 95734
  have htrace : WordTrace (prefixWord ++ tailWord_95734) baseStart_95734 baseEnd_95734 := by
    simpa [prefixWord, tailWord_95734, baseEnd_95734] using wordTrace_append hprefix tailTrace_95734
  have hstable : (prefixWord ++ tailWord_95734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95734).length < 2 ^ (prefixWord ++ tailWord_95734).sum := by decide
  have hdescent : baseEnd_95734 < baseStart_95734 := by decide
  rcases family_descends (prefixWord ++ tailWord_95734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95751 : List Nat := [1, 1, 4, 3, 2, 3, 1, 5]
def baseStart_95751 : Nat := 118140960795 + 95751 * 2 ^ 59
def prefixEnd_95751 : Nat := 4983230072969 + 3 ^ 40 * 95751 * 2
def baseEnd_95751 : Nat := 14567788488521513325083

theorem tailTrace_95751 : CollatzResearch.WordTrace tailWord_95751 prefixEnd_95751 14567788488521513325083 := by
  unfold tailWord_95751
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492325876117954813983107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2328217250745303209322071 3492325876117954813983107)
  ·
    refine ⟨5238488814176932220974661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3492325876117954813983107 5238488814176932220974661)
    ·
      refine ⟨982216652658174791432749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5238488814176932220974661 982216652658174791432749)
      ·
        refine ⟨368331244746815546787281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 982216652658174791432749 368331244746815546787281)
        ·
          refine ⟨276248433560111660090461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368331244746815546787281 276248433560111660090461)
          ·
            refine ⟨103593162585041872533923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276248433560111660090461 103593162585041872533923)
            ·
              refine ⟨155389743877562808800885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103593162585041872533923 155389743877562808800885)
              ·
                refine ⟨14567788488521513325083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155389743877562808800885 14567788488521513325083)
                ·
                  rfl

theorem cell20_95751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_95751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95751 prefixEnd_95751 := by exact prefixLift 95751
  have htrace : WordTrace (prefixWord ++ tailWord_95751) baseStart_95751 baseEnd_95751 := by
    simpa [prefixWord, tailWord_95751, baseEnd_95751] using wordTrace_append hprefix tailTrace_95751
  have hstable : (prefixWord ++ tailWord_95751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95751).length < 2 ^ (prefixWord ++ tailWord_95751).sum := by decide
  have hdescent : baseEnd_95751 < baseStart_95751 := by decide
  rcases family_descends (prefixWord ++ tailWord_95751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95765 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_95765 : Nat := 118140960795 + 95765 * 2 ^ 59
def prefixEnd_95765 : Nat := 4983230072969 + 3 ^ 40 * 95765 * 2
def baseEnd_95765 : Nat := 43709755447042713508525

theorem tailTrace_95765 : CollatzResearch.WordTrace tailWord_95765 prefixEnd_95765 43709755447042713508525 := by
  unfold tailWord_95765
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492836498067235204992749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2328557665378156803328499 3492836498067235204992749)
  ·
    refine ⟨1309813686775213201872281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3492836498067235204992749 1309813686775213201872281)
    ·
      refine ⟨982360265081409901404211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1309813686775213201872281 982360265081409901404211)
      ·
        refine ⟨1473540397622114852106317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982360265081409901404211 1473540397622114852106317)
        ·
          refine ⟨552577649108293069539869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1473540397622114852106317 552577649108293069539869)
          ·
            refine ⟨207216618415609901077451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 552577649108293069539869 207216618415609901077451)
            ·
              refine ⟨310824927623414851616177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207216618415609901077451 310824927623414851616177)
              ·
                refine ⟨233118695717561138712133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310824927623414851616177 233118695717561138712133)
                ·
                  refine ⟨43709755447042713508525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233118695717561138712133 43709755447042713508525)
                  ·
                    rfl

theorem cell20_95765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_95765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95765 prefixEnd_95765 := by exact prefixLift 95765
  have htrace : WordTrace (prefixWord ++ tailWord_95765) baseStart_95765 baseEnd_95765 := by
    simpa [prefixWord, tailWord_95765, baseEnd_95765] using wordTrace_append hprefix tailTrace_95765
  have hstable : (prefixWord ++ tailWord_95765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95765).length < 2 ^ (prefixWord ++ tailWord_95765).sum := by decide
  have hdescent : baseEnd_95765 < baseStart_95765 := by decide
  rcases family_descends (prefixWord ++ tailWord_95765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95774 : List Nat := [4, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_95774 : Nat := 118140960795 + 95774 * 2 ^ 59
def prefixEnd_95774 : Nat := 4983230072969 + 3 ^ 40 * 95774 * 2
def baseEnd_95774 : Nat := 43713863292278682208489

theorem tailTrace_95774 : CollatzResearch.WordTrace tailWord_95774 prefixEnd_95774 43713863292278682208489 := by
  unfold tailWord_95774
  simp only [CollatzResearch.WordTrace]
  refine ⟨436645594379328717758797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2328776503356419828046917 436645594379328717758797)
  ·
    refine ⟨163742097892248269159549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 436645594379328717758797 163742097892248269159549)
    ·
      refine ⟨61403286709593100934831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163742097892248269159549 61403286709593100934831)
      ·
        refine ⟨92104930064389651402247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61403286709593100934831 92104930064389651402247)
        ·
          refine ⟨138157395096584477103371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92104930064389651402247 138157395096584477103371)
          ·
            refine ⟨207236092644876715655057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138157395096584477103371 207236092644876715655057)
            ·
              refine ⟨155427069483657536741293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207236092644876715655057 155427069483657536741293)
              ·
                refine ⟨58285151056371576277985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155427069483657536741293 58285151056371576277985)
                ·
                  refine ⟨43713863292278682208489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58285151056371576277985 43713863292278682208489)
                  ·
                    rfl

theorem cell20_95774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_95774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95774 prefixEnd_95774 := by exact prefixLift 95774
  have htrace : WordTrace (prefixWord ++ tailWord_95774) baseStart_95774 baseEnd_95774 := by
    simpa [prefixWord, tailWord_95774, baseEnd_95774] using wordTrace_append hprefix tailTrace_95774
  have hstable : (prefixWord ++ tailWord_95774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95774).length < 2 ^ (prefixWord ++ tailWord_95774).sum := by decide
  have hdescent : baseEnd_95774 < baseStart_95774 := by decide
  rcases family_descends (prefixWord ++ tailWord_95774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95817 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 3]
def baseStart_95817 : Nat := 118140960795 + 95817 * 2 ^ 59
def prefixEnd_95817 : Nat := 4983230072969 + 3 ^ 40 * 95817 * 2
def baseEnd_95817 : Nat := 43733489663961643774979

theorem tailTrace_95817 : CollatzResearch.WordTrace tailWord_95817 prefixEnd_95817 43733489663961643774979 := by
  unfold tailWord_95817
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494733093878848085885705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2329822062585898723923803 3494733093878848085885705)
  ·
    refine ⟨2621049820409136064414279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3494733093878848085885705 2621049820409136064414279)
    ·
      refine ⟨3931574730613704096621419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621049820409136064414279 3931574730613704096621419)
      ·
        refine ⟨5897362095920556144932129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931574730613704096621419 5897362095920556144932129)
        ·
          refine ⟨4423021571940417108699097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5897362095920556144932129 4423021571940417108699097)
          ·
            refine ⟨3317266178955312831524323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4423021571940417108699097 3317266178955312831524323)
            ·
              refine ⟨4975899268432969247286485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317266178955312831524323 4975899268432969247286485)
              ·
                refine ⟨116622639103897716733277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4975899268432969247286485 116622639103897716733277)
                ·
                  refine ⟨43733489663961643774979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116622639103897716733277 43733489663961643774979)
                  ·
                    rfl

theorem cell20_95817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_95817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95817 prefixEnd_95817 := by exact prefixLift 95817
  have htrace : WordTrace (prefixWord ++ tailWord_95817) baseStart_95817 baseEnd_95817 := by
    simpa [prefixWord, tailWord_95817, baseEnd_95817] using wordTrace_append hprefix tailTrace_95817
  have hstable : (prefixWord ++ tailWord_95817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95817).length < 2 ^ (prefixWord ++ tailWord_95817).sum := by decide
  have hdescent : baseEnd_95817 < baseStart_95817 := by decide
  rcases family_descends (prefixWord ++ tailWord_95817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95824 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_95824 : Nat := 118140960795 + 95824 * 2 ^ 59
def prefixEnd_95824 : Nat := 4983230072969 + 3 ^ 40 * 95824 * 2
def baseEnd_95824 : Nat := 43736684654700730541617

theorem tailTrace_95824 : CollatzResearch.WordTrace tailWord_95824 prefixEnd_95824 43736684654700730541617 := by
  unfold tailWord_95824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747494202426744140695263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2329992269902325520927017 1747494202426744140695263)
  ·
    refine ⟨2621241303640116211042895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1747494202426744140695263 2621241303640116211042895)
    ·
      refine ⟨3931861955460174316564343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621241303640116211042895 3931861955460174316564343)
      ·
        refine ⟨5897792933190261474846515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3931861955460174316564343 5897792933190261474846515)
        ·
          refine ⟨8846689399785392212269773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5897792933190261474846515 8846689399785392212269773)
          ·
            refine ⟨3317508524919522079601165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8846689399785392212269773 3317508524919522079601165)
            ·
              refine ⟨1244065696844820779850437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3317508524919522079601165 1244065696844820779850437)
              ·
                refine ⟨233262318158403896221957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1244065696844820779850437 233262318158403896221957)
                ·
                  refine ⟨43736684654700730541617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233262318158403896221957 43736684654700730541617)
                  ·
                    rfl

theorem cell20_95824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_95824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95824 prefixEnd_95824 := by exact prefixLift 95824
  have htrace : WordTrace (prefixWord ++ tailWord_95824) baseStart_95824 baseEnd_95824 := by
    simpa [prefixWord, tailWord_95824, baseEnd_95824] using wordTrace_append hprefix tailTrace_95824
  have hstable : (prefixWord ++ tailWord_95824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95824).length < 2 ^ (prefixWord ++ tailWord_95824).sum := by decide
  have hdescent : baseEnd_95824 < baseStart_95824 := by decide
  rcases family_descends (prefixWord ++ tailWord_95824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95848 : List Nat := [2, 1, 4, 3, 1, 1, 8]
def baseStart_95848 : Nat := 118140960795 + 95848 * 2 ^ 59
def prefixEnd_95848 : Nat := 4983230072969 + 3 ^ 40 * 95848 * 2
def baseEnd_95848 : Nat := 4860848767629257082391

theorem tailTrace_95848 : CollatzResearch.WordTrace tailWord_95848 prefixEnd_95848 4860848767629257082391 := by
  unfold tailWord_95848
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747931878383270190132099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2330575837844360253509465 1747931878383270190132099)
  ·
    refine ⟨2621897817574905285198149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1747931878383270190132099 2621897817574905285198149)
    ·
      refine ⟨491605840795294740974653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2621897817574905285198149 491605840795294740974653)
      ·
        refine ⟨184352190298235527865495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491605840795294740974653 184352190298235527865495)
        ·
          refine ⟨276528285447353291798243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184352190298235527865495 276528285447353291798243)
          ·
            refine ⟨414792428171029937697365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276528285447353291798243 414792428171029937697365)
            ·
              refine ⟨4860848767629257082391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 414792428171029937697365 4860848767629257082391)
              ·
                rfl

theorem cell20_95848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 8].length) (baseStart_95848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95848 prefixEnd_95848 := by exact prefixLift 95848
  have htrace : WordTrace (prefixWord ++ tailWord_95848) baseStart_95848 baseEnd_95848 := by
    simpa [prefixWord, tailWord_95848, baseEnd_95848] using wordTrace_append hprefix tailTrace_95848
  have hstable : (prefixWord ++ tailWord_95848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95848).length < 2 ^ (prefixWord ++ tailWord_95848).sum := by decide
  have hdescent : baseEnd_95848 < baseStart_95848 := by decide
  rcases family_descends (prefixWord ++ tailWord_95848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95854 : List Nat := [4, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_95854 : Nat := 118140960795 + 95854 * 2 ^ 59
def prefixEnd_95854 : Nat := 4983230072969 + 3 ^ 40 * 95854 * 2
def baseEnd_95854 : Nat := 43750377472153959541495

theorem tailTrace_95854 : CollatzResearch.WordTrace tailWord_95854 prefixEnd_95854 43750377472153959541495 := by
  unfold tailWord_95854
  simp only [CollatzResearch.WordTrace]
  refine ⟨437010324343100425622827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2330721729829868936655077 437010324343100425622827)
  ·
    refine ⟨655515486514650638434241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437010324343100425622827 655515486514650638434241)
    ·
      refine ⟨491636614885987978825681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 655515486514650638434241 491636614885987978825681)
      ·
        refine ⟨368727461164490984119261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491636614885987978825681 368727461164490984119261)
        ·
          refine ⟨138272797936684119044723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368727461164490984119261 138272797936684119044723)
          ·
            refine ⟨207409196905026178567085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138272797936684119044723 207409196905026178567085)
            ·
              refine ⟨77778448839384816962657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207409196905026178567085 77778448839384816962657)
              ·
                refine ⟨58333836629538612721993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77778448839384816962657 58333836629538612721993)
                ·
                  refine ⟨43750377472153959541495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58333836629538612721993 43750377472153959541495)
                  ·
                    rfl

theorem cell20_95854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_95854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95854 prefixEnd_95854 := by exact prefixLift 95854
  have htrace : WordTrace (prefixWord ++ tailWord_95854) baseStart_95854 baseEnd_95854 := by
    simpa [prefixWord, tailWord_95854, baseEnd_95854] using wordTrace_append hprefix tailTrace_95854
  have hstable : (prefixWord ++ tailWord_95854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95854).length < 2 ^ (prefixWord ++ tailWord_95854).sum := by decide
  have hdescent : baseEnd_95854 < baseStart_95854 := by decide
  rcases family_descends (prefixWord ++ tailWord_95854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95855 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 3]
def baseStart_95855 : Nat := 118140960795 + 95855 * 2 ^ 59
def prefixEnd_95855 : Nat := 4983230072969 + 3 ^ 40 * 95855 * 2
def baseEnd_95855 : Nat := 43750833899402400508157

theorem tailTrace_95855 : CollatzResearch.WordTrace tailWord_95855 prefixEnd_95855 43750833899402400508157 := by
  unfold tailWord_95855
  simp only [CollatzResearch.WordTrace]
  refine ⟨3496119067741180575769019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2330746045160787050512679 3496119067741180575769019)
  ·
    refine ⟨5244178601611770863653529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3496119067741180575769019 5244178601611770863653529)
    ·
      refine ⟨3933133951208828147740147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5244178601611770863653529 3933133951208828147740147)
      ·
        refine ⟨5899700926813242221610221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933133951208828147740147 5899700926813242221610221)
        ·
          refine ⟨2212387847554965833103833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5899700926813242221610221 2212387847554965833103833)
          ·
            refine ⟨1659290885666224374827875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2212387847554965833103833 1659290885666224374827875)
            ·
              refine ⟨2488936328499336562241813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659290885666224374827875 2488936328499336562241813)
              ·
                refine ⟨116668890398406401355085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2488936328499336562241813 116668890398406401355085)
                ·
                  refine ⟨43750833899402400508157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116668890398406401355085 43750833899402400508157)
                  ·
                    rfl

theorem cell20_95855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_95855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95855 prefixEnd_95855 := by exact prefixLift 95855
  have htrace : WordTrace (prefixWord ++ tailWord_95855) baseStart_95855 baseEnd_95855 := by
    simpa [prefixWord, tailWord_95855, baseEnd_95855] using wordTrace_append hprefix tailTrace_95855
  have hstable : (prefixWord ++ tailWord_95855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95855).length < 2 ^ (prefixWord ++ tailWord_95855).sum := by decide
  have hdescent : baseEnd_95855 < baseStart_95855 := by decide
  rcases family_descends (prefixWord ++ tailWord_95855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95858 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_95858 : Nat := 118140960795 + 95858 * 2 ^ 59
def prefixEnd_95858 : Nat := 4983230072969 + 3 ^ 40 * 95858 * 2
def baseEnd_95858 : Nat := 43752203181147723408145

theorem tailTrace_95858 : CollatzResearch.WordTrace tailWord_95858 prefixEnd_95858 43752203181147723408145 := by
  unfold tailWord_95858
  simp only [CollatzResearch.WordTrace]
  refine ⟨874057121682578022032057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2330818991153541392085485 874057121682578022032057)
  ·
    refine ⟨655542841261933516524043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 874057121682578022032057 655542841261933516524043)
    ·
      refine ⟨983314261892900274786065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655542841261933516524043 983314261892900274786065)
      ·
        refine ⟨737485696419675206089549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 983314261892900274786065 737485696419675206089549)
        ·
          refine ⟨276557136157378202283581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 737485696419675206089549 276557136157378202283581)
          ·
            refine ⟨103708926059016825856343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276557136157378202283581 103708926059016825856343)
            ·
              refine ⟨155563389088525238784515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103708926059016825856343 155563389088525238784515)
              ·
                refine ⟨233345083632787858176773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155563389088525238784515 233345083632787858176773)
                ·
                  refine ⟨43752203181147723408145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233345083632787858176773 43752203181147723408145)
                  ·
                    rfl

theorem cell20_95858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_95858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95858 prefixEnd_95858 := by exact prefixLift 95858
  have htrace : WordTrace (prefixWord ++ tailWord_95858) baseStart_95858 baseEnd_95858 := by
    simpa [prefixWord, tailWord_95858, baseEnd_95858] using wordTrace_append hprefix tailTrace_95858
  have hstable : (prefixWord ++ tailWord_95858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95858).length < 2 ^ (prefixWord ++ tailWord_95858).sum := by decide
  have hdescent : baseEnd_95858 < baseStart_95858 := by decide
  rcases family_descends (prefixWord ++ tailWord_95858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95886 : List Nat := [4, 1, 1, 3, 1, 2, 2, 6]
def baseStart_95886 : Nat := 118140960795 + 95886 * 2 ^ 59
def prefixEnd_95886 : Nat := 4983230072969 + 3 ^ 40 * 95886 * 2
def baseEnd_95886 : Nat := 14588327714701356824899

theorem tailTrace_95886 : CollatzResearch.WordTrace tailWord_95886 prefixEnd_95886 14588327714701356824899 := by
  unfold tailWord_95886
  simp only [CollatzResearch.WordTrace]
  refine ⟨437156216328609108768439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2331499820419248580098341 437156216328609108768439)
  ·
    refine ⟨655734324492913663152659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437156216328609108768439 655734324492913663152659)
    ·
      refine ⟨983601486739370494728989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655734324492913663152659 983601486739370494728989)
      ·
        refine ⟨368850557527263935523371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 983601486739370494728989 368850557527263935523371)
        ·
          refine ⟨553275836290895903285057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368850557527263935523371 553275836290895903285057)
          ·
            refine ⟨414956877218171927463793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553275836290895903285057 414956877218171927463793)
            ·
              refine ⟨311217657913628945597845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414956877218171927463793 311217657913628945597845)
              ·
                refine ⟨14588327714701356824899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 311217657913628945597845 14588327714701356824899)
                ·
                  rfl

theorem cell20_95886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_95886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95886 prefixEnd_95886 := by exact prefixLift 95886
  have htrace : WordTrace (prefixWord ++ tailWord_95886) baseStart_95886 baseEnd_95886 := by
    simpa [prefixWord, tailWord_95886, baseEnd_95886] using wordTrace_append hprefix tailTrace_95886
  have hstable : (prefixWord ++ tailWord_95886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95886).length < 2 ^ (prefixWord ++ tailWord_95886).sum := by decide
  have hdescent : baseEnd_95886 < baseStart_95886 := by decide
  rcases family_descends (prefixWord ++ tailWord_95886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95903 : List Nat := [1, 1, 2, 7, 2, 7]
def baseStart_95903 : Nat := 118140960795 + 95903 * 2 ^ 59
def prefixEnd_95903 : Nat := 4983230072969 + 3 ^ 40 * 95903 * 2
def baseEnd_95903 : Nat := 1621212681752872848443

theorem tailTrace_95903 : CollatzResearch.WordTrace tailWord_95903 prefixEnd_95903 1621212681752872848443 := by
  unfold tailWord_95903
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497869771567284773516363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2331913181044856515677575 3497869771567284773516363)
  ·
    refine ⟨5246804657350927160274545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497869771567284773516363 5246804657350927160274545)
    ·
      refine ⟨3935103493013195370205909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5246804657350927160274545 3935103493013195370205909)
      ·
        refine ⟨92228988117496766489201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3935103493013195370205909 92228988117496766489201)
        ·
          refine ⟨69171741088122574866901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92228988117496766489201 69171741088122574866901)
          ·
            refine ⟨1621212681752872848443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69171741088122574866901 1621212681752872848443)
            ·
              rfl

theorem cell20_95903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 7].length) (baseStart_95903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95903 prefixEnd_95903 := by exact prefixLift 95903
  have htrace : WordTrace (prefixWord ++ tailWord_95903) baseStart_95903 baseEnd_95903 := by
    simpa [prefixWord, tailWord_95903, baseEnd_95903] using wordTrace_append hprefix tailTrace_95903
  have hstable : (prefixWord ++ tailWord_95903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95903).length < 2 ^ (prefixWord ++ tailWord_95903).sum := by decide
  have hdescent : baseEnd_95903 < baseStart_95903 := by decide
  rcases family_descends (prefixWord ++ tailWord_95903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95906 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_95906 : Nat := 118140960795 + 95906 * 2 ^ 59
def prefixEnd_95906 : Nat := 4983230072969 + 3 ^ 40 * 95906 * 2
def baseEnd_95906 : Nat := 43774111689072889807949

theorem tailTrace_95906 : CollatzResearch.WordTrace tailWord_95906 prefixEnd_95906 43774111689072889807949 := by
  unfold tailWord_95906
  simp only [CollatzResearch.WordTrace]
  refine ⟨874494797639104071468893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2331986127037610857250381 874494797639104071468893)
  ·
    refine ⟨327935549114664026800835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 874494797639104071468893 327935549114664026800835)
    ·
      refine ⟨491903323671996040201253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327935549114664026800835 491903323671996040201253)
      ·
        refine ⟨92231873188499257537735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 491903323671996040201253 92231873188499257537735)
        ·
          refine ⟨138347809782748886306603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92231873188499257537735 138347809782748886306603)
          ·
            refine ⟨207521714674123329459905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138347809782748886306603 207521714674123329459905)
            ·
              refine ⟨155641286005592497094929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207521714674123329459905 155641286005592497094929)
              ·
                refine ⟨116730964504194372821197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155641286005592497094929 116730964504194372821197)
                ·
                  refine ⟨43774111689072889807949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116730964504194372821197 43774111689072889807949)
                  ·
                    rfl

theorem cell20_95906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_95906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95906 prefixEnd_95906 := by exact prefixLift 95906
  have htrace : WordTrace (prefixWord ++ tailWord_95906) baseStart_95906 baseEnd_95906 := by
    simpa [prefixWord, tailWord_95906, baseEnd_95906] using wordTrace_append hprefix tailTrace_95906
  have hstable : (prefixWord ++ tailWord_95906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95906).length < 2 ^ (prefixWord ++ tailWord_95906).sum := by decide
  have hdescent : baseEnd_95906 < baseStart_95906 := by decide
  rcases family_descends (prefixWord ++ tailWord_95906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95917 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_95917 : Nat := 118140960795 + 95917 * 2 ^ 59
def prefixEnd_95917 : Nat := 4983230072969 + 3 ^ 40 * 95917 * 2
def baseEnd_95917 : Nat := 43779132388805740441237

theorem tailTrace_95917 : CollatzResearch.WordTrace tailWord_95917 prefixEnd_95917 43779132388805740441237 := by
  unfold tailWord_95917
  simp only [CollatzResearch.WordTrace]
  refine ⟨3498380393516565164526005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2332253595677710109684003 3498380393516565164526005)
  ·
    refine ⟨327973161892177984174313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3498380393516565164526005 327973161892177984174313)
    ·
      refine ⟨245979871419133488130735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327973161892177984174313 245979871419133488130735)
      ·
        refine ⟨368969807128700232196103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245979871419133488130735 368969807128700232196103)
        ·
          refine ⟨553454710693050348294155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368969807128700232196103 553454710693050348294155)
          ·
            refine ⟨830182066039575522441233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553454710693050348294155 830182066039575522441233)
            ·
              refine ⟨622636549529681641830925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830182066039575522441233 622636549529681641830925)
              ·
                refine ⟨233488706073630615686597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622636549529681641830925 233488706073630615686597)
                ·
                  refine ⟨43779132388805740441237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233488706073630615686597 43779132388805740441237)
                  ·
                    rfl

theorem cell20_95917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_95917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95917 prefixEnd_95917 := by exact prefixLift 95917
  have htrace : WordTrace (prefixWord ++ tailWord_95917) baseStart_95917 baseEnd_95917 := by
    simpa [prefixWord, tailWord_95917, baseEnd_95917] using wordTrace_append hprefix tailTrace_95917
  have hstable : (prefixWord ++ tailWord_95917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95917).length < 2 ^ (prefixWord ++ tailWord_95917).sum := by decide
  have hdescent : baseEnd_95917 < baseStart_95917 := by decide
  rcases family_descends (prefixWord ++ tailWord_95917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95958 : List Nat := [5, 2, 1, 3, 1, 1, 7]
def baseStart_95958 : Nat := 118140960795 + 95958 * 2 ^ 59
def prefixEnd_95958 : Nat := 4983230072969 + 3 ^ 40 * 95958 * 2
def baseEnd_95958 : Nat := 4866427322887980008267

theorem tailTrace_95958 : CollatzResearch.WordTrace tailWord_95958 prefixEnd_95958 4866427322887980008267 := by
  unfold tailWord_95958
  simp only [CollatzResearch.WordTrace]
  refine ⟨218742236648001822923033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2333250524245352777845685 218742236648001822923033)
  ·
    refine ⟨164056677486001367192275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218742236648001822923033 164056677486001367192275)
    ·
      refine ⟨246085016229002050788413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164056677486001367192275 246085016229002050788413)
      ·
        refine ⟨92281881085875769045655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246085016229002050788413 92281881085875769045655)
        ·
          refine ⟨138422821628813653568483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92281881085875769045655 138422821628813653568483)
          ·
            refine ⟨207634232443220480352725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138422821628813653568483 207634232443220480352725)
            ·
              refine ⟨4866427322887980008267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207634232443220480352725 4866427322887980008267)
              ·
                rfl

theorem cell20_95958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 7].length) (baseStart_95958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95958 prefixEnd_95958 := by exact prefixLift 95958
  have htrace : WordTrace (prefixWord ++ tailWord_95958) baseStart_95958 baseEnd_95958 := by
    simpa [prefixWord, tailWord_95958, baseEnd_95958] using wordTrace_append hprefix tailTrace_95958
  have hstable : (prefixWord ++ tailWord_95958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95958).length < 2 ^ (prefixWord ++ tailWord_95958).sum := by decide
  have hdescent : baseEnd_95958 < baseStart_95958 := by decide
  rcases family_descends (prefixWord ++ tailWord_95958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95965 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 5]
def baseStart_95965 : Nat := 118140960795 + 95965 * 2 ^ 59
def prefixEnd_95965 : Nat := 4983230072969 + 3 ^ 40 * 95965 * 2
def baseEnd_95965 : Nat := 43801040896730906841041

theorem tailTrace_95965 : CollatzResearch.WordTrace tailWord_95965 prefixEnd_95965 43801040896730906841041 := by
  unfold tailWord_95965
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500131097342669362273349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2333420731561779574848899 3500131097342669362273349)
  ·
    refine ⟨656274580751750505426253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3500131097342669362273349 656274580751750505426253)
    ·
      refine ⟨246102967781906439534845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 656274580751750505426253 246102967781906439534845)
      ·
        refine ⟨92288612918214914825567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246102967781906439534845 92288612918214914825567)
        ·
          refine ⟨138432919377322372238351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92288612918214914825567 138432919377322372238351)
          ·
            refine ⟨207649379065983558357527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138432919377322372238351 207649379065983558357527)
            ·
              refine ⟨311474068598975337536291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207649379065983558357527 311474068598975337536291)
              ·
                refine ⟨467211102898463006304437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311474068598975337536291 467211102898463006304437)
                ·
                  refine ⟨43801040896730906841041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 467211102898463006304437 43801040896730906841041)
                  ·
                    rfl

theorem cell20_95965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_95965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95965 prefixEnd_95965 := by exact prefixLift 95965
  have htrace : WordTrace (prefixWord ++ tailWord_95965) baseStart_95965 baseEnd_95965 := by
    simpa [prefixWord, tailWord_95965, baseEnd_95965] using wordTrace_append hprefix tailTrace_95965
  have hstable : (prefixWord ++ tailWord_95965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95965).length < 2 ^ (prefixWord ++ tailWord_95965).sum := by decide
  have hdescent : baseEnd_95965 < baseStart_95965 := by decide
  rcases family_descends (prefixWord ++ tailWord_95965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95983 : List Nat := [1, 1, 2, 1, 5, 1, 2, 7]
def baseStart_95983 : Nat := 118140960795 + 95983 * 2 ^ 59
def prefixEnd_95983 : Nat := 4983230072969 + 3 ^ 40 * 95983 * 2
def baseEnd_95983 : Nat := 14603085529067614746989

theorem tailTrace_95983 : CollatzResearch.WordTrace tailWord_95983 prefixEnd_95983 14603085529067614746989 := by
  unfold tailWord_95983
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500787611277458436428603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2333858407518305624285735 3500787611277458436428603)
  ·
    refine ⟨5251181416916187654642905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3500787611277458436428603 5251181416916187654642905)
    ·
      refine ⟨3938386062687140740982179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5251181416916187654642905 3938386062687140740982179)
      ·
        refine ⟨5907579094030711111473269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3938386062687140740982179 5907579094030711111473269)
        ·
          refine ⟨553835540065379166700619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5907579094030711111473269 553835540065379166700619)
          ·
            refine ⟨830753310098068750050929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553835540065379166700619 830753310098068750050929)
            ·
              refine ⟨623064982573551562538197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830753310098068750050929 623064982573551562538197)
              ·
                refine ⟨14603085529067614746989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 623064982573551562538197 14603085529067614746989)
                ·
                  rfl

theorem cell20_95983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_95983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_95983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_95983 prefixEnd_95983 := by exact prefixLift 95983
  have htrace : WordTrace (prefixWord ++ tailWord_95983) baseStart_95983 baseEnd_95983 := by
    simpa [prefixWord, tailWord_95983, baseEnd_95983] using wordTrace_append hprefix tailTrace_95983
  have hstable : (prefixWord ++ tailWord_95983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95983).length < 2 ^ (prefixWord ++ tailWord_95983).sum := by decide
  have hdescent : baseEnd_95983 < baseStart_95983 := by decide
  rcases family_descends (prefixWord ++ tailWord_95983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96010 : List Nat := [3, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_96010 : Nat := 118140960795 + 96010 * 2 ^ 59
def prefixEnd_96010 : Nat := 4983230072969 + 3 ^ 40 * 96010 * 2
def baseEnd_96010 : Nat := 43821580122910750340857

theorem tailTrace_96010 : CollatzResearch.WordTrace tailWord_96010 prefixEnd_96010 43821580122910750340857 := by
  unfold tailWord_96010
  simp only [CollatzResearch.WordTrace]
  refine ⟨875443095544910511915371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2334514921453094698440989 875443095544910511915371)
  ·
    refine ⟨1313164643317365767873057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 875443095544910511915371 1313164643317365767873057)
    ·
      refine ⟨984873482488024325904793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1313164643317365767873057 984873482488024325904793)
      ·
        refine ⟨738655111866018244428595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 984873482488024325904793 738655111866018244428595)
        ·
          refine ⟨1107982667799027366642893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738655111866018244428595 1107982667799027366642893)
          ·
            refine ⟨415493500424635262491085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1107982667799027366642893 415493500424635262491085)
            ·
              refine ⟨155810062659238223434157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 415493500424635262491085 155810062659238223434157)
              ·
                refine ⟨58428773497214333787809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155810062659238223434157 58428773497214333787809)
                ·
                  refine ⟨43821580122910750340857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58428773497214333787809 43821580122910750340857)
                  ·
                    rfl

theorem cell20_96010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_96010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96010 prefixEnd_96010 := by exact prefixLift 96010
  have htrace : WordTrace (prefixWord ++ tailWord_96010) baseStart_96010 baseEnd_96010 := by
    simpa [prefixWord, tailWord_96010, baseEnd_96010] using wordTrace_append hprefix tailTrace_96010
  have hstable : (prefixWord ++ tailWord_96010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96010).length < 2 ^ (prefixWord ++ tailWord_96010).sum := by decide
  have hdescent : baseEnd_96010 < baseStart_96010 := by decide
  rcases family_descends (prefixWord ++ tailWord_96010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96014 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_96014 : Nat := 118140960795 + 96014 * 2 ^ 59
def prefixEnd_96014 : Nat := 4983230072969 + 3 ^ 40 * 96014 * 2
def baseEnd_96014 : Nat := 43823405831904514207507

theorem tailTrace_96014 : CollatzResearch.WordTrace tailWord_96014 prefixEnd_96014 43823405831904514207507 := by
  unfold tailWord_96014
  simp only [CollatzResearch.WordTrace]
  refine ⟨437739784270643841350887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2334612182776767153871397 437739784270643841350887)
  ·
    refine ⟨656609676405965762026331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437739784270643841350887 656609676405965762026331)
    ·
      refine ⟨984914514608948643039497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 656609676405965762026331 984914514608948643039497)
      ·
        refine ⟨738685885956711482279623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 984914514608948643039497 738685885956711482279623)
        ·
          refine ⟨1108028828935067223419435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738685885956711482279623 1108028828935067223419435)
          ·
            refine ⟨1662043243402600835129153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108028828935067223419435 1662043243402600835129153)
            ·
              refine ⟨1246532432551950626346865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662043243402600835129153 1246532432551950626346865)
              ·
                refine ⟨934899324413962969760149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246532432551950626346865 934899324413962969760149)
                ·
                  refine ⟨43823405831904514207507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 934899324413962969760149 43823405831904514207507)
                  ·
                    rfl

theorem cell20_96014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_96014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96014 prefixEnd_96014 := by exact prefixLift 96014
  have htrace : WordTrace (prefixWord ++ tailWord_96014) baseStart_96014 baseEnd_96014 := by
    simpa [prefixWord, tailWord_96014, baseEnd_96014] using wordTrace_append hprefix tailTrace_96014
  have hstable : (prefixWord ++ tailWord_96014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96014).length < 2 ^ (prefixWord ++ tailWord_96014).sum := by decide
  have hdescent : baseEnd_96014 < baseStart_96014 := by decide
  rcases family_descends (prefixWord ++ tailWord_96014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96021 : List Nat := [1, 3, 2, 1, 2, 3, 8]
def baseStart_96021 : Nat := 118140960795 + 96021 * 2 ^ 59
def prefixEnd_96021 : Nat := 4983230072969 + 3 ^ 40 * 96021 * 2
def baseEnd_96021 : Nat := 4869622313627066774905

theorem tailTrace_96021 : CollatzResearch.WordTrace tailWord_96021 prefixEnd_96021 4869622313627066774905 := by
  unfold tailWord_96021
  simp only [CollatzResearch.WordTrace]
  refine ⟨3502173585139790926311917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2334782390093193950874611 3502173585139790926311917)
  ·
    refine ⟨1313315094427421597366969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3502173585139790926311917 1313315094427421597366969)
    ·
      refine ⟨984986320820566198025227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1313315094427421597366969 984986320820566198025227)
      ·
        refine ⟨1477479481230849297037841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984986320820566198025227 1477479481230849297037841)
        ·
          refine ⟨1108109610923136972778381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1477479481230849297037841 1108109610923136972778381)
          ·
            refine ⟨415541104096176364791893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1108109610923136972778381 415541104096176364791893)
            ·
              refine ⟨4869622313627066774905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 415541104096176364791893 4869622313627066774905)
              ·
                rfl

theorem cell20_96021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_96021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_96021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_96021 prefixEnd_96021 := by exact prefixLift 96021
  have htrace : WordTrace (prefixWord ++ tailWord_96021) baseStart_96021 baseEnd_96021 := by
    simpa [prefixWord, tailWord_96021, baseEnd_96021] using wordTrace_append hprefix tailTrace_96021
  have hstable : (prefixWord ++ tailWord_96021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96021).length < 2 ^ (prefixWord ++ tailWord_96021).sum := by decide
  have hdescent : baseEnd_96021 < baseStart_96021 := by decide
  rcases family_descends (prefixWord ++ tailWord_96021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
