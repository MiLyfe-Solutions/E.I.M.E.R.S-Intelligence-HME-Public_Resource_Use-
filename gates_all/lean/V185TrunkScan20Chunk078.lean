import V185TrunkScan20Chunk077

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_475237 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_475237 : Nat := 118140960795 + 475237 * 2 ^ 59
def prefixEnd_475237 : Nat := 4983230072969 + 3 ^ 40 * 475237 * 2
def baseEnd_475237 : Nat := 216911116267433214890605

theorem tailTrace_475237 : CollatzResearch.WordTrace tailWord_475237 prefixEnd_475237 216911116267433214890605 := by
  unfold tailWord_475237
  simp only [CollatzResearch.WordTrace]
  refine ⟨17333317379304987862911965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11555544919536658575274643 17333317379304987862911965)
  ·
    refine ⟨6499994017239370448591987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17333317379304987862911965 6499994017239370448591987)
    ·
      refine ⟨9749991025859055672887981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499994017239370448591987 9749991025859055672887981)
      ·
        refine ⟨3656246634697145877332993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9749991025859055672887981 3656246634697145877332993)
        ·
          refine ⟨2742184976022859407999745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656246634697145877332993 2742184976022859407999745)
          ·
            refine ⟨2056638732017144555999809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742184976022859407999745 2056638732017144555999809)
            ·
              refine ⟨1542479049012858416999857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056638732017144555999809 1542479049012858416999857)
              ·
                refine ⟨1156859286759643812749893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542479049012858416999857 1156859286759643812749893)
                ·
                  refine ⟨216911116267433214890605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1156859286759643812749893 216911116267433214890605)
                  ·
                    rfl

theorem cell20_475237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_475237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475237 prefixEnd_475237 := by exact prefixLift 475237
  have htrace : WordTrace (prefixWord ++ tailWord_475237) baseStart_475237 baseEnd_475237 := by
    simpa [prefixWord, tailWord_475237, baseEnd_475237] using wordTrace_append hprefix tailTrace_475237
  have hstable : (prefixWord ++ tailWord_475237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475237).length < 2 ^ (prefixWord ++ tailWord_475237).sum := by decide
  have hdescent : baseEnd_475237 < baseStart_475237 := by decide
  rcases family_descends (prefixWord ++ tailWord_475237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475244 : List Nat := [2, 2, 1, 1, 3, 4, 1, 6]
def baseStart_475244 : Nat := 118140960795 + 475244 * 2 ^ 59
def prefixEnd_475244 : Nat := 4983230072969 + 3 ^ 40 * 475244 * 2
def baseEnd_475244 : Nat := 72304770419390767219081

theorem tailTrace_475244 : CollatzResearch.WordTrace tailWord_475244 prefixEnd_475244 72304770419390767219081 := by
  unfold tailWord_475244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8666786345139814029208393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11555715126853085372277857 8666786345139814029208393)
  ·
    refine ⟨6500089758854860521906295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8666786345139814029208393 6500089758854860521906295)
    ·
      refine ⟨9750134638282290782859443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6500089758854860521906295 9750134638282290782859443)
      ·
        refine ⟨14625201957423436174289165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9750134638282290782859443 14625201957423436174289165)
        ·
          refine ⟨5484450734033788565358437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14625201957423436174289165 5484450734033788565358437)
          ·
            refine ⟨1028334512631335356004707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5484450734033788565358437 1028334512631335356004707)
            ·
              refine ⟨1542501768947003034007061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028334512631335356004707 1542501768947003034007061)
              ·
                refine ⟨72304770419390767219081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1542501768947003034007061 72304770419390767219081)
                ·
                  rfl

theorem cell20_475244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_475244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475244 prefixEnd_475244 := by exact prefixLift 475244
  have htrace : WordTrace (prefixWord ++ tailWord_475244) baseStart_475244 baseEnd_475244 := by
    simpa [prefixWord, tailWord_475244, baseEnd_475244] using wordTrace_append hprefix tailTrace_475244
  have hstable : (prefixWord ++ tailWord_475244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475244).length < 2 ^ (prefixWord ++ tailWord_475244).sum := by decide
  have hdescent : baseEnd_475244 < baseStart_475244 := by decide
  rcases family_descends (prefixWord ++ tailWord_475244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475268 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_475268 : Nat := 118140960795 + 475268 * 2 ^ 59
def prefixEnd_475268 : Nat := 4983230072969 + 3 ^ 40 * 475268 * 2
def baseEnd_475268 : Nat := 216925265512134884857145

theorem tailTrace_475268 : CollatzResearch.WordTrace tailWord_475268 prefixEnd_475268 216925265512134884857145 := by
  unfold tailWord_475268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8667224021096340078645229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11556298694795120104860305 8667224021096340078645229)
  ·
    refine ⟨3250209007911127529491961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8667224021096340078645229 3250209007911127529491961)
    ·
      refine ⟨2437656755933345647118971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3250209007911127529491961 2437656755933345647118971)
      ·
        refine ⟨3656485133900018470678457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437656755933345647118971 3656485133900018470678457)
        ·
          refine ⟨2742363850425013853008843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656485133900018470678457 2742363850425013853008843)
          ·
            refine ⟨4113545775637520779513265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742363850425013853008843 4113545775637520779513265)
            ·
              refine ⟨3085159331728140584634949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113545775637520779513265 3085159331728140584634949)
              ·
                refine ⟨578467374699026359619053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3085159331728140584634949 578467374699026359619053)
                ·
                  refine ⟨216925265512134884857145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578467374699026359619053 216925265512134884857145)
                  ·
                    rfl

theorem cell20_475268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_475268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475268 prefixEnd_475268 := by exact prefixLift 475268
  have htrace : WordTrace (prefixWord ++ tailWord_475268) baseStart_475268 baseEnd_475268 := by
    simpa [prefixWord, tailWord_475268, baseEnd_475268] using wordTrace_append hprefix tailTrace_475268
  have hstable : (prefixWord ++ tailWord_475268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475268).length < 2 ^ (prefixWord ++ tailWord_475268).sum := by decide
  have hdescent : baseEnd_475268 < baseStart_475268 := by decide
  rcases family_descends (prefixWord ++ tailWord_475268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475316 : List Nat := [2, 5, 3, 1, 9]
def baseStart_475316 : Nat := 118140960795 + 475316 * 2 ^ 59
def prefixEnd_475316 : Nat := 4983230072969 + 3 ^ 40 * 475316 * 2
def baseEnd_475316 : Nat := 2678360173087161126629

theorem tailTrace_475316 : CollatzResearch.WordTrace tailWord_475316 prefixEnd_475316 2678360173087161126629 := by
  unfold tailWord_475316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668099373009392177518901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11557465830679189570025201 8668099373009392177518901)
  ·
    refine ⟨812634316219630516642397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8668099373009392177518901 812634316219630516642397)
    ·
      refine ⟨304737868582361443740899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 812634316219630516642397 304737868582361443740899)
      ·
        refine ⟨457106802873542165611349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304737868582361443740899 457106802873542165611349)
        ·
          refine ⟨2678360173087161126629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 457106802873542165611349 2678360173087161126629)
          ·
            rfl

theorem cell20_475316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 9].length) (baseStart_475316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475316 prefixEnd_475316 := by exact prefixLift 475316
  have htrace : WordTrace (prefixWord ++ tailWord_475316) baseStart_475316 baseEnd_475316 := by
    simpa [prefixWord, tailWord_475316, baseEnd_475316] using wordTrace_append hprefix tailTrace_475316
  have hstable : (prefixWord ++ tailWord_475316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475316).length < 2 ^ (prefixWord ++ tailWord_475316).sum := by decide
  have hdescent : baseEnd_475316 < baseStart_475316 := by decide
  rcases family_descends (prefixWord ++ tailWord_475316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475368 : List Nat := [2, 1, 4, 1, 2, 2, 1, 5, 2]
def baseStart_475368 : Nat := 118140960795 + 475368 * 2 ^ 59
def prefixEnd_475368 : Nat := 4983230072969 + 3 ^ 40 * 475368 * 2
def baseEnd_475368 : Nat := 216970908236978981523403

theorem tailTrace_475368 : CollatzResearch.WordTrace tailWord_475368 prefixEnd_475368 216970908236978981523403 := by
  unfold tailWord_475368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669047670915198617965379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11558730227886931490620505 8669047670915198617965379)
  ·
    refine ⟨13003571506372797926948069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8669047670915198617965379 13003571506372797926948069)
    ·
      refine ⟨2438169657444899611302763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13003571506372797926948069 2438169657444899611302763)
      ·
        refine ⟨3657254486167349416954145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438169657444899611302763 3657254486167349416954145)
        ·
          refine ⟨2742940864625512062715609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3657254486167349416954145 2742940864625512062715609)
          ·
            refine ⟨2057205648469134047036707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742940864625512062715609 2057205648469134047036707)
            ·
              refine ⟨3085808472703701070555061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057205648469134047036707 3085808472703701070555061)
              ·
                refine ⟨289294544315971975364537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3085808472703701070555061 289294544315971975364537)
                ·
                  refine ⟨216970908236978981523403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289294544315971975364537 216970908236978981523403)
                  ·
                    rfl

theorem cell20_475368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_475368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475368 prefixEnd_475368 := by exact prefixLift 475368
  have htrace : WordTrace (prefixWord ++ tailWord_475368) baseStart_475368 baseEnd_475368 := by
    simpa [prefixWord, tailWord_475368, baseEnd_475368] using wordTrace_append hprefix tailTrace_475368
  have hstable : (prefixWord ++ tailWord_475368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475368).length < 2 ^ (prefixWord ++ tailWord_475368).sum := by decide
  have hdescent : baseEnd_475368 < baseStart_475368 := by decide
  rcases family_descends (prefixWord ++ tailWord_475368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475372 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_475372 : Nat := 118140960795 + 475372 * 2 ^ 59
def prefixEnd_475372 : Nat := 4983230072969 + 3 ^ 40 * 475372 * 2
def baseEnd_475372 : Nat := 216972733945972745390053

theorem tailTrace_475372 : CollatzResearch.WordTrace tailWord_475372 prefixEnd_475372 216972733945972745390053 := by
  unfold tailWord_475372
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669120616907952959538185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11558827489210603946050913 8669120616907952959538185)
  ·
    refine ⟨6501840462680964719653639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8669120616907952959538185 6501840462680964719653639)
    ·
      refine ⟨9752760694021447079480459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501840462680964719653639 9752760694021447079480459)
      ·
        refine ⟨14629141041032170619220689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9752760694021447079480459 14629141041032170619220689)
        ·
          refine ⟨10971855780774127964415517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14629141041032170619220689 10971855780774127964415517)
          ·
            refine ⟨4114445917790297986655819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10971855780774127964415517 4114445917790297986655819)
            ·
              refine ⟨6171668876685446979983729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114445917790297986655819 6171668876685446979983729)
              ·
                refine ⟨4628751657514085234987797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171668876685446979983729 4628751657514085234987797)
                ·
                  refine ⟨216972733945972745390053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4628751657514085234987797 216972733945972745390053)
                  ·
                    rfl

theorem cell20_475372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_475372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475372 prefixEnd_475372 := by exact prefixLift 475372
  have htrace : WordTrace (prefixWord ++ tailWord_475372) baseStart_475372 baseEnd_475372 := by
    simpa [prefixWord, tailWord_475372, baseEnd_475372] using wordTrace_append hprefix tailTrace_475372
  have hstable : (prefixWord ++ tailWord_475372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475372).length < 2 ^ (prefixWord ++ tailWord_475372).sum := by decide
  have hdescent : baseEnd_475372 < baseStart_475372 := by decide
  rcases family_descends (prefixWord ++ tailWord_475372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475379 : List Nat := [1, 1, 1, 2, 2, 4, 9]
def baseStart_475379 : Nat := 118140960795 + 475379 * 2 ^ 59
def prefixEnd_475379 : Nat := 4983230072969 + 3 ^ 40 * 475379 * 2
def baseEnd_475379 : Nat := 24108436548523536906299

theorem tailTrace_475379 : CollatzResearch.WordTrace tailWord_475379 prefixEnd_475379 24108436548523536906299 := by
  unfold tailWord_475379
  simp only [CollatzResearch.WordTrace]
  refine ⟨17338496544790546114581191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11558997696527030743054127 17338496544790546114581191)
  ·
    refine ⟨26007744817185819171871787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17338496544790546114581191 26007744817185819171871787)
    ·
      refine ⟨39011617225778728757807681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26007744817185819171871787 39011617225778728757807681)
      ·
        refine ⟨29258712919334046568355761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39011617225778728757807681 29258712919334046568355761)
        ·
          refine ⟨21944034689500534926266821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29258712919334046568355761 21944034689500534926266821)
          ·
            refine ⟨4114506504281350298675029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21944034689500534926266821 4114506504281350298675029)
            ·
              refine ⟨24108436548523536906299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4114506504281350298675029 24108436548523536906299)
              ·
                rfl

theorem cell20_475379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_475379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475379 prefixEnd_475379 := by exact prefixLift 475379
  have htrace : WordTrace (prefixWord ++ tailWord_475379) baseStart_475379 baseEnd_475379 := by
    simpa [prefixWord, tailWord_475379, baseEnd_475379] using wordTrace_append hprefix tailTrace_475379
  have hstable : (prefixWord ++ tailWord_475379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475379).length < 2 ^ (prefixWord ++ tailWord_475379).sum := by decide
  have hdescent : baseEnd_475379 < baseStart_475379 := by decide
  rcases family_descends (prefixWord ++ tailWord_475379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475423 : List Nat := [1, 1, 2, 4, 3, 3, 1, 3, 2]
def baseStart_475423 : Nat := 118140960795 + 475423 * 2 ^ 59
def prefixEnd_475423 : Nat := 4983230072969 + 3 ^ 40 * 475423 * 2
def baseEnd_475423 : Nat := 216996011735643234689845

theorem tailTrace_475423 : CollatzResearch.WordTrace tailWord_475423 prefixEnd_475423 216996011735643234689845 := by
  unfold tailWord_475423
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340101356631141629182923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11560067571087427752788615 17340101356631141629182923)
  ·
    refine ⟨26010152034946712443774385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17340101356631141629182923 26010152034946712443774385)
    ·
      refine ⟨19507614026210034332830789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26010152034946712443774385 19507614026210034332830789)
      ·
        refine ⟨3657677629914381437405773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19507614026210034332830789 3657677629914381437405773)
        ·
          refine ⟨1371629111217893039027165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3657677629914381437405773 1371629111217893039027165)
          ·
            refine ⟨514360916706709889635187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1371629111217893039027165 514360916706709889635187)
            ·
              refine ⟨771541375060064834452781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514360916706709889635187 771541375060064834452781)
              ·
                refine ⟨289328015647524312919793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 771541375060064834452781 289328015647524312919793)
                ·
                  refine ⟨216996011735643234689845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289328015647524312919793 216996011735643234689845)
                  ·
                    rfl

theorem cell20_475423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 2].length) (baseStart_475423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475423 prefixEnd_475423 := by exact prefixLift 475423
  have htrace : WordTrace (prefixWord ++ tailWord_475423) baseStart_475423 baseEnd_475423 := by
    simpa [prefixWord, tailWord_475423, baseEnd_475423] using wordTrace_append hprefix tailTrace_475423
  have hstable : (prefixWord ++ tailWord_475423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475423).length < 2 ^ (prefixWord ++ tailWord_475423).sum := by decide
  have hdescent : baseEnd_475423 < baseStart_475423 := by decide
  rcases family_descends (prefixWord ++ tailWord_475423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475444 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_475444 : Nat := 118140960795 + 475444 * 2 ^ 59
def prefixEnd_475444 : Nat := 4983230072969 + 3 ^ 40 * 475444 * 2
def baseEnd_475444 : Nat := 217005596707860494989759

theorem tailTrace_475444 : CollatzResearch.WordTrace tailWord_475444 prefixEnd_475444 217005596707860494989759 := by
  unfold tailWord_475444
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670433644777531107848693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11560578193036708143798257 8670433644777531107848693)
  ·
    refine ⟨812853154197893541360815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8670433644777531107848693 812853154197893541360815)
    ·
      refine ⟨1219279731296840312041223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812853154197893541360815 1219279731296840312041223)
      ·
        refine ⟨1828919596945260468061835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219279731296840312041223 1828919596945260468061835)
        ·
          refine ⟨2743379395417890702092753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828919596945260468061835 2743379395417890702092753)
          ·
            refine ⟨2057534546563418026569565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2743379395417890702092753 2057534546563418026569565)
            ·
              refine ⟨771575454961281759963587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2057534546563418026569565 771575454961281759963587)
              ·
                refine ⟨1157363182441922639945381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771575454961281759963587 1157363182441922639945381)
                ·
                  refine ⟨217005596707860494989759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1157363182441922639945381 217005596707860494989759)
                  ·
                    rfl

theorem cell20_475444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_475444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475444 prefixEnd_475444 := by exact prefixLift 475444
  have htrace : WordTrace (prefixWord ++ tailWord_475444) baseStart_475444 baseEnd_475444 := by
    simpa [prefixWord, tailWord_475444, baseEnd_475444] using wordTrace_append hprefix tailTrace_475444
  have hstable : (prefixWord ++ tailWord_475444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475444).length < 2 ^ (prefixWord ++ tailWord_475444).sum := by decide
  have hdescent : baseEnd_475444 < baseStart_475444 := by decide
  rcases family_descends (prefixWord ++ tailWord_475444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475454 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_475454 : Nat := 118140960795 + 475454 * 2 ^ 59
def prefixEnd_475454 : Nat := 4983230072969 + 3 ^ 40 * 475454 * 2
def baseEnd_475454 : Nat := 217010160980344904656385

theorem tailTrace_475454 : CollatzResearch.WordTrace tailWord_475454 prefixEnd_475454 217010160980344904656385 := by
  unfold tailWord_475454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2167654002439854240445177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11560821346345889282374277 2167654002439854240445177)
  ·
    refine ⟨1625740501829890680333883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2167654002439854240445177 1625740501829890680333883)
    ·
      refine ⟨2438610752744836020500825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625740501829890680333883 2438610752744836020500825)
      ·
        refine ⟨1828958064558627015375619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2438610752744836020500825 1828958064558627015375619)
        ·
          refine ⟨2743437096837940523063429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828958064558627015375619 2743437096837940523063429)
          ·
            refine ⟨514394455657113848074393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2743437096837940523063429 514394455657113848074393)
            ·
              refine ⟨385795841742835386055795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514394455657113848074393 385795841742835386055795)
              ·
                refine ⟨578693762614253079083693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385795841742835386055795 578693762614253079083693)
                ·
                  refine ⟨217010160980344904656385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578693762614253079083693 217010160980344904656385)
                  ·
                    rfl

theorem cell20_475454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_475454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475454 prefixEnd_475454 := by exact prefixLift 475454
  have htrace : WordTrace (prefixWord ++ tailWord_475454) baseStart_475454 baseEnd_475454 := by
    simpa [prefixWord, tailWord_475454, baseEnd_475454] using wordTrace_append hprefix tailTrace_475454
  have hstable : (prefixWord ++ tailWord_475454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475454).length < 2 ^ (prefixWord ++ tailWord_475454).sum := by decide
  have hdescent : baseEnd_475454 < baseStart_475454 := by decide
  rcases family_descends (prefixWord ++ tailWord_475454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475493 : List Nat := [1, 3, 1, 3, 1, 11]
def baseStart_475493 : Nat := 118140960795 + 475493 * 2 ^ 59
def prefixEnd_475493 : Nat := 4983230072969 + 3 ^ 40 * 475493 * 2
def baseEnd_475493 : Nat := 8038072653445707494675

theorem tailTrace_475493 : CollatzResearch.WordTrace tailWord_475493 prefixEnd_475493 8038072653445707494675 := by
  unfold tailWord_475493
  simp only [CollatzResearch.WordTrace]
  refine ⟨17342654466377543584231133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11561769644251695722820755 17342654466377543584231133)
  ·
    refine ⟨6503495424891578844086675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17342654466377543584231133 6503495424891578844086675)
    ·
      refine ⟨9755243137337368266130013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6503495424891578844086675 9755243137337368266130013)
      ·
        refine ⟨3658216176501513099798755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9755243137337368266130013 3658216176501513099798755)
        ·
          refine ⟨5487324264752269649698133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3658216176501513099798755 5487324264752269649698133)
          ·
            refine ⟨8038072653445707494675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5487324264752269649698133 8038072653445707494675)
            ·
              rfl

theorem cell20_475493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 11].length) (baseStart_475493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475493 prefixEnd_475493 := by exact prefixLift 475493
  have htrace : WordTrace (prefixWord ++ tailWord_475493) baseStart_475493 baseEnd_475493 := by
    simpa [prefixWord, tailWord_475493, baseEnd_475493] using wordTrace_append hprefix tailTrace_475493
  have hstable : (prefixWord ++ tailWord_475493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475493).length < 2 ^ (prefixWord ++ tailWord_475493).sum := by decide
  have hdescent : baseEnd_475493 < baseStart_475493 := by decide
  rcases family_descends (prefixWord ++ tailWord_475493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475496 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_475496 : Nat := 118140960795 + 475496 * 2 ^ 59
def prefixEnd_475496 : Nat := 4983230072969 + 3 ^ 40 * 475496 * 2
def baseEnd_475496 : Nat := 217029330924779425256213

theorem tailTrace_475496 : CollatzResearch.WordTrace tailWord_475496 prefixEnd_475496 217029330924779425256213 := by
  unfold tailWord_475496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8671381942683337548295171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11561842590244450064393561 8671381942683337548295171)
  ·
    refine ⟨13007072914025006322442757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8671381942683337548295171 13007072914025006322442757)
    ·
      refine ⟨2438826171379688685458017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13007072914025006322442757 2438826171379688685458017)
      ·
        refine ⟨1829119628534766514093513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2438826171379688685458017 1829119628534766514093513)
        ·
          refine ⟨1371839721401074885570135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1829119628534766514093513 1371839721401074885570135)
          ·
            refine ⟨2057759582101612328355203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371839721401074885570135 2057759582101612328355203)
            ·
              refine ⟨3086639373152418492532805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057759582101612328355203 3086639373152418492532805)
              ·
                refine ⟨578744882466078467349901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3086639373152418492532805 578744882466078467349901)
                ·
                  refine ⟨217029330924779425256213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578744882466078467349901 217029330924779425256213)
                  ·
                    rfl

theorem cell20_475496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_475496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475496 prefixEnd_475496 := by exact prefixLift 475496
  have htrace : WordTrace (prefixWord ++ tailWord_475496) baseStart_475496 baseEnd_475496 := by
    simpa [prefixWord, tailWord_475496, baseEnd_475496] using wordTrace_append hprefix tailTrace_475496
  have hstable : (prefixWord ++ tailWord_475496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475496).length < 2 ^ (prefixWord ++ tailWord_475496).sum := by decide
  have hdescent : baseEnd_475496 < baseStart_475496 := by decide
  rcases family_descends (prefixWord ++ tailWord_475496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475555 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_475555 : Nat := 118140960795 + 475555 * 2 ^ 59
def prefixEnd_475555 : Nat := 4983230072969 + 3 ^ 40 * 475555 * 2
def baseEnd_475555 : Nat := 217056260132437442289305

theorem tailTrace_475555 : CollatzResearch.WordTrace tailWord_475555 prefixEnd_475555 217056260132437442289305 := by
  unfold tailWord_475555
  simp only [CollatzResearch.WordTrace]
  refine ⟨17344915792152928172988119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11563277194768618781992079 17344915792152928172988119)
  ·
    refine ⟨26017373688229392259482179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17344915792152928172988119 26017373688229392259482179)
    ·
      refine ⟨39026060532344088389223269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26017373688229392259482179 39026060532344088389223269)
      ·
        refine ⟨7317386349814516572979363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39026060532344088389223269 7317386349814516572979363)
        ·
          refine ⟨10976079524721774859469045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7317386349814516572979363 10976079524721774859469045)
          ·
            refine ⟨1029007455442666393075223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10976079524721774859469045 1029007455442666393075223)
            ·
              refine ⟨1543511183163999589612835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029007455442666393075223 1543511183163999589612835)
              ·
                refine ⟨2315266774745999384419253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543511183163999589612835 2315266774745999384419253)
                ·
                  refine ⟨217056260132437442289305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2315266774745999384419253 217056260132437442289305)
                  ·
                    rfl

theorem cell20_475555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_475555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475555 prefixEnd_475555 := by exact prefixLift 475555
  have htrace : WordTrace (prefixWord ++ tailWord_475555) baseStart_475555 baseEnd_475555 := by
    simpa [prefixWord, tailWord_475555, baseEnd_475555] using wordTrace_append hprefix tailTrace_475555
  have hstable : (prefixWord ++ tailWord_475555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475555).length < 2 ^ (prefixWord ++ tailWord_475555).sum := by decide
  have hdescent : baseEnd_475555 < baseStart_475555 := by decide
  rcases family_descends (prefixWord ++ tailWord_475555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475613 : List Nat := [1, 4, 3, 1, 1, 1, 5, 2, 2]
def baseStart_475613 : Nat := 118140960795 + 475613 * 2 ^ 59
def prefixEnd_475613 : Nat := 4983230072969 + 3 ^ 40 * 475613 * 2
def baseEnd_475613 : Nat := 217082732912847018355735

theorem tailTrace_475613 : CollatzResearch.WordTrace tailWord_475613 prefixEnd_475613 217082732912847018355735 := by
  unfold tailWord_475613
  simp only [CollatzResearch.WordTrace]
  refine ⟨17347031225942804078599493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11564687483961869385732995 17347031225942804078599493)
  ·
    refine ⟨3252568354864275764737405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17347031225942804078599493 3252568354864275764737405)
    ·
      refine ⟨1219713133074103411776527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3252568354864275764737405 1219713133074103411776527)
      ·
        refine ⟨1829569699611155117664791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219713133074103411776527 1829569699611155117664791)
        ·
          refine ⟨2744354549416732676497187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829569699611155117664791 2744354549416732676497187)
          ·
            refine ⟨4116531824125099014745781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744354549416732676497187 4116531824125099014745781)
            ·
              refine ⟨385924858511728032632417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4116531824125099014745781 385924858511728032632417)
              ·
                refine ⟨289443643883796024474313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385924858511728032632417 289443643883796024474313)
                ·
                  refine ⟨217082732912847018355735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289443643883796024474313 217082732912847018355735)
                  ·
                    rfl

theorem cell20_475613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_475613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475613 prefixEnd_475613 := by exact prefixLift 475613
  have htrace : WordTrace (prefixWord ++ tailWord_475613) baseStart_475613 baseEnd_475613 := by
    simpa [prefixWord, tailWord_475613, baseEnd_475613] using wordTrace_append hprefix tailTrace_475613
  have hstable : (prefixWord ++ tailWord_475613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475613).length < 2 ^ (prefixWord ++ tailWord_475613).sum := by decide
  have hdescent : baseEnd_475613 < baseStart_475613 := by decide
  rcases family_descends (prefixWord ++ tailWord_475613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475624 : List Nat := [2, 1, 4, 1, 1, 4, 2, 5]
def baseStart_475624 : Nat := 118140960795 + 475624 * 2 ^ 59
def prefixEnd_475624 : Nat := 4983230072969 + 3 ^ 40 * 475624 * 2
def baseEnd_475624 : Nat := 72362584537526622996341

theorem tailTrace_475624 : CollatzResearch.WordTrace tailWord_475624 prefixEnd_475624 72362584537526622996341 := by
  unfold tailWord_475624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673716214451476478624963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11564954952601968638166617 8673716214451476478624963)
  ·
    refine ⟨13010574321677214717937445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8673716214451476478624963 13010574321677214717937445)
    ·
      refine ⟨2439482685314477759613271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13010574321677214717937445 2439482685314477759613271)
      ·
        refine ⟨3659224027971716639419907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439482685314477759613271 3659224027971716639419907)
        ·
          refine ⟨5488836041957574959129861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659224027971716639419907 5488836041957574959129861)
          ·
            refine ⟨1029156757867045304836849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5488836041957574959129861 1029156757867045304836849)
            ·
              refine ⟨771867568400283978627637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029156757867045304836849 771867568400283978627637)
              ·
                refine ⟨72362584537526622996341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 771867568400283978627637 72362584537526622996341)
                ·
                  rfl

theorem cell20_475624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_475624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475624 prefixEnd_475624 := by exact prefixLift 475624
  have htrace : WordTrace (prefixWord ++ tailWord_475624) baseStart_475624 baseEnd_475624 := by
    simpa [prefixWord, tailWord_475624, baseEnd_475624] using wordTrace_append hprefix tailTrace_475624
  have hstable : (prefixWord ++ tailWord_475624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475624).length < 2 ^ (prefixWord ++ tailWord_475624).sum := by decide
  have hdescent : baseEnd_475624 < baseStart_475624 := by decide
  rcases family_descends (prefixWord ++ tailWord_475624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475645 : List Nat := [1, 4, 1, 1, 1, 3, 1, 8]
def baseStart_475645 : Nat := 118140960795 + 475645 * 2 ^ 59
def prefixEnd_475645 : Nat := 4983230072969 + 3 ^ 40 * 475645 * 2
def baseEnd_475645 : Nat := 72365779528265709762979

theorem tailTrace_475645 : CollatzResearch.WordTrace tailWord_475645 prefixEnd_475645 72365779528265709762979 := by
  unfold tailWord_475645
  simp only [CollatzResearch.WordTrace]
  refine ⟨17348198361826873543764389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11565465574551249029176259 17348198361826873543764389)
  ·
    refine ⟨3252787192842538789455823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17348198361826873543764389 3252787192842538789455823)
    ·
      refine ⟨4879180789263808184183735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252787192842538789455823 4879180789263808184183735)
      ·
        refine ⟨7318771183895712276275603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879180789263808184183735 7318771183895712276275603)
        ·
          refine ⟨10978156775843568414413405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318771183895712276275603 10978156775843568414413405)
          ·
            refine ⟨4116808790941338155405027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10978156775843568414413405 4116808790941338155405027)
            ·
              refine ⟨6175213186412007233107541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116808790941338155405027 6175213186412007233107541)
              ·
                refine ⟨72365779528265709762979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6175213186412007233107541 72365779528265709762979)
                ·
                  rfl

theorem cell20_475645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_475645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475645 prefixEnd_475645 := by exact prefixLift 475645
  have htrace : WordTrace (prefixWord ++ tailWord_475645) baseStart_475645 baseEnd_475645 := by
    simpa [prefixWord, tailWord_475645, baseEnd_475645] using wordTrace_append hprefix tailTrace_475645
  have hstable : (prefixWord ++ tailWord_475645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475645).length < 2 ^ (prefixWord ++ tailWord_475645).sum := by decide
  have hdescent : baseEnd_475645 < baseStart_475645 := by decide
  rcases family_descends (prefixWord ++ tailWord_475645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475668 : List Nat := [2, 4, 3, 1, 1, 1, 4, 2, 2]
def baseStart_475668 : Nat := 118140960795 + 475668 * 2 ^ 59
def prefixEnd_475668 : Nat := 4983230072969 + 3 ^ 40 * 475668 * 2
def baseEnd_475668 : Nat := 217107836411511271522177

theorem tailTrace_475668 : CollatzResearch.WordTrace tailWord_475668 prefixEnd_475668 217107836411511271522177 := by
  unfold tailWord_475668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674518620371774235925829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11566024827162365647901105 8674518620371774235925829)
  ·
    refine ⟨1626472241319707669236093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8674518620371774235925829 1626472241319707669236093)
    ·
      refine ⟨609927090494890375963535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1626472241319707669236093 609927090494890375963535)
      ·
        refine ⟨914890635742335563945303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609927090494890375963535 914890635742335563945303)
        ·
          refine ⟨1372335953613503345917955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914890635742335563945303 1372335953613503345917955)
          ·
            refine ⟨2058503930420255018876933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372335953613503345917955 2058503930420255018876933)
            ·
              refine ⟨385969486953797816039425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2058503930420255018876933 385969486953797816039425)
              ·
                refine ⟨289477115215348362029569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385969486953797816039425 289477115215348362029569)
                ·
                  refine ⟨217107836411511271522177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289477115215348362029569 217107836411511271522177)
                  ·
                    rfl

theorem cell20_475668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_475668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475668 prefixEnd_475668 := by exact prefixLift 475668
  have htrace : WordTrace (prefixWord ++ tailWord_475668) baseStart_475668 baseEnd_475668 := by
    simpa [prefixWord, tailWord_475668, baseEnd_475668] using wordTrace_append hprefix tailTrace_475668
  have hstable : (prefixWord ++ tailWord_475668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475668).length < 2 ^ (prefixWord ++ tailWord_475668).sum := by decide
  have hdescent : baseEnd_475668 < baseStart_475668 := by decide
  rcases family_descends (prefixWord ++ tailWord_475668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475672 : List Nat := [2, 1, 2, 3, 3, 2, 1, 4, 2]
def baseStart_475672 : Nat := 118140960795 + 475672 * 2 ^ 59
def prefixEnd_475672 : Nat := 4983230072969 + 3 ^ 40 * 475672 * 2
def baseEnd_475672 : Nat := 217109662120505035388827

theorem tailTrace_475672 : CollatzResearch.WordTrace tailWord_475672 prefixEnd_475672 217109662120505035388827 := by
  unfold tailWord_475672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674591566364528577498635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11566122088486038103331513 8674591566364528577498635)
  ·
    refine ⟨13011887349546792866247953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674591566364528577498635 13011887349546792866247953)
    ·
      refine ⟨9758915512160094649685965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13011887349546792866247953 9758915512160094649685965)
      ·
        refine ⟨3659593317060035493632237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9758915512160094649685965 3659593317060035493632237)
        ·
          refine ⟨1372347493897513310112089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3659593317060035493632237 1372347493897513310112089)
          ·
            refine ⟨1029260620423134982584067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372347493897513310112089 1029260620423134982584067)
            ·
              refine ⟨1543890930634702473876101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029260620423134982584067 1543890930634702473876101)
              ·
                refine ⟨289479549494006713851769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1543890930634702473876101 289479549494006713851769)
                ·
                  refine ⟨217109662120505035388827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289479549494006713851769 217109662120505035388827)
                  ·
                    rfl

theorem cell20_475672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_475672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475672 prefixEnd_475672 := by exact prefixLift 475672
  have htrace : WordTrace (prefixWord ++ tailWord_475672) baseStart_475672 baseEnd_475672 := by
    simpa [prefixWord, tailWord_475672, baseEnd_475672] using wordTrace_append hprefix tailTrace_475672
  have hstable : (prefixWord ++ tailWord_475672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475672).length < 2 ^ (prefixWord ++ tailWord_475672).sum := by decide
  have hdescent : baseEnd_475672 < baseStart_475672 := by decide
  rcases family_descends (prefixWord ++ tailWord_475672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475716 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 3]
def baseStart_475716 : Nat := 118140960795 + 475716 * 2 ^ 59
def prefixEnd_475716 : Nat := 4983230072969 + 3 ^ 40 * 475716 * 2
def baseEnd_475716 : Nat := 217129744919436437921981

theorem tailTrace_475716 : CollatzResearch.WordTrace tailWord_475716 prefixEnd_475716 217129744919436437921981 := by
  unfold tailWord_475716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675393972284826334799501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11567191963046435113066001 8675393972284826334799501)
  ·
    refine ⟨3253272739606809875549813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8675393972284826334799501 3253272739606809875549813)
    ·
      refine ⟨304994319338138425832795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3253272739606809875549813 304994319338138425832795)
      ·
        refine ⟨457491479007207638749193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304994319338138425832795 457491479007207638749193)
        ·
          refine ⟨343118609255405729061895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457491479007207638749193 343118609255405729061895)
          ·
            refine ⟨514677913883108593592843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343118609255405729061895 514677913883108593592843)
            ·
              refine ⟨772016870824662890389265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514677913883108593592843 772016870824662890389265)
              ·
                refine ⟨579012653118497167791949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772016870824662890389265 579012653118497167791949)
                ·
                  refine ⟨217129744919436437921981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579012653118497167791949 217129744919436437921981)
                  ·
                    rfl

theorem cell20_475716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_475716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475716 prefixEnd_475716 := by exact prefixLift 475716
  have htrace : WordTrace (prefixWord ++ tailWord_475716) baseStart_475716 baseEnd_475716 := by
    simpa [prefixWord, tailWord_475716, baseEnd_475716] using wordTrace_append hprefix tailTrace_475716
  have hstable : (prefixWord ++ tailWord_475716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475716).length < 2 ^ (prefixWord ++ tailWord_475716).sum := by decide
  have hdescent : baseEnd_475716 < baseStart_475716 := by decide
  rcases family_descends (prefixWord ++ tailWord_475716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475778 : List Nat := [3, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_475778 : Nat := 118140960795 + 475778 * 2 ^ 59
def prefixEnd_475778 : Nat := 4983230072969 + 3 ^ 40 * 475778 * 2
def baseEnd_475778 : Nat := 217158043408839777855061

theorem tailTrace_475778 : CollatzResearch.WordTrace tailWord_475778 prefixEnd_475778 217158043408839777855061 := by
  unfold tailWord_475778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338262317586259314588997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11568699513563358172237325 4338262317586259314588997)
  ·
    refine ⟨813424184547423621485437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4338262317586259314588997 813424184547423621485437)
    ·
      refine ⟨305034069205283858057039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 813424184547423621485437 305034069205283858057039)
      ·
        refine ⟨457551103807925787085559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305034069205283858057039 457551103807925787085559)
        ·
          refine ⟨686326655711888680628339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457551103807925787085559 686326655711888680628339)
          ·
            refine ⟨1029489983567833020942509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686326655711888680628339 1029489983567833020942509)
            ·
              refine ⟨386058743837937382853441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029489983567833020942509 386058743837937382853441)
              ·
                refine ⟨289544057878453037140081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386058743837937382853441 289544057878453037140081)
                ·
                  refine ⟨217158043408839777855061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289544057878453037140081 217158043408839777855061)
                  ·
                    rfl

theorem cell20_475778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_475778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475778 prefixEnd_475778 := by exact prefixLift 475778
  have htrace : WordTrace (prefixWord ++ tailWord_475778) baseStart_475778 baseEnd_475778 := by
    simpa [prefixWord, tailWord_475778, baseEnd_475778] using wordTrace_append hprefix tailTrace_475778
  have hstable : (prefixWord ++ tailWord_475778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475778).length < 2 ^ (prefixWord ++ tailWord_475778).sum := by decide
  have hdescent : baseEnd_475778 < baseStart_475778 := by decide
  rcases family_descends (prefixWord ++ tailWord_475778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475783 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 3]
def baseStart_475783 : Nat := 118140960795 + 475783 * 2 ^ 59
def prefixEnd_475783 : Nat := 4983230072969 + 3 ^ 40 * 475783 * 2
def baseEnd_475783 : Nat := 217160325545081982688373

theorem tailTrace_475783 : CollatzResearch.WordTrace tailWord_475783 prefixEnd_475783 217160325545081982688373 := by
  unfold tailWord_475783
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353231635326923112288003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11568821090217948741525335 17353231635326923112288003)
  ·
    refine ⟨26029847452990384668432005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17353231635326923112288003 26029847452990384668432005)
    ·
      refine ⟨4880596397435697125331001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26029847452990384668432005 4880596397435697125331001)
      ·
        refine ⟨3660447298076772843998251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4880596397435697125331001 3660447298076772843998251)
        ·
          refine ⟨5490670947115159265997377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660447298076772843998251 5490670947115159265997377)
          ·
            refine ⟨4118003210336369449498033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5490670947115159265997377 4118003210336369449498033)
            ·
              refine ⟨3088502407752277087123525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118003210336369449498033 3088502407752277087123525)
              ·
                refine ⟨579094201453551953835661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3088502407752277087123525 579094201453551953835661)
                ·
                  refine ⟨217160325545081982688373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579094201453551953835661 217160325545081982688373)
                  ·
                    rfl

theorem cell20_475783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_475783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475783 prefixEnd_475783 := by exact prefixLift 475783
  have htrace : WordTrace (prefixWord ++ tailWord_475783) baseStart_475783 baseEnd_475783 := by
    simpa [prefixWord, tailWord_475783, baseEnd_475783] using wordTrace_append hprefix tailTrace_475783
  have hstable : (prefixWord ++ tailWord_475783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475783).length < 2 ^ (prefixWord ++ tailWord_475783).sum := by decide
  have hdescent : baseEnd_475783 < baseStart_475783 := by decide
  rcases family_descends (prefixWord ++ tailWord_475783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475786 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_475786 : Nat := 118140960795 + 475786 * 2 ^ 59
def prefixEnd_475786 : Nat := 4983230072969 + 3 ^ 40 * 475786 * 2
def baseEnd_475786 : Nat := 217161694826827305588361

theorem tailTrace_475786 : CollatzResearch.WordTrace tailWord_475786 prefixEnd_475786 217161694826827305588361 := by
  unfold tailWord_475786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338335263579013656161803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11568894036210703083098141 4338335263579013656161803)
  ·
    refine ⟨6507502895368520484242705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4338335263579013656161803 6507502895368520484242705)
    ·
      refine ⟨4880627171526390363182029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6507502895368520484242705 4880627171526390363182029)
      ·
        refine ⟨1830235189322396386193261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4880627171526390363182029 1830235189322396386193261)
        ·
          refine ⟨686338195995898644822473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1830235189322396386193261 686338195995898644822473)
          ·
            refine ⟨514753646996923983616855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686338195995898644822473 514753646996923983616855)
            ·
              refine ⟨772130470495385975425283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514753646996923983616855 772130470495385975425283)
              ·
                refine ⟨1158195705743078963137925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772130470495385975425283 1158195705743078963137925)
                ·
                  refine ⟨217161694826827305588361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158195705743078963137925 217161694826827305588361)
                  ·
                    rfl

theorem cell20_475786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_475786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475786 prefixEnd_475786 := by exact prefixLift 475786
  have htrace : WordTrace (prefixWord ++ tailWord_475786) baseStart_475786 baseEnd_475786 := by
    simpa [prefixWord, tailWord_475786, baseEnd_475786] using wordTrace_append hprefix tailTrace_475786
  have hstable : (prefixWord ++ tailWord_475786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475786).length < 2 ^ (prefixWord ++ tailWord_475786).sum := by decide
  have hdescent : baseEnd_475786 < baseStart_475786 := by decide
  rcases family_descends (prefixWord ++ tailWord_475786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475796 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_475796 : Nat := 118140960795 + 475796 * 2 ^ 59
def prefixEnd_475796 : Nat := 4983230072969 + 3 ^ 40 * 475796 * 2
def baseEnd_475796 : Nat := 217166259099311715254987

theorem tailTrace_475796 : CollatzResearch.WordTrace tailWord_475796 prefixEnd_475796 217166259099311715254987 := by
  unfold tailWord_475796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676852892139913166255621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11569137189519884221674161 8676852892139913166255621)
  ·
    refine ⟨1626909917276233718672929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8676852892139913166255621 1626909917276233718672929)
    ·
      refine ⟨1220182437957175289004697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1626909917276233718672929 1220182437957175289004697)
      ·
        refine ⟨915136828467881466753523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1220182437957175289004697 915136828467881466753523)
        ·
          refine ⟨1372705242701822200130285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915136828467881466753523 1372705242701822200130285)
          ·
            refine ⟨514764466013183325048857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1372705242701822200130285 514764466013183325048857)
            ·
              refine ⟨386073349509887493786643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514764466013183325048857 386073349509887493786643)
              ·
                refine ⟨579110024264831240679965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386073349509887493786643 579110024264831240679965)
                ·
                  refine ⟨217166259099311715254987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579110024264831240679965 217166259099311715254987)
                  ·
                    rfl

theorem cell20_475796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_475796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475796 prefixEnd_475796 := by exact prefixLift 475796
  have htrace : WordTrace (prefixWord ++ tailWord_475796) baseStart_475796 baseEnd_475796 := by
    simpa [prefixWord, tailWord_475796, baseEnd_475796] using wordTrace_append hprefix tailTrace_475796
  have hstable : (prefixWord ++ tailWord_475796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475796).length < 2 ^ (prefixWord ++ tailWord_475796).sum := by decide
  have hdescent : baseEnd_475796 < baseStart_475796 := by decide
  rcases family_descends (prefixWord ++ tailWord_475796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475838 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_475838 : Nat := 118140960795 + 475838 * 2 ^ 59
def prefixEnd_475838 : Nat := 4983230072969 + 3 ^ 40 * 475838 * 2
def baseEnd_475838 : Nat := 217185429043746235854815

theorem tailTrace_475838 : CollatzResearch.WordTrace tailWord_475838 prefixEnd_475838 217185429043746235854815 := by
  unfold tailWord_475838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169404706265958438192521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11570158433418445003693445 2169404706265958438192521)
  ·
    refine ⟨1627053529699468828644391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2169404706265958438192521 1627053529699468828644391)
    ·
      refine ⟨2440580294549203242966587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627053529699468828644391 2440580294549203242966587)
      ·
        refine ⟨3660870441823804864449881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440580294549203242966587 3660870441823804864449881)
        ·
          refine ⟨2745652831367853648337411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3660870441823804864449881 2745652831367853648337411)
          ·
            refine ⟨4118479247051780472506117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745652831367853648337411 4118479247051780472506117)
            ·
              refine ⟨772214858822208838594897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4118479247051780472506117 772214858822208838594897)
              ·
                refine ⟨579161144116656628946173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772214858822208838594897 579161144116656628946173)
                ·
                  refine ⟨217185429043746235854815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579161144116656628946173 217185429043746235854815)
                  ·
                    rfl

theorem cell20_475838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_475838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475838 prefixEnd_475838 := by exact prefixLift 475838
  have htrace : WordTrace (prefixWord ++ tailWord_475838) baseStart_475838 baseEnd_475838 := by
    simpa [prefixWord, tailWord_475838, baseEnd_475838] using wordTrace_append hprefix tailTrace_475838
  have hstable : (prefixWord ++ tailWord_475838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475838).length < 2 ^ (prefixWord ++ tailWord_475838).sum := by decide
  have hdescent : baseEnd_475838 < baseStart_475838 := by decide
  rcases family_descends (prefixWord ++ tailWord_475838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475849 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_475849 : Nat := 118140960795 + 475849 * 2 ^ 59
def prefixEnd_475849 : Nat := 4983230072969 + 3 ^ 40 * 475849 * 2
def baseEnd_475849 : Nat := 217190449743479086488103

theorem tailTrace_475849 : CollatzResearch.WordTrace tailWord_475849 prefixEnd_475849 217190449743479086488103 := by
  unfold tailWord_475849
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355638853087816384190601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11570425902058544256127067 17355638853087816384190601)
  ·
    refine ⟨13016729139815862288142951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17355638853087816384190601 13016729139815862288142951)
    ·
      refine ⟨19525093709723793432214427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13016729139815862288142951 19525093709723793432214427)
      ·
        refine ⟨29287640564585690148321641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19525093709723793432214427 29287640564585690148321641)
        ·
          refine ⟨21965730423439267611241231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29287640564585690148321641 21965730423439267611241231)
          ·
            refine ⟨32948595635158901416861847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21965730423439267611241231 32948595635158901416861847)
            ·
              refine ⟨49422893452738352125292771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32948595635158901416861847 49422893452738352125292771)
              ·
                refine ⟨74134340179107528187939157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49422893452738352125292771 74134340179107528187939157)
                ·
                  refine ⟨217190449743479086488103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74134340179107528187939157 217190449743479086488103)
                  ·
                    rfl

theorem cell20_475849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_475849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475849 prefixEnd_475849 := by exact prefixLift 475849
  have htrace : WordTrace (prefixWord ++ tailWord_475849) baseStart_475849 baseEnd_475849 := by
    simpa [prefixWord, tailWord_475849, baseEnd_475849] using wordTrace_append hprefix tailTrace_475849
  have hstable : (prefixWord ++ tailWord_475849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475849).length < 2 ^ (prefixWord ++ tailWord_475849).sum := by decide
  have hdescent : baseEnd_475849 < baseStart_475849 := by decide
  rcases family_descends (prefixWord ++ tailWord_475849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475852 : List Nat := [2, 2, 1, 5, 1, 1, 3, 5]
def baseStart_475852 : Nat := 118140960795 + 475852 * 2 ^ 59
def prefixEnd_475852 : Nat := 4983230072969 + 3 ^ 40 * 475852 * 2
def baseEnd_475852 : Nat := 72397273008408136462697

theorem tailTrace_475852 : CollatzResearch.WordTrace tailWord_475852 prefixEnd_475852 72397273008408136462697 := by
  unfold tailWord_475852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677874136038473948274905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11570498848051298597699873 8677874136038473948274905)
  ·
    refine ⟨6508405602028855461206179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8677874136038473948274905 6508405602028855461206179)
    ·
      refine ⟨9762608403043283191809269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508405602028855461206179 9762608403043283191809269)
      ·
        refine ⟨915244537785307799232119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9762608403043283191809269 915244537785307799232119)
        ·
          refine ⟨1372866806677961698848179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915244537785307799232119 1372866806677961698848179)
          ·
            refine ⟨2059300210016942548272269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372866806677961698848179 2059300210016942548272269)
            ·
              refine ⟨772237578756353455602101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2059300210016942548272269 772237578756353455602101)
              ·
                refine ⟨72397273008408136462697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 772237578756353455602101 72397273008408136462697)
                ·
                  rfl

theorem cell20_475852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_475852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475852 prefixEnd_475852 := by exact prefixLift 475852
  have htrace : WordTrace (prefixWord ++ tailWord_475852) baseStart_475852 baseEnd_475852 := by
    simpa [prefixWord, tailWord_475852, baseEnd_475852] using wordTrace_append hprefix tailTrace_475852
  have hstable : (prefixWord ++ tailWord_475852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475852).length < 2 ^ (prefixWord ++ tailWord_475852).sum := by decide
  have hdescent : baseEnd_475852 < baseStart_475852 := by decide
  rcases family_descends (prefixWord ++ tailWord_475852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475866 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_475866 : Nat := 118140960795 + 475866 * 2 ^ 59
def prefixEnd_475866 : Nat := 4983230072969 + 3 ^ 40 * 475866 * 2
def baseEnd_475866 : Nat := 217198209006702582921367

theorem tailTrace_475866 : CollatzResearch.WordTrace tailWord_475866 prefixEnd_475866 217198209006702582921367 := by
  unfold tailWord_475866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339064723506557071889863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11570839262684152191706301 4339064723506557071889863)
  ·
    refine ⟨6508597085259835607834795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4339064723506557071889863 6508597085259835607834795)
    ·
      refine ⟨9762895627889753411752193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508597085259835607834795 9762895627889753411752193)
      ·
        refine ⟨7322171720917315058814145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9762895627889753411752193 7322171720917315058814145)
        ·
          refine ⟨5491628790687986294110609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7322171720917315058814145 5491628790687986294110609)
          ·
            refine ⟨4118721593015989720582957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5491628790687986294110609 4118721593015989720582957)
            ·
              refine ⟨1544520597380996145218609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4118721593015989720582957 1544520597380996145218609)
              ·
                refine ⟨1158390448035747108913957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544520597380996145218609 1158390448035747108913957)
                ·
                  refine ⟨217198209006702582921367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158390448035747108913957 217198209006702582921367)
                  ·
                    rfl

theorem cell20_475866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_475866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475866 prefixEnd_475866 := by exact prefixLift 475866
  have htrace : WordTrace (prefixWord ++ tailWord_475866) baseStart_475866 baseEnd_475866 := by
    simpa [prefixWord, tailWord_475866, baseEnd_475866] using wordTrace_append hprefix tailTrace_475866
  have hstable : (prefixWord ++ tailWord_475866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475866).length < 2 ^ (prefixWord ++ tailWord_475866).sum := by decide
  have hdescent : baseEnd_475866 < baseStart_475866 := by decide
  rcases family_descends (prefixWord ++ tailWord_475866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475914 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_475914 : Nat := 118140960795 + 475914 * 2 ^ 59
def prefixEnd_475914 : Nat := 4983230072969 + 3 ^ 40 * 475914 * 2
def baseEnd_475914 : Nat := 217220117514627749321171

theorem tailTrace_475914 : CollatzResearch.WordTrace tailWord_475914 prefixEnd_475914 217220117514627749321171 := by
  unfold tailWord_475914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339502399463083121326699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11572006398568221656871197 4339502399463083121326699)
  ·
    refine ⟨6509253599194624681990049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4339502399463083121326699 6509253599194624681990049)
    ·
      refine ⟨4881940199395968511492537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6509253599194624681990049 4881940199395968511492537)
      ·
        refine ⟨3661455149546976383619403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4881940199395968511492537 3661455149546976383619403)
        ·
          refine ⟨5492182724320464575429105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661455149546976383619403 5492182724320464575429105)
          ·
            refine ⟨4119137043240348431571829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492182724320464575429105 4119137043240348431571829)
            ·
              refine ⟨386169097803782665459859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4119137043240348431571829 386169097803782665459859)
              ·
                refine ⟨579253646705673998189789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386169097803782665459859 579253646705673998189789)
                ·
                  refine ⟨217220117514627749321171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579253646705673998189789 217220117514627749321171)
                  ·
                    rfl

theorem cell20_475914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_475914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475914 prefixEnd_475914 := by exact prefixLift 475914
  have htrace : WordTrace (prefixWord ++ tailWord_475914) baseStart_475914 baseEnd_475914 := by
    simpa [prefixWord, tailWord_475914, baseEnd_475914] using wordTrace_append hprefix tailTrace_475914
  have hstable : (prefixWord ++ tailWord_475914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475914).length < 2 ^ (prefixWord ++ tailWord_475914).sum := by decide
  have hdescent : baseEnd_475914 < baseStart_475914 := by decide
  rcases family_descends (prefixWord ++ tailWord_475914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475938 : List Nat := [3, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_475938 : Nat := 118140960795 + 475938 * 2 ^ 59
def prefixEnd_475938 : Nat := 4983230072969 + 3 ^ 40 * 475938 * 2
def baseEnd_475938 : Nat := 217231071768590332521073

theorem tailTrace_475938 : CollatzResearch.WordTrace tailWord_475938 prefixEnd_475938 217231071768590332521073 := by
  unfold tailWord_475938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339721237441346146045117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11572589966510256389453645 4339721237441346146045117)
  ·
    refine ⟨1627395464040504804766919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4339721237441346146045117 1627395464040504804766919)
    ·
      refine ⟨2441093196060757207150379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627395464040504804766919 2441093196060757207150379)
      ·
        refine ⟨3661639794091135810725569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441093196060757207150379 3661639794091135810725569)
        ·
          refine ⟨2746229845568351858044177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3661639794091135810725569 2746229845568351858044177)
          ·
            refine ⟨2059672384176263893533133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746229845568351858044177 2059672384176263893533133)
            ·
              refine ⟨772377144066098960074925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2059672384176263893533133 772377144066098960074925)
              ·
                refine ⟨289641429024787110028097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 772377144066098960074925 289641429024787110028097)
                ·
                  refine ⟨217231071768590332521073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289641429024787110028097 217231071768590332521073)
                  ·
                    rfl

theorem cell20_475938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_475938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475938 prefixEnd_475938 := by exact prefixLift 475938
  have htrace : WordTrace (prefixWord ++ tailWord_475938) baseStart_475938 baseEnd_475938 := by
    simpa [prefixWord, tailWord_475938, baseEnd_475938] using wordTrace_append hprefix tailTrace_475938
  have hstable : (prefixWord ++ tailWord_475938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475938).length < 2 ^ (prefixWord ++ tailWord_475938).sum := by decide
  have hdescent : baseEnd_475938 < baseStart_475938 := by decide
  rcases family_descends (prefixWord ++ tailWord_475938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475969 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 3]
def baseStart_475969 : Nat := 118140960795 + 475969 * 2 ^ 59
def prefixEnd_475969 : Nat := 4983230072969 + 3 ^ 40 * 475969 * 2
def baseEnd_475969 : Nat := 217245221013292002487613

theorem tailTrace_475969 : CollatzResearch.WordTrace tailWord_475969 prefixEnd_475969 217245221013292002487613 := by
  unfold tailWord_475969
  simp only [CollatzResearch.WordTrace]
  refine ⟨17360015612653076878558961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11573343741768717919039307 17360015612653076878558961)
  ·
    refine ⟨13020011709489807658919221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17360015612653076878558961 13020011709489807658919221)
    ·
      refine ⟨1220626097764669468023677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13020011709489807658919221 1220626097764669468023677)
      ·
        refine ⟨457734786661751050508879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1220626097764669468023677 457734786661751050508879)
        ·
          refine ⟨686602179992626575763319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457734786661751050508879 686602179992626575763319)
          ·
            refine ⟨1029903269988939863644979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686602179992626575763319 1029903269988939863644979)
            ·
              refine ⟨1544854904983409795467469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029903269988939863644979 1544854904983409795467469)
              ·
                refine ⟨579320589368778673300301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1544854904983409795467469 579320589368778673300301)
                ·
                  refine ⟨217245221013292002487613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579320589368778673300301 217245221013292002487613)
                  ·
                    rfl

theorem cell20_475969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_475969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475969 prefixEnd_475969 := by exact prefixLift 475969
  have htrace : WordTrace (prefixWord ++ tailWord_475969) baseStart_475969 baseEnd_475969 := by
    simpa [prefixWord, tailWord_475969, baseEnd_475969] using wordTrace_append hprefix tailTrace_475969
  have hstable : (prefixWord ++ tailWord_475969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475969).length < 2 ^ (prefixWord ++ tailWord_475969).sum := by decide
  have hdescent : baseEnd_475969 < baseStart_475969 := by decide
  rcases family_descends (prefixWord ++ tailWord_475969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476001 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_476001 : Nat := 118140960795 + 476001 * 2 ^ 59
def prefixEnd_476001 : Nat := 4983230072969 + 3 ^ 40 * 476001 * 2
def baseEnd_476001 : Nat := 217259826685242113420815

theorem tailTrace_476001 : CollatzResearch.WordTrace tailWord_476001 prefixEnd_476001 217259826685242113420815 := by
  unfold tailWord_476001
  simp only [CollatzResearch.WordTrace]
  refine ⟨17361182748537146343723857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11574121832358097562482571 17361182748537146343723857)
  ·
    refine ⟨13020887061402859757792893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17361182748537146343723857 13020887061402859757792893)
    ·
      refine ⟨4882832648026072409172335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13020887061402859757792893 4882832648026072409172335)
      ·
        refine ⟨7324248972039108613758503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882832648026072409172335 7324248972039108613758503)
        ·
          refine ⟨10986373458058662920637755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324248972039108613758503 10986373458058662920637755)
          ·
            refine ⟨16479560187087994380956633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10986373458058662920637755 16479560187087994380956633)
            ·
              refine ⟨12359670140315995785717475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16479560187087994380956633 12359670140315995785717475)
              ·
                refine ⟨18539505210473993678576213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12359670140315995785717475 18539505210473993678576213)
                ·
                  refine ⟨217259826685242113420815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18539505210473993678576213 217259826685242113420815)
                  ·
                    rfl

theorem cell20_476001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_476001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476001 prefixEnd_476001 := by exact prefixLift 476001
  have htrace : WordTrace (prefixWord ++ tailWord_476001) baseStart_476001 baseEnd_476001 := by
    simpa [prefixWord, tailWord_476001, baseEnd_476001] using wordTrace_append hprefix tailTrace_476001
  have hstable : (prefixWord ++ tailWord_476001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476001).length < 2 ^ (prefixWord ++ tailWord_476001).sum := by decide
  have hdescent : baseEnd_476001 < baseStart_476001 := by decide
  rcases family_descends (prefixWord ++ tailWord_476001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476025 : List Nat := [1, 2, 1, 3, 2, 3, 3, 5]
def baseStart_476025 : Nat := 118140960795 + 476025 * 2 ^ 59
def prefixEnd_476025 : Nat := 4983230072969 + 3 ^ 40 * 476025 * 2
def baseEnd_476025 : Nat := 72423593646401565540239

theorem tailTrace_476025 : CollatzResearch.WordTrace tailWord_476025 prefixEnd_476025 72423593646401565540239 := by
  unfold tailWord_476025
  simp only [CollatzResearch.WordTrace]
  refine ⟨17362058100450198442597529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11574705400300132295065019 17362058100450198442597529)
  ·
    refine ⟨13021543575337648831948147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17362058100450198442597529 13021543575337648831948147)
    ·
      refine ⟨19532315363006473247922221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13021543575337648831948147 19532315363006473247922221)
      ·
        refine ⟨7324618261127427467970833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19532315363006473247922221 7324618261127427467970833)
        ·
          refine ⟨5493463695845570600978125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7324618261127427467970833 5493463695845570600978125)
          ·
            refine ⟨2060048885942088975366797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5493463695845570600978125 2060048885942088975366797)
            ·
              refine ⟨772518332228283365762549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2060048885942088975366797 772518332228283365762549)
              ·
                refine ⟨72423593646401565540239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 772518332228283365762549 72423593646401565540239)
                ·
                  rfl

theorem cell20_476025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_476025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476025 prefixEnd_476025 := by exact prefixLift 476025
  have htrace : WordTrace (prefixWord ++ tailWord_476025) baseStart_476025 baseEnd_476025 := by
    simpa [prefixWord, tailWord_476025, baseEnd_476025] using wordTrace_append hprefix tailTrace_476025
  have hstable : (prefixWord ++ tailWord_476025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476025).length < 2 ^ (prefixWord ++ tailWord_476025).sum := by decide
  have hdescent : baseEnd_476025 < baseStart_476025 := by decide
  rcases family_descends (prefixWord ++ tailWord_476025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476052 : List Nat := [2, 4, 2, 1, 1, 1, 4, 3, 2]
def baseStart_476052 : Nat := 118140960795 + 476052 * 2 ^ 59
def prefixEnd_476052 : Nat := 4983230072969 + 3 ^ 40 * 476052 * 2
def baseEnd_476052 : Nat := 217283104474912602720607

theorem tailTrace_476052 : CollatzResearch.WordTrace tailWord_476052 prefixEnd_476052 217283104474912602720607 := by
  unfold tailWord_476052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681521435676191026915205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11575361914234921369220273 8681521435676191026915205)
  ·
    refine ⟨1627785269189285817546601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8681521435676191026915205 1627785269189285817546601)
    ·
      refine ⟨1220838951891964363159951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1627785269189285817546601 1220838951891964363159951)
      ·
        refine ⟨1831258427837946544739927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220838951891964363159951 1831258427837946544739927)
        ·
          refine ⟨2746887641756919817109891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831258427837946544739927 2746887641756919817109891)
          ·
            refine ⟨4120331462635379725664837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746887641756919817109891 4120331462635379725664837)
            ·
              refine ⟨772562149244133698562157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4120331462635379725664837 772562149244133698562157)
              ·
                refine ⟨289710805966550136960809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 772562149244133698562157 289710805966550136960809)
                ·
                  refine ⟨217283104474912602720607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289710805966550136960809 217283104474912602720607)
                  ·
                    rfl

theorem cell20_476052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_476052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476052 prefixEnd_476052 := by exact prefixLift 476052
  have htrace : WordTrace (prefixWord ++ tailWord_476052) baseStart_476052 baseEnd_476052 := by
    simpa [prefixWord, tailWord_476052, baseEnd_476052] using wordTrace_append hprefix tailTrace_476052
  have hstable : (prefixWord ++ tailWord_476052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476052).length < 2 ^ (prefixWord ++ tailWord_476052).sum := by decide
  have hdescent : baseEnd_476052 < baseStart_476052 := by decide
  rcases family_descends (prefixWord ++ tailWord_476052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476063 : List Nat := [1, 1, 2, 5, 2, 2, 7]
def baseStart_476063 : Nat := 118140960795 + 476063 * 2 ^ 59
def prefixEnd_476063 : Nat := 4983230072969 + 3 ^ 40 * 476063 * 2
def baseEnd_476063 : Nat := 24143125019405050372655

theorem tailTrace_476063 : CollatzResearch.WordTrace tailWord_476063 prefixEnd_476063 24143125019405050372655 := by
  unfold tailWord_476063
  simp only [CollatzResearch.WordTrace]
  refine ⟨17363444074312530932480843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11575629382875020621653895 17363444074312530932480843)
  ·
    refine ⟨26045166111468796398721265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17363444074312530932480843 26045166111468796398721265)
    ·
      refine ⟨19533874583601597299040949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26045166111468796398721265 19533874583601597299040949)
      ·
        refine ⟨1831300742212649746785089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19533874583601597299040949 1831300742212649746785089)
        ·
          refine ⟨1373475556659487310088817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831300742212649746785089 1373475556659487310088817)
          ·
            refine ⟨1030106667494615482566613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373475556659487310088817 1030106667494615482566613)
            ·
              refine ⟨24143125019405050372655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1030106667494615482566613 24143125019405050372655)
              ·
                rfl

theorem cell20_476063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_476063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476063 prefixEnd_476063 := by exact prefixLift 476063
  have htrace : WordTrace (prefixWord ++ tailWord_476063) baseStart_476063 baseEnd_476063 := by
    simpa [prefixWord, tailWord_476063, baseEnd_476063] using wordTrace_append hprefix tailTrace_476063
  have hstable : (prefixWord ++ tailWord_476063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476063).length < 2 ^ (prefixWord ++ tailWord_476063).sum := by decide
  have hdescent : baseEnd_476063 < baseStart_476063 := by decide
  rcases family_descends (prefixWord ++ tailWord_476063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476066 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_476066 : Nat := 118140960795 + 476066 * 2 ^ 59
def prefixEnd_476066 : Nat := 4983230072969 + 3 ^ 40 * 476066 * 2
def baseEnd_476066 : Nat := 217289494456390776253883

theorem tailTrace_476066 : CollatzResearch.WordTrace tailWord_476066 prefixEnd_476066 217289494456390776253883 := by
  unfold tailWord_476066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340888373325415611210013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11575702328867774963226701 4340888373325415611210013)
  ·
    refine ⟨1627833139997030854203755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4340888373325415611210013 1627833139997030854203755)
    ·
      refine ⟨2441749709995546281305633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627833139997030854203755 2441749709995546281305633)
      ·
        refine ⟨1831312282496659710979225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441749709995546281305633 1831312282496659710979225)
        ·
          refine ⟨1373484211872494783234419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831312282496659710979225 1373484211872494783234419)
          ·
            refine ⟨2060226317808742174851629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373484211872494783234419 2060226317808742174851629)
            ·
              refine ⟨772584869178278315569361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2060226317808742174851629 772584869178278315569361)
              ·
                refine ⟨579438651883708736677021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772584869178278315569361 579438651883708736677021)
                ·
                  refine ⟨217289494456390776253883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579438651883708736677021 217289494456390776253883)
                  ·
                    rfl

theorem cell20_476066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_476066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476066 prefixEnd_476066 := by exact prefixLift 476066
  have htrace : WordTrace (prefixWord ++ tailWord_476066) baseStart_476066 baseEnd_476066 := by
    simpa [prefixWord, tailWord_476066, baseEnd_476066] using wordTrace_append hprefix tailTrace_476066
  have hstable : (prefixWord ++ tailWord_476066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476066).length < 2 ^ (prefixWord ++ tailWord_476066).sum := by decide
  have hdescent : baseEnd_476066 < baseStart_476066 := by decide
  rcases family_descends (prefixWord ++ tailWord_476066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476094 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_476094 : Nat := 118140960795 + 476094 * 2 ^ 59
def prefixEnd_476094 : Nat := 4983230072969 + 3 ^ 40 * 476094 * 2
def baseEnd_476094 : Nat := 217302274419347123320435

theorem tailTrace_476094 : CollatzResearch.WordTrace tailWord_476094 prefixEnd_476094 217302274419347123320435 := by
  unfold tailWord_476094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170571842150027903357417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11576383158133482151239557 2170571842150027903357417)
  ·
    refine ⟨1627928881612520927518063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2170571842150027903357417 1627928881612520927518063)
    ·
      refine ⟨2441893322418781391277095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627928881612520927518063 2441893322418781391277095)
      ·
        refine ⟨3662839983628172086915643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441893322418781391277095 3662839983628172086915643)
        ·
          refine ⟨5494259975442258130373465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3662839983628172086915643 5494259975442258130373465)
          ·
            refine ⟨4120694981581693597780099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5494259975442258130373465 4120694981581693597780099)
            ·
              refine ⟨6181042472372540396670149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120694981581693597780099 6181042472372540396670149)
              ·
                refine ⟨1158945463569851324375653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6181042472372540396670149 1158945463569851324375653)
                ·
                  refine ⟨217302274419347123320435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1158945463569851324375653 217302274419347123320435)
                  ·
                    rfl

theorem cell20_476094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_476094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476094 prefixEnd_476094 := by exact prefixLift 476094
  have htrace : WordTrace (prefixWord ++ tailWord_476094) baseStart_476094 baseEnd_476094 := by
    simpa [prefixWord, tailWord_476094, baseEnd_476094] using wordTrace_append hprefix tailTrace_476094
  have hstable : (prefixWord ++ tailWord_476094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476094).length < 2 ^ (prefixWord ++ tailWord_476094).sum := by decide
  have hdescent : baseEnd_476094 < baseStart_476094 := by decide
  rcases family_descends (prefixWord ++ tailWord_476094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476108 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_476108 : Nat := 118140960795 + 476108 * 2 ^ 59
def prefixEnd_476108 : Nat := 4983230072969 + 3 ^ 40 * 476108 * 2
def baseEnd_476108 : Nat := 217308664400825296853711

theorem tailTrace_476108 : CollatzResearch.WordTrace tailWord_476108 prefixEnd_476108 217308664400825296853711 := by
  unfold tailWord_476108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682542679574751808934489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11576723572766335745245985 8682542679574751808934489)
  ·
    refine ⟨6511907009681063856700867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8682542679574751808934489 6511907009681063856700867)
    ·
      refine ⟨9767860514521595785051301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511907009681063856700867 9767860514521595785051301)
      ·
        refine ⟨1831473846472799209697119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9767860514521595785051301 1831473846472799209697119)
        ·
          refine ⟨2747210769709198814545679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831473846472799209697119 2747210769709198814545679)
          ·
            refine ⟨4120816154563798221818519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747210769709198814545679 4120816154563798221818519)
            ·
              refine ⟨6181224231845697332727779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120816154563798221818519 6181224231845697332727779)
              ·
                refine ⟨9271836347768545999091669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181224231845697332727779 9271836347768545999091669)
                ·
                  refine ⟨217308664400825296853711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9271836347768545999091669 217308664400825296853711)
                  ·
                    rfl

theorem cell20_476108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_476108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476108 prefixEnd_476108 := by exact prefixLift 476108
  have htrace : WordTrace (prefixWord ++ tailWord_476108) baseStart_476108 baseEnd_476108 := by
    simpa [prefixWord, tailWord_476108, baseEnd_476108] using wordTrace_append hprefix tailTrace_476108
  have hstable : (prefixWord ++ tailWord_476108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476108).length < 2 ^ (prefixWord ++ tailWord_476108).sum := by decide
  have hdescent : baseEnd_476108 < baseStart_476108 := by decide
  rcases family_descends (prefixWord ++ tailWord_476108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476111 : List Nat := [1, 1, 2, 1, 1, 6, 3, 3, 2]
def baseStart_476111 : Nat := 118140960795 + 476111 * 2 ^ 59
def prefixEnd_476111 : Nat := 4983230072969 + 3 ^ 40 * 476111 * 2
def baseEnd_476111 : Nat := 217310033682570619753699

theorem tailTrace_476111 : CollatzResearch.WordTrace tailWord_476111 prefixEnd_476111 217310033682570619753699 := by
  unfold tailWord_476111
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365194778138635130228187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11576796518759090086818791 17365194778138635130228187)
  ·
    refine ⟨26047792167207952695342281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17365194778138635130228187 26047792167207952695342281)
    ·
      refine ⟨19535844125405964521506711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26047792167207952695342281 19535844125405964521506711)
      ·
        refine ⟨29303766188108946782260067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535844125405964521506711 29303766188108946782260067)
        ·
          refine ⟨43955649282163420173390101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29303766188108946782260067 43955649282163420173390101)
          ·
            refine ⟨2060421060101410320627661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43955649282163420173390101 2060421060101410320627661)
            ·
              refine ⟨772657897538028870235373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2060421060101410320627661 772657897538028870235373)
              ·
                refine ⟨289746711576760826338265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 772657897538028870235373 289746711576760826338265)
                ·
                  refine ⟨217310033682570619753699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289746711576760826338265 217310033682570619753699)
                  ·
                    rfl

theorem cell20_476111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 2].length) (baseStart_476111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476111 prefixEnd_476111 := by exact prefixLift 476111
  have htrace : WordTrace (prefixWord ++ tailWord_476111) baseStart_476111 baseEnd_476111 := by
    simpa [prefixWord, tailWord_476111, baseEnd_476111] using wordTrace_append hprefix tailTrace_476111
  have hstable : (prefixWord ++ tailWord_476111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476111).length < 2 ^ (prefixWord ++ tailWord_476111).sum := by decide
  have hdescent : baseEnd_476111 < baseStart_476111 := by decide
  rcases family_descends (prefixWord ++ tailWord_476111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476118 : List Nat := [5, 2, 1, 1, 2, 1, 8]
def baseStart_476118 : Nat := 118140960795 + 476118 * 2 ^ 59
def prefixEnd_476118 : Nat := 4983230072969 + 3 ^ 40 * 476118 * 2
def baseEnd_476118 : Nat := 24145914297034411835593

theorem tailTrace_476118 : CollatzResearch.WordTrace tailWord_476118 prefixEnd_476118 24145914297034411835593 := by
  unfold tailWord_476118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085340630569579707858313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11576966726075516883822005 1085340630569579707858313)
  ·
    refine ⟨814005472927184780893735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1085340630569579707858313 814005472927184780893735)
    ·
      refine ⟨1221008209390777171340603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814005472927184780893735 1221008209390777171340603)
      ·
        refine ⟨1831512314086165757010905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221008209390777171340603 1831512314086165757010905)
        ·
          refine ⟨1373634235564624317758179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831512314086165757010905 1373634235564624317758179)
          ·
            refine ⟨2060451353346936476637269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373634235564624317758179 2060451353346936476637269)
            ·
              refine ⟨24145914297034411835593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2060451353346936476637269 24145914297034411835593)
              ·
                rfl

theorem cell20_476118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 8].length) (baseStart_476118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476118 prefixEnd_476118 := by exact prefixLift 476118
  have htrace : WordTrace (prefixWord ++ tailWord_476118) baseStart_476118 baseEnd_476118 := by
    simpa [prefixWord, tailWord_476118, baseEnd_476118] using wordTrace_append hprefix tailTrace_476118
  have hstable : (prefixWord ++ tailWord_476118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476118).length < 2 ^ (prefixWord ++ tailWord_476118).sum := by decide
  have hdescent : baseEnd_476118 < baseStart_476118 := by decide
  rcases family_descends (prefixWord ++ tailWord_476118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476125 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_476125 : Nat := 118140960795 + 476125 * 2 ^ 59
def prefixEnd_476125 : Nat := 4983230072969 + 3 ^ 40 * 476125 * 2
def baseEnd_476125 : Nat := 217316423664048793286975

theorem tailTrace_476125 : CollatzResearch.WordTrace tailWord_476125 prefixEnd_476125 217316423664048793286975 := by
  unfold tailWord_476125
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365705400087915521237829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11577136933391943680825219 17365705400087915521237829)
  ·
    refine ⟨3256069762516484160232093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17365705400087915521237829 3256069762516484160232093)
    ·
      refine ⟨1221026160943681560087035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3256069762516484160232093 1221026160943681560087035)
      ·
        refine ⟨1831539241415522340130553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221026160943681560087035 1831539241415522340130553)
        ·
          refine ⟨1373654431061641755097915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1831539241415522340130553 1373654431061641755097915)
          ·
            refine ⟨2060481646592462632646873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373654431061641755097915 2060481646592462632646873)
            ·
              refine ⟨1545361234944346974485155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060481646592462632646873 1545361234944346974485155)
              ·
                refine ⟨2318041852416520461727733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545361234944346974485155 2318041852416520461727733)
                ·
                  refine ⟨217316423664048793286975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2318041852416520461727733 217316423664048793286975)
                  ·
                    rfl

theorem cell20_476125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_476125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476125 prefixEnd_476125 := by exact prefixLift 476125
  have htrace : WordTrace (prefixWord ++ tailWord_476125) baseStart_476125 baseEnd_476125 := by
    simpa [prefixWord, tailWord_476125, baseEnd_476125] using wordTrace_append hprefix tailTrace_476125
  have hstable : (prefixWord ++ tailWord_476125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476125).length < 2 ^ (prefixWord ++ tailWord_476125).sum := by decide
  have hdescent : baseEnd_476125 < baseStart_476125 := by decide
  rcases family_descends (prefixWord ++ tailWord_476125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476142 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_476142 : Nat := 118140960795 + 476142 * 2 ^ 59
def prefixEnd_476142 : Nat := 4983230072969 + 3 ^ 40 * 476142 * 2
def baseEnd_476142 : Nat := 217324182927272289720239

theorem tailTrace_476142 : CollatzResearch.WordTrace tailWord_476142 prefixEnd_476142 217324182927272289720239 := by
  unfold tailWord_476142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170790680128290928075835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11577550294017551616404453 2170790680128290928075835)
  ·
    refine ⟨3256186020192436392113753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170790680128290928075835 3256186020192436392113753)
    ·
      refine ⟨2442139515144327294085315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3256186020192436392113753 2442139515144327294085315)
      ·
        refine ⟨3663209272716490941127973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442139515144327294085315 3663209272716490941127973)
        ·
          refine ⟨686851738634342051461495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3663209272716490941127973 686851738634342051461495)
          ·
            refine ⟨1030277607951513077192243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686851738634342051461495 1030277607951513077192243)
            ·
              refine ⟨1545416411927269615788365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030277607951513077192243 1545416411927269615788365)
              ·
                refine ⟨579531154472726105920637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545416411927269615788365 579531154472726105920637)
                ·
                  refine ⟨217324182927272289720239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579531154472726105920637 217324182927272289720239)
                  ·
                    rfl

theorem cell20_476142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_476142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476142 prefixEnd_476142 := by exact prefixLift 476142
  have htrace : WordTrace (prefixWord ++ tailWord_476142) baseStart_476142 baseEnd_476142 := by
    simpa [prefixWord, tailWord_476142, baseEnd_476142] using wordTrace_append hprefix tailTrace_476142
  have hstable : (prefixWord ++ tailWord_476142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476142).length < 2 ^ (prefixWord ++ tailWord_476142).sum := by decide
  have hdescent : baseEnd_476142 < baseStart_476142 := by decide
  rcases family_descends (prefixWord ++ tailWord_476142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476153 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_476153 : Nat := 118140960795 + 476153 * 2 ^ 59
def prefixEnd_476153 : Nat := 4983230072969 + 3 ^ 40 * 476153 * 2
def baseEnd_476153 : Nat := 217329203627005140353527

theorem tailTrace_476153 : CollatzResearch.WordTrace tailWord_476153 prefixEnd_476153 217329203627005140353527 := by
  unfold tailWord_476153
  simp only [CollatzResearch.WordTrace]
  refine ⟨17366726643986476303257113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11577817762657650868838075 17366726643986476303257113)
  ·
    refine ⟨13025044982989857227442835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17366726643986476303257113 13025044982989857227442835)
    ·
      refine ⟨19537567474484785841164253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13025044982989857227442835 19537567474484785841164253)
      ·
        refine ⟨7326587802931794690436595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19537567474484785841164253 7326587802931794690436595)
        ·
          refine ⟨10989881704397692035654893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326587802931794690436595 10989881704397692035654893)
          ·
            refine ⟨4121205639149134513370585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10989881704397692035654893 4121205639149134513370585)
            ·
              refine ⟨3090904229361850885027939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4121205639149134513370585 3090904229361850885027939)
              ·
                refine ⟨4636356344042776327541909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090904229361850885027939 4636356344042776327541909)
                ·
                  refine ⟨217329203627005140353527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4636356344042776327541909 217329203627005140353527)
                  ·
                    rfl

theorem cell20_476153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_476153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476153 prefixEnd_476153 := by exact prefixLift 476153
  have htrace : WordTrace (prefixWord ++ tailWord_476153) baseStart_476153 baseEnd_476153 := by
    simpa [prefixWord, tailWord_476153, baseEnd_476153] using wordTrace_append hprefix tailTrace_476153
  have hstable : (prefixWord ++ tailWord_476153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476153).length < 2 ^ (prefixWord ++ tailWord_476153).sum := by decide
  have hdescent : baseEnd_476153 < baseStart_476153 := by decide
  rcases family_descends (prefixWord ++ tailWord_476153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476183 : List Nat := [1, 1, 3, 5, 1, 3, 2, 2, 2]
def baseStart_476183 : Nat := 118140960795 + 476183 * 2 ^ 59
def prefixEnd_476183 : Nat := 4983230072969 + 3 ^ 40 * 476183 * 2
def baseEnd_476183 : Nat := 217342896444458369353405

theorem tailTrace_476183 : CollatzResearch.WordTrace tailWord_476183 prefixEnd_476183 217342896444458369353405 := by
  unfold tailWord_476183
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367820833877791426849203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11578547222585194284566135 17367820833877791426849203)
  ·
    refine ⟨26051731250816687140273805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17367820833877791426849203 26051731250816687140273805)
    ·
      refine ⟨9769399219056257677602677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26051731250816687140273805 9769399219056257677602677)
      ·
        refine ⟨915881176786524157275251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9769399219056257677602677 915881176786524157275251)
        ·
          refine ⟨1373821765179786235912877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915881176786524157275251 1373821765179786235912877)
          ·
            refine ⟨515183161942419838467329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1373821765179786235912877 515183161942419838467329)
            ·
              refine ⟨386387371456814878850497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515183161942419838467329 386387371456814878850497)
              ·
                refine ⟨289790528592611159137873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386387371456814878850497 289790528592611159137873)
                ·
                  refine ⟨217342896444458369353405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289790528592611159137873 217342896444458369353405)
                  ·
                    rfl

theorem cell20_476183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 2].length) (baseStart_476183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476183 prefixEnd_476183 := by exact prefixLift 476183
  have htrace : WordTrace (prefixWord ++ tailWord_476183) baseStart_476183 baseEnd_476183 := by
    simpa [prefixWord, tailWord_476183, baseEnd_476183] using wordTrace_append hprefix tailTrace_476183
  have hstable : (prefixWord ++ tailWord_476183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476183).length < 2 ^ (prefixWord ++ tailWord_476183).sum := by decide
  have hdescent : baseEnd_476183 < baseStart_476183 := by decide
  rcases family_descends (prefixWord ++ tailWord_476183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476194 : List Nat := [3, 3, 1, 1, 1, 5, 1, 5]
def baseStart_476194 : Nat := 118140960795 + 476194 * 2 ^ 59
def prefixEnd_476194 : Nat := 4983230072969 + 3 ^ 40 * 476194 * 2
def baseEnd_476194 : Nat := 72449305714730406662231

theorem tailTrace_476194 : CollatzResearch.WordTrace tailWord_476194 prefixEnd_476194 72449305714730406662231 := by
  unfold tailWord_476194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4342055509209485076374909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11578814691225293536999757 4342055509209485076374909)
  ·
    refine ⟨1628270815953556903640591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4342055509209485076374909 1628270815953556903640591)
    ·
      refine ⟨2442406223930335355460887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628270815953556903640591 2442406223930335355460887)
      ·
        refine ⟨3663609335895503033191331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442406223930335355460887 3663609335895503033191331)
        ·
          refine ⟨5495414003843254549786997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663609335895503033191331 5495414003843254549786997)
          ·
            refine ⟨515195062860305114042531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5495414003843254549786997 515195062860305114042531)
            ·
              refine ⟨772792594290457671063797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515195062860305114042531 772792594290457671063797)
              ·
                refine ⟨72449305714730406662231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 772792594290457671063797 72449305714730406662231)
                ·
                  rfl

theorem cell20_476194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_476194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476194 prefixEnd_476194 := by exact prefixLift 476194
  have htrace : WordTrace (prefixWord ++ tailWord_476194) baseStart_476194 baseEnd_476194 := by
    simpa [prefixWord, tailWord_476194, baseEnd_476194] using wordTrace_append hprefix tailTrace_476194
  have hstable : (prefixWord ++ tailWord_476194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476194).length < 2 ^ (prefixWord ++ tailWord_476194).sum := by decide
  have hdescent : baseEnd_476194 < baseStart_476194 := by decide
  rcases family_descends (prefixWord ++ tailWord_476194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476270 : List Nat := [4, 1, 2, 2, 1, 2, 4, 4]
def baseStart_476270 : Nat := 118140960795 + 476270 * 2 ^ 59
def prefixEnd_476270 : Nat := 4983230072969 + 3 ^ 40 * 476270 * 2
def baseEnd_476270 : Nat := 72460868538357577817683

theorem tailTrace_476270 : CollatzResearch.WordTrace tailWord_476270 prefixEnd_476270 72460868538357577817683 := by
  unfold tailWord_476270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171374248070325660658283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11580662656375070190177509 2171374248070325660658283)
  ·
    refine ⟨3257061372105488490987425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2171374248070325660658283 3257061372105488490987425)
    ·
      refine ⟨2442796029079116368240569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3257061372105488490987425 2442796029079116368240569)
      ·
        refine ⟨1832097021809337276180427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2442796029079116368240569 1832097021809337276180427)
        ·
          refine ⟨2748145532714005914270641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832097021809337276180427 2748145532714005914270641)
          ·
            refine ⟨2061109149535504435702981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748145532714005914270641 2061109149535504435702981)
            ·
              refine ⟨386457965537907081694309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2061109149535504435702981 386457965537907081694309)
              ·
                refine ⟨72460868538357577817683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386457965537907081694309 72460868538357577817683)
                ·
                  rfl

theorem cell20_476270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_476270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476270 prefixEnd_476270 := by exact prefixLift 476270
  have htrace : WordTrace (prefixWord ++ tailWord_476270) baseStart_476270 baseEnd_476270 := by
    simpa [prefixWord, tailWord_476270, baseEnd_476270] using wordTrace_append hprefix tailTrace_476270
  have hstable : (prefixWord ++ tailWord_476270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476270).length < 2 ^ (prefixWord ++ tailWord_476270).sum := by decide
  have hdescent : baseEnd_476270 < baseStart_476270 := by decide
  rcases family_descends (prefixWord ++ tailWord_476270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476298 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_476298 : Nat := 118140960795 + 476298 * 2 ^ 59
def prefixEnd_476298 : Nat := 4983230072969 + 3 ^ 40 * 476298 * 2
def baseEnd_476298 : Nat := 217395385578029080519601

theorem tailTrace_476298 : CollatzResearch.WordTrace tailWord_476298 prefixEnd_476298 217395385578029080519601 := by
  unfold tailWord_476298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4343003807115291516821387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11581343485640777378190365 4343003807115291516821387)
  ·
    refine ⟨6514505710672937275232081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4343003807115291516821387 6514505710672937275232081)
    ·
      refine ⟨4885879283004702956424061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6514505710672937275232081 4885879283004702956424061)
      ·
        refine ⟨1832204731126763608659023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4885879283004702956424061 1832204731126763608659023)
        ·
          refine ⟨2748307096690145412988535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832204731126763608659023 2748307096690145412988535)
          ·
            refine ⟨4122460645035218119482803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748307096690145412988535 4122460645035218119482803)
            ·
              refine ⟨6183690967552827179224205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122460645035218119482803 6183690967552827179224205)
              ·
                refine ⟨2318884112832310192209077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6183690967552827179224205 2318884112832310192209077)
                ·
                  refine ⟨217395385578029080519601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2318884112832310192209077 217395385578029080519601)
                  ·
                    rfl

theorem cell20_476298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_476298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476298 prefixEnd_476298 := by exact prefixLift 476298
  have htrace : WordTrace (prefixWord ++ tailWord_476298) baseStart_476298 baseEnd_476298 := by
    simpa [prefixWord, tailWord_476298, baseEnd_476298] using wordTrace_append hprefix tailTrace_476298
  have hstable : (prefixWord ++ tailWord_476298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476298).length < 2 ^ (prefixWord ++ tailWord_476298).sum := by decide
  have hdescent : baseEnd_476298 < baseStart_476298 := by decide
  rcases family_descends (prefixWord ++ tailWord_476298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476356 : List Nat := [2, 3, 3, 1, 3, 1, 1, 4, 2]
def baseStart_476356 : Nat := 118140960795 + 476356 * 2 ^ 59
def prefixEnd_476356 : Nat := 4983230072969 + 3 ^ 40 * 476356 * 2
def baseEnd_476356 : Nat := 217421858358438656586031

theorem tailTrace_476356 : CollatzResearch.WordTrace tailWord_476356 prefixEnd_476356 217421858358438656586031 := by
  unfold tailWord_476356
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687065331125520986448461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11582753774834027981931281 8687065331125520986448461)
  ·
    refine ⟨3257649499172070369918173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8687065331125520986448461 3257649499172070369918173)
    ·
      refine ⟨1221618562189526388719315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3257649499172070369918173 1221618562189526388719315)
      ·
        refine ⟨1832427843284289583078973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221618562189526388719315 1832427843284289583078973)
        ·
          refine ⟨687160441231608593654615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1832427843284289583078973 687160441231608593654615)
          ·
            refine ⟨1030740661847412890481923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687160441231608593654615 1030740661847412890481923)
            ·
              refine ⟨1546110992771119335722885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030740661847412890481923 1546110992771119335722885)
              ·
                refine ⟨289895811144584875448041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1546110992771119335722885 289895811144584875448041)
                ·
                  refine ⟨217421858358438656586031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289895811144584875448041 217421858358438656586031)
                  ·
                    rfl

theorem cell20_476356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_476356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476356 prefixEnd_476356 := by exact prefixLift 476356
  have htrace : WordTrace (prefixWord ++ tailWord_476356) baseStart_476356 baseEnd_476356 := by
    simpa [prefixWord, tailWord_476356, baseEnd_476356] using wordTrace_append hprefix tailTrace_476356
  have hstable : (prefixWord ++ tailWord_476356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476356).length < 2 ^ (prefixWord ++ tailWord_476356).sum := by decide
  have hdescent : baseEnd_476356 < baseStart_476356 := by decide
  rcases family_descends (prefixWord ++ tailWord_476356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476388 : List Nat := [2, 3, 1, 1, 1, 2, 2, 8]
def baseStart_476388 : Nat := 118140960795 + 476388 * 2 ^ 59
def prefixEnd_476388 : Nat := 4983230072969 + 3 ^ 40 * 476388 * 2
def baseEnd_476388 : Nat := 72478821343462922506411

theorem tailTrace_476388 : CollatzResearch.WordTrace tailWord_476388 prefixEnd_476388 72478821343462922506411 := by
  unfold tailWord_476388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687648899067555719030909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11583531865423407625374545 8687648899067555719030909)
  ·
    refine ⟨3257868337150333394636591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8687648899067555719030909 3257868337150333394636591)
    ·
      refine ⟨4886802505725500091954887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257868337150333394636591 4886802505725500091954887)
      ·
        refine ⟨7330203758588250137932331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886802505725500091954887 7330203758588250137932331)
        ·
          refine ⟨10995305637882375206898497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330203758588250137932331 10995305637882375206898497)
          ·
            refine ⟨8246479228411781405173873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10995305637882375206898497 8246479228411781405173873)
            ·
              refine ⟨6184859421308836053880405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8246479228411781405173873 6184859421308836053880405)
              ·
                refine ⟨72478821343462922506411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6184859421308836053880405 72478821343462922506411)
                ·
                  rfl

theorem cell20_476388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_476388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476388 prefixEnd_476388 := by exact prefixLift 476388
  have htrace : WordTrace (prefixWord ++ tailWord_476388) baseStart_476388 baseEnd_476388 := by
    simpa [prefixWord, tailWord_476388, baseEnd_476388] using wordTrace_append hprefix tailTrace_476388
  have hstable : (prefixWord ++ tailWord_476388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476388).length < 2 ^ (prefixWord ++ tailWord_476388).sum := by decide
  have hdescent : baseEnd_476388 < baseStart_476388 := by decide
  rcases family_descends (prefixWord ++ tailWord_476388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476419 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_476419 : Nat := 118140960795 + 476419 * 2 ^ 59
def prefixEnd_476419 : Nat := 4983230072969 + 3 ^ 40 * 476419 * 2
def baseEnd_476419 : Nat := 217450613275090437485773

theorem tailTrace_476419 : CollatzResearch.WordTrace tailWord_476419 prefixEnd_476419 217450613275090437485773 := by
  unfold tailWord_476419
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376428461022803732440311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11584285640681869154960207 17376428461022803732440311)
  ·
    refine ⟨26064642691534205598660467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17376428461022803732440311 26064642691534205598660467)
    ·
      refine ⟨39096964037301308397990701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26064642691534205598660467 39096964037301308397990701)
      ·
        refine ⟨14661361513987990649246513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39096964037301308397990701 14661361513987990649246513)
        ·
          refine ⟨10996021135490992986934885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14661361513987990649246513 10996021135490992986934885)
          ·
            refine ⟨2061753962904561185050291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10996021135490992986934885 2061753962904561185050291)
            ·
              refine ⟨3092630944356841777575437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061753962904561185050291 3092630944356841777575437)
              ·
                refine ⟨1159736604133815666590789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3092630944356841777575437 1159736604133815666590789)
                ·
                  refine ⟨217450613275090437485773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1159736604133815666590789 217450613275090437485773)
                  ·
                    rfl

theorem cell20_476419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_476419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476419 prefixEnd_476419 := by exact prefixLift 476419
  have htrace : WordTrace (prefixWord ++ tailWord_476419) baseStart_476419 baseEnd_476419 := by
    simpa [prefixWord, tailWord_476419, baseEnd_476419] using wordTrace_append hprefix tailTrace_476419
  have hstable : (prefixWord ++ tailWord_476419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476419).length < 2 ^ (prefixWord ++ tailWord_476419).sum := by decide
  have hdescent : baseEnd_476419 < baseStart_476419 := by decide
  rcases family_descends (prefixWord ++ tailWord_476419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476426 : List Nat := [3, 1, 2, 2, 1, 1, 1, 9]
def baseStart_476426 : Nat := 118140960795 + 476426 * 2 ^ 59
def prefixEnd_476426 : Nat := 4983230072969 + 3 ^ 40 * 476426 * 2
def baseEnd_476426 : Nat := 72484602755276508084137

theorem tailTrace_476426 : CollatzResearch.WordTrace tailWord_476426 prefixEnd_476426 72484602755276508084137 := by
  unfold tailWord_476426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344170942999360981986283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11584455847998295951963421 4344170942999360981986283)
  ·
    refine ⟨6516256414499041472979425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4344170942999360981986283 6516256414499041472979425)
    ·
      refine ⟨4887192310874281104734569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6516256414499041472979425 4887192310874281104734569)
      ·
        refine ⟨3665394233155710828550927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4887192310874281104734569 3665394233155710828550927)
        ·
          refine ⟨5498091349733566242826391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665394233155710828550927 5498091349733566242826391)
          ·
            refine ⟨8247137024600349364239587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5498091349733566242826391 8247137024600349364239587)
            ·
              refine ⟨12370705536900524046359381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247137024600349364239587 12370705536900524046359381)
              ·
                refine ⟨72484602755276508084137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12370705536900524046359381 72484602755276508084137)
                ·
                  rfl

theorem cell20_476426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_476426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476426 prefixEnd_476426 := by exact prefixLift 476426
  have htrace : WordTrace (prefixWord ++ tailWord_476426) baseStart_476426 baseEnd_476426 := by
    simpa [prefixWord, tailWord_476426, baseEnd_476426] using wordTrace_append hprefix tailTrace_476426
  have hstable : (prefixWord ++ tailWord_476426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476426).length < 2 ^ (prefixWord ++ tailWord_476426).sum := by decide
  have hdescent : baseEnd_476426 < baseStart_476426 := by decide
  rcases family_descends (prefixWord ++ tailWord_476426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476453 : List Nat := [1, 3, 1, 2, 4, 1, 3, 3, 2]
def baseStart_476453 : Nat := 118140960795 + 476453 * 2 ^ 59
def prefixEnd_476453 : Nat := 4983230072969 + 3 ^ 40 * 476453 * 2
def baseEnd_476453 : Nat := 217466131801537430352301

theorem tailTrace_476453 : CollatzResearch.WordTrace tailWord_476453 prefixEnd_476453 217466131801537430352301 := by
  unfold tailWord_476453
  simp only [CollatzResearch.WordTrace]
  refine ⟨17377668542899627539178013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11585112361933085026118675 17377668542899627539178013)
  ·
    refine ⟨6516625703587360327191755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17377668542899627539178013 6516625703587360327191755)
    ·
      refine ⟨9774938555381040490787633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516625703587360327191755 9774938555381040490787633)
      ·
        refine ⟨7331203916535780368090725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9774938555381040490787633 7331203916535780368090725)
        ·
          refine ⟨1374600734350458819017011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7331203916535780368090725 1374600734350458819017011)
          ·
            refine ⟨2061901101525688228525517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374600734350458819017011 2061901101525688228525517)
            ·
              refine ⟨773212913072133085697069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2061901101525688228525517 773212913072133085697069)
              ·
                refine ⟨289954842402049907136401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773212913072133085697069 289954842402049907136401)
                ·
                  refine ⟨217466131801537430352301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289954842402049907136401 217466131801537430352301)
                  ·
                    rfl

theorem cell20_476453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_476453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476453 prefixEnd_476453 := by exact prefixLift 476453
  have htrace : WordTrace (prefixWord ++ tailWord_476453) baseStart_476453 baseEnd_476453 := by
    simpa [prefixWord, tailWord_476453, baseEnd_476453] using wordTrace_append hprefix tailTrace_476453
  have hstable : (prefixWord ++ tailWord_476453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476453).length < 2 ^ (prefixWord ++ tailWord_476453).sum := by decide
  have hdescent : baseEnd_476453 < baseStart_476453 := by decide
  rcases family_descends (prefixWord ++ tailWord_476453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476481 : List Nat := [1, 2, 5, 2, 1, 1, 1, 7]
def baseStart_476481 : Nat := 118140960795 + 476481 * 2 ^ 59
def prefixEnd_476481 : Nat := 4983230072969 + 3 ^ 40 * 476481 * 2
def baseEnd_476481 : Nat := 72492970588164592472951

theorem tailTrace_476481 : CollatzResearch.WordTrace tailWord_476481 prefixEnd_476481 72492970588164592472951 := by
  unfold tailWord_476481
  simp only [CollatzResearch.WordTrace]
  refine ⟨17378689786798188321197297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11585793191198792214131531 17378689786798188321197297)
  ·
    refine ⟨13034017340098641240897973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17378689786798188321197297 13034017340098641240897973)
    ·
      refine ⟨1221939125634247616334185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13034017340098641240897973 1221939125634247616334185)
      ·
        refine ⟨916454344225685712250639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1221939125634247616334185 916454344225685712250639)
        ·
          refine ⟨1374681516338528568375959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916454344225685712250639 1374681516338528568375959)
          ·
            refine ⟨2062022274507792852563939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374681516338528568375959 2062022274507792852563939)
            ·
              refine ⟨3093033411761689278845909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062022274507792852563939 3093033411761689278845909)
              ·
                refine ⟨72492970588164592472951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3093033411761689278845909 72492970588164592472951)
                ·
                  rfl

theorem cell20_476481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_476481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476481 prefixEnd_476481 := by exact prefixLift 476481
  have htrace : WordTrace (prefixWord ++ tailWord_476481) baseStart_476481 baseEnd_476481 := by
    simpa [prefixWord, tailWord_476481, baseEnd_476481] using wordTrace_append hprefix tailTrace_476481
  have hstable : (prefixWord ++ tailWord_476481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476481).length < 2 ^ (prefixWord ++ tailWord_476481).sum := by decide
  have hdescent : baseEnd_476481 < baseStart_476481 := by decide
  rcases family_descends (prefixWord ++ tailWord_476481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476484 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_476484 : Nat := 118140960795 + 476484 * 2 ^ 59
def prefixEnd_476484 : Nat := 4983230072969 + 3 ^ 40 * 476484 * 2
def baseEnd_476484 : Nat := 217480281046239100318841

theorem tailTrace_476484 : CollatzResearch.WordTrace tailWord_476484 prefixEnd_476484 217480281046239100318841 := by
  unfold tailWord_476484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8689399602893659916778253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11585866137191546555704337 8689399602893659916778253)
  ·
    refine ⟨3258524851085122468791845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8689399602893659916778253 3258524851085122468791845)
    ·
      refine ⟨610973409578460462898471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3258524851085122468791845 610973409578460462898471)
      ·
        refine ⟨916460114367690694347707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610973409578460462898471 916460114367690694347707)
        ·
          refine ⟨1374690171551536041521561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916460114367690694347707 1374690171551536041521561)
          ·
            refine ⟨1031017628663652031141171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374690171551536041521561 1031017628663652031141171)
            ·
              refine ⟨1546526442995478046711757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031017628663652031141171 1546526442995478046711757)
              ·
                refine ⟨579947416123304267516909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1546526442995478046711757 579947416123304267516909)
                ·
                  refine ⟨217480281046239100318841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579947416123304267516909 217480281046239100318841)
                  ·
                    rfl

theorem cell20_476484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_476484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476484 prefixEnd_476484 := by exact prefixLift 476484
  have htrace : WordTrace (prefixWord ++ tailWord_476484) baseStart_476484 baseEnd_476484 := by
    simpa [prefixWord, tailWord_476484, baseEnd_476484] using wordTrace_append hprefix tailTrace_476484
  have hstable : (prefixWord ++ tailWord_476484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476484).length < 2 ^ (prefixWord ++ tailWord_476484).sum := by decide
  have hdescent : baseEnd_476484 < baseStart_476484 := by decide
  rcases family_descends (prefixWord ++ tailWord_476484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476519 : List Nat := [1, 1, 5, 1, 5, 7]
def baseStart_476519 : Nat := 118140960795 + 476519 * 2 ^ 59
def prefixEnd_476519 : Nat := 4983230072969 + 3 ^ 40 * 476519 * 2
def baseEnd_476519 : Nat := 8055416888886464227853

theorem tailTrace_476519 : CollatzResearch.WordTrace tailWord_476519 prefixEnd_476519 8055416888886464227853 := by
  unfold tailWord_476519
  simp only [CollatzResearch.WordTrace]
  refine ⟨17380075760660520811080611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11586717173773680540720407 17380075760660520811080611)
  ·
    refine ⟨26070113640990781216620917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17380075760660520811080611 26070113640990781216620917)
    ·
      refine ⟨2444073153842885739058211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26070113640990781216620917 2444073153842885739058211)
      ·
        refine ⟨3666109730764328608587317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444073153842885739058211 3666109730764328608587317)
        ·
          refine ⟨343697787259155807055061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3666109730764328608587317 343697787259155807055061)
          ·
            refine ⟨8055416888886464227853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 343697787259155807055061 8055416888886464227853)
            ·
              rfl

theorem cell20_476519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 7].length) (baseStart_476519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476519 prefixEnd_476519 := by exact prefixLift 476519
  have htrace : WordTrace (prefixWord ++ tailWord_476519) baseStart_476519 baseEnd_476519 := by
    simpa [prefixWord, tailWord_476519, baseEnd_476519] using wordTrace_append hprefix tailTrace_476519
  have hstable : (prefixWord ++ tailWord_476519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476519).length < 2 ^ (prefixWord ++ tailWord_476519).sum := by decide
  have hdescent : baseEnd_476519 < baseStart_476519 := by decide
  rcases family_descends (prefixWord ++ tailWord_476519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476522 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_476522 : Nat := 118140960795 + 476522 * 2 ^ 59
def prefixEnd_476522 : Nat := 4983230072969 + 3 ^ 40 * 476522 * 2
def baseEnd_476522 : Nat := 217497625281679857052019

theorem tailTrace_476522 : CollatzResearch.WordTrace tailWord_476522 prefixEnd_476522 217497625281679857052019 := by
  unfold tailWord_476522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345046294912413080859955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11586790119766434882293213 4345046294912413080859955)
  ·
    refine ⟨6517569442368619621289933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4345046294912413080859955 6517569442368619621289933)
    ·
      refine ⟨2444088540888232357983725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6517569442368619621289933 2444088540888232357983725)
      ·
        refine ⟨916533202833087134243897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2444088540888232357983725 916533202833087134243897)
        ·
          refine ⟨687399902124815350682923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 916533202833087134243897 687399902124815350682923)
          ·
            refine ⟨1031099853187223026024385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687399902124815350682923 1031099853187223026024385)
            ·
              refine ⟨773324889890417269518289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031099853187223026024385 773324889890417269518289)
              ·
                refine ⟨579993667417812952138717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773324889890417269518289 579993667417812952138717)
                ·
                  refine ⟨217497625281679857052019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579993667417812952138717 217497625281679857052019)
                  ·
                    rfl

theorem cell20_476522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_476522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476522 prefixEnd_476522 := by exact prefixLift 476522
  have htrace : WordTrace (prefixWord ++ tailWord_476522) baseStart_476522 baseEnd_476522 := by
    simpa [prefixWord, tailWord_476522, baseEnd_476522] using wordTrace_append hprefix tailTrace_476522
  have hstable : (prefixWord ++ tailWord_476522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476522).length < 2 ^ (prefixWord ++ tailWord_476522).sum := by decide
  have hdescent : baseEnd_476522 < baseStart_476522 := by decide
  rcases family_descends (prefixWord ++ tailWord_476522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476529 : List Nat := [1, 2, 2, 2, 1, 2, 6, 2, 2]
def baseStart_476529 : Nat := 118140960795 + 476529 * 2 ^ 59
def prefixEnd_476529 : Nat := 4983230072969 + 3 ^ 40 * 476529 * 2
def baseEnd_476529 : Nat := 217500820272418943818657

theorem tailTrace_476529 : CollatzResearch.WordTrace tailWord_476529 prefixEnd_476529 217500820272418943818657 := by
  unfold tailWord_476529
  simp only [CollatzResearch.WordTrace]
  refine ⟨17380440490624292518944641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11586960327082861679296427 17380440490624292518944641)
  ·
    refine ⟨13035330367968219389208481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17380440490624292518944641 13035330367968219389208481)
    ·
      refine ⟨9776497775976164541906361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13035330367968219389208481 9776497775976164541906361)
      ·
        refine ⟨7332373331982123406429771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9776497775976164541906361 7332373331982123406429771)
        ·
          refine ⟨10998559997973185109644657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332373331982123406429771 10998559997973185109644657)
          ·
            refine ⟨8248919998479888832233493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998559997973185109644657 8248919998479888832233493)
            ·
              refine ⟨386668124928744789010945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8248919998479888832233493 386668124928744789010945)
              ·
                refine ⟨290001093696558591758209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386668124928744789010945 290001093696558591758209)
                ·
                  refine ⟨217500820272418943818657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290001093696558591758209 217500820272418943818657)
                  ·
                    rfl

theorem cell20_476529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_476529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476529 prefixEnd_476529 := by exact prefixLift 476529
  have htrace : WordTrace (prefixWord ++ tailWord_476529) baseStart_476529 baseEnd_476529 := by
    simpa [prefixWord, tailWord_476529, baseEnd_476529] using wordTrace_append hprefix tailTrace_476529
  have hstable : (prefixWord ++ tailWord_476529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476529).length < 2 ^ (prefixWord ++ tailWord_476529).sum := by decide
  have hdescent : baseEnd_476529 < baseStart_476529 := by decide
  rcases family_descends (prefixWord ++ tailWord_476529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476574 : List Nat := [4, 3, 1, 2, 2, 1, 7]
def baseStart_476574 : Nat := 118140960795 + 476574 * 2 ^ 59
def prefixEnd_476574 : Nat := 4983230072969 + 3 ^ 40 * 476574 * 2
def baseEnd_476574 : Nat := 24169039944288754146497

theorem tailTrace_476574 : CollatzResearch.WordTrace tailWord_476574 prefixEnd_476574 24169039944288754146497 := by
  unfold tailWord_476574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172760221932658150541597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11588054516974176802888517 2172760221932658150541597)
  ·
    refine ⟨814785083224746806453099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2172760221932658150541597 814785083224746806453099)
    ·
      refine ⟨1222177624837120209679649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814785083224746806453099 1222177624837120209679649)
      ·
        refine ⟨916633218627840157259737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1222177624837120209679649 916633218627840157259737)
        ·
          refine ⟨687474913970880117944803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 916633218627840157259737 687474913970880117944803)
          ·
            refine ⟨1031212370956320176917205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687474913970880117944803 1031212370956320176917205)
            ·
              refine ⟨24169039944288754146497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1031212370956320176917205 24169039944288754146497)
              ·
                rfl

theorem cell20_476574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 7].length) (baseStart_476574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476574 prefixEnd_476574 := by exact prefixLift 476574
  have htrace : WordTrace (prefixWord ++ tailWord_476574) baseStart_476574 baseEnd_476574 := by
    simpa [prefixWord, tailWord_476574, baseEnd_476574] using wordTrace_append hprefix tailTrace_476574
  have hstable : (prefixWord ++ tailWord_476574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476574).length < 2 ^ (prefixWord ++ tailWord_476574).sum := by decide
  have hdescent : baseEnd_476574 < baseStart_476574 := by decide
  rcases family_descends (prefixWord ++ tailWord_476574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476588 : List Nat := [2, 2, 1, 1, 1, 1, 6, 4, 2]
def baseStart_476588 : Nat := 118140960795 + 476588 * 2 ^ 59
def prefixEnd_476588 : Nat := 4983230072969 + 3 ^ 40 * 476588 * 2
def baseEnd_476588 : Nat := 217527749480076960851749

theorem tailTrace_476588 : CollatzResearch.WordTrace tailWord_476588 prefixEnd_476588 217527749480076960851749 := by
  unfold tailWord_476588
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691296198705272797671209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11588394931607030396894945 8691296198705272797671209)
  ·
    refine ⟨6518472149028954598253407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8691296198705272797671209 6518472149028954598253407)
    ·
      refine ⟨9777708223543431897380111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6518472149028954598253407 9777708223543431897380111)
      ·
        refine ⟨14666562335315147846070167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9777708223543431897380111 14666562335315147846070167)
        ·
          refine ⟨21999843502972721769105251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14666562335315147846070167 21999843502972721769105251)
          ·
            refine ⟨32999765254459082653657877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21999843502972721769105251 32999765254459082653657877)
            ·
              refine ⟨1546863996302769499390213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32999765254459082653657877 1546863996302769499390213)
              ·
                refine ⟨290036999306769281135665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1546863996302769499390213 290036999306769281135665)
                ·
                  refine ⟨217527749480076960851749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290036999306769281135665 217527749480076960851749)
                  ·
                    rfl

theorem cell20_476588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_476588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476588 prefixEnd_476588 := by exact prefixLift 476588
  have htrace : WordTrace (prefixWord ++ tailWord_476588) baseStart_476588 baseEnd_476588 := by
    simpa [prefixWord, tailWord_476588, baseEnd_476588] using wordTrace_append hprefix tailTrace_476588
  have hstable : (prefixWord ++ tailWord_476588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476588).length < 2 ^ (prefixWord ++ tailWord_476588).sum := by decide
  have hdescent : baseEnd_476588 < baseStart_476588 := by decide
  rcases family_descends (prefixWord ++ tailWord_476588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476612 : List Nat := [2, 3, 3, 2, 1, 1, 4, 4]
def baseStart_476612 : Nat := 118140960795 + 476612 * 2 ^ 59
def prefixEnd_476612 : Nat := 4983230072969 + 3 ^ 40 * 476612 * 2
def baseEnd_476612 : Nat := 72512901244679848017217

theorem tailTrace_476612 : CollatzResearch.WordTrace tailWord_476612 prefixEnd_476612 72512901244679848017217 := by
  unfold tailWord_476612
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691733874661798847108045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11588978499549065129477393 8691733874661798847108045)
  ·
    refine ⟨3259400202998174567665517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8691733874661798847108045 3259400202998174567665517)
    ·
      refine ⟨1222275076124315462874569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3259400202998174567665517 1222275076124315462874569)
      ·
        refine ⟨916706307093236597155927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1222275076124315462874569 916706307093236597155927)
        ·
          refine ⟨1375059460639854895733891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916706307093236597155927 1375059460639854895733891)
          ·
            refine ⟨2062589190959782343600837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375059460639854895733891 2062589190959782343600837)
            ·
              refine ⟨386735473304959189425157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2062589190959782343600837 386735473304959189425157)
              ·
                refine ⟨72512901244679848017217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386735473304959189425157 72512901244679848017217)
                ·
                  rfl

theorem cell20_476612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_476612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476612 prefixEnd_476612 := by exact prefixLift 476612
  have htrace : WordTrace (prefixWord ++ tailWord_476612) baseStart_476612 baseEnd_476612 := by
    simpa [prefixWord, tailWord_476612, baseEnd_476612] using wordTrace_append hprefix tailTrace_476612
  have hstable : (prefixWord ++ tailWord_476612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476612).length < 2 ^ (prefixWord ++ tailWord_476612).sum := by decide
  have hdescent : baseEnd_476612 < baseStart_476612 := by decide
  rcases family_descends (prefixWord ++ tailWord_476612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476616 : List Nat := [2, 1, 3, 1, 3, 1, 3, 6]
def baseStart_476616 : Nat := 118140960795 + 476616 * 2 ^ 59
def prefixEnd_476616 : Nat := 4983230072969 + 3 ^ 40 * 476616 * 2
def baseEnd_476616 : Nat := 72513509814344435972767

theorem tailTrace_476616 : CollatzResearch.WordTrace tailWord_476616 prefixEnd_476616 72513509814344435972767 := by
  unfold tailWord_476616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691806820654553188680851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11589075760872737584907801 8691806820654553188680851)
  ·
    refine ⟨13037710230981829783021277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8691806820654553188680851 13037710230981829783021277)
    ·
      refine ⟨4889141336618186168632979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13037710230981829783021277 4889141336618186168632979)
      ·
        refine ⟨7333712004927279252949469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889141336618186168632979 7333712004927279252949469)
        ·
          refine ⟨2750142001847729719856051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7333712004927279252949469 2750142001847729719856051)
          ·
            refine ⟨4125213002771594579784077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750142001847729719856051 4125213002771594579784077)
            ·
              refine ⟨1546954876039347967419029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4125213002771594579784077 1546954876039347967419029)
              ·
                refine ⟨72513509814344435972767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1546954876039347967419029 72513509814344435972767)
                ·
                  rfl

theorem cell20_476616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_476616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476616 prefixEnd_476616 := by exact prefixLift 476616
  have htrace : WordTrace (prefixWord ++ tailWord_476616) baseStart_476616 baseEnd_476616 := by
    simpa [prefixWord, tailWord_476616, baseEnd_476616] using wordTrace_append hprefix tailTrace_476616
  have hstable : (prefixWord ++ tailWord_476616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476616).length < 2 ^ (prefixWord ++ tailWord_476616).sum := by decide
  have hdescent : baseEnd_476616 < baseStart_476616 := by decide
  rcases family_descends (prefixWord ++ tailWord_476616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476623 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_476623 : Nat := 118140960795 + 476623 * 2 ^ 59
def prefixEnd_476623 : Nat := 4983230072969 + 3 ^ 40 * 476623 * 2
def baseEnd_476623 : Nat := 217543724433772394684939

theorem tailTrace_476623 : CollatzResearch.WordTrace tailWord_476623 prefixEnd_476623 217543724433772394684939 := by
  unfold tailWord_476623
  simp only [CollatzResearch.WordTrace]
  refine ⟨17383868952283746572866523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11589245968189164381911015 17383868952283746572866523)
  ·
    refine ⟨26075803428425619859299785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17383868952283746572866523 26075803428425619859299785)
    ·
      refine ⟨19556852571319214894474839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26075803428425619859299785 19556852571319214894474839)
      ·
        refine ⟨29335278856978822341712259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19556852571319214894474839 29335278856978822341712259)
        ·
          refine ⟨44002918285468233512568389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29335278856978822341712259 44002918285468233512568389)
          ·
            refine ⟨8250547178525293783606573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44002918285468233512568389 8250547178525293783606573)
            ·
              refine ⟨3093955191946985168852465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8250547178525293783606573 3093955191946985168852465)
              ·
                refine ⟨2320466393960238876639349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3093955191946985168852465 2320466393960238876639349)
                ·
                  refine ⟨217543724433772394684939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2320466393960238876639349 217543724433772394684939)
                  ·
                    rfl

theorem cell20_476623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_476623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476623 prefixEnd_476623 := by exact prefixLift 476623
  have htrace : WordTrace (prefixWord ++ tailWord_476623) baseStart_476623 baseEnd_476623 := by
    simpa [prefixWord, tailWord_476623, baseEnd_476623] using wordTrace_append hprefix tailTrace_476623
  have hstable : (prefixWord ++ tailWord_476623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476623).length < 2 ^ (prefixWord ++ tailWord_476623).sum := by decide
  have hdescent : baseEnd_476623 < baseStart_476623 := by decide
  rcases family_descends (prefixWord ++ tailWord_476623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476653 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 3]
def baseStart_476653 : Nat := 118140960795 + 476653 * 2 ^ 59
def prefixEnd_476653 : Nat := 4983230072969 + 3 ^ 40 * 476653 * 2
def baseEnd_476653 : Nat := 217557417251225623684817

theorem tailTrace_476653 : CollatzResearch.WordTrace tailWord_476653 prefixEnd_476653 217557417251225623684817 := by
  unfold tailWord_476653
  simp only [CollatzResearch.WordTrace]
  refine ⟨17384963142175061696458613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11589975428116707797639075 17384963142175061696458613)
  ·
    refine ⟨1629840294578912034042995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17384963142175061696458613 1629840294578912034042995)
    ·
      refine ⟨2444760441868368051064493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629840294578912034042995 2444760441868368051064493)
      ·
        refine ⟨916785165700638019149185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2444760441868368051064493 916785165700638019149185)
        ·
          refine ⟨687588874275478514361889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 916785165700638019149185 687588874275478514361889)
          ·
            refine ⟨515691655706608885771417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687588874275478514361889 515691655706608885771417)
            ·
              refine ⟨386768741779956664328563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515691655706608885771417 386768741779956664328563)
              ·
                refine ⟨580153112669934996492845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386768741779956664328563 580153112669934996492845)
                ·
                  refine ⟨217557417251225623684817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580153112669934996492845 217557417251225623684817)
                  ·
                    rfl

theorem cell20_476653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_476653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476653 prefixEnd_476653 := by exact prefixLift 476653
  have htrace : WordTrace (prefixWord ++ tailWord_476653) baseStart_476653 baseEnd_476653 := by
    simpa [prefixWord, tailWord_476653, baseEnd_476653] using wordTrace_append hprefix tailTrace_476653
  have hstable : (prefixWord ++ tailWord_476653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476653).length < 2 ^ (prefixWord ++ tailWord_476653).sum := by decide
  have hdescent : baseEnd_476653 < baseStart_476653 := by decide
  rcases family_descends (prefixWord ++ tailWord_476653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476657 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 3]
def baseStart_476657 : Nat := 118140960795 + 476657 * 2 ^ 59
def prefixEnd_476657 : Nat := 4983230072969 + 3 ^ 40 * 476657 * 2
def baseEnd_476657 : Nat := 217559242960219387551467

theorem tailTrace_476657 : CollatzResearch.WordTrace tailWord_476657 prefixEnd_476657 217559242960219387551467 := by
  unfold tailWord_476657
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385109034160570379604225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11590072689440380253069483 17385109034160570379604225)
  ·
    refine ⟨13038831775620427784703169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17385109034160570379604225 13038831775620427784703169)
    ·
      refine ⟨9779123831715320838527377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13038831775620427784703169 9779123831715320838527377)
      ·
        refine ⟨7334342873786490628895533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9779123831715320838527377 7334342873786490628895533)
        ·
          refine ⟨2750378577669933985835825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7334342873786490628895533 2750378577669933985835825)
          ·
            refine ⟨2062783933252450489376869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750378577669933985835825 2062783933252450489376869)
            ·
              refine ⟨386771987484834466758163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2062783933252450489376869 386771987484834466758163)
              ·
                refine ⟨580157981227251700137245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386771987484834466758163 580157981227251700137245)
                ·
                  refine ⟨217559242960219387551467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580157981227251700137245 217559242960219387551467)
                  ·
                    rfl

theorem cell20_476657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_476657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476657 prefixEnd_476657 := by exact prefixLift 476657
  have htrace : WordTrace (prefixWord ++ tailWord_476657) baseStart_476657 baseEnd_476657 := by
    simpa [prefixWord, tailWord_476657, baseEnd_476657] using wordTrace_append hprefix tailTrace_476657
  have hstable : (prefixWord ++ tailWord_476657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476657).length < 2 ^ (prefixWord ++ tailWord_476657).sum := by decide
  have hdescent : baseEnd_476657 < baseStart_476657 := by decide
  rcases family_descends (prefixWord ++ tailWord_476657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476723 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_476723 : Nat := 118140960795 + 476723 * 2 ^ 59
def prefixEnd_476723 : Nat := 4983230072969 + 3 ^ 40 * 476723 * 2
def baseEnd_476723 : Nat := 217589367158616491351197

theorem tailTrace_476723 : CollatzResearch.WordTrace tailWord_476723 prefixEnd_476723 217589367158616491351197 := by
  unfold tailWord_476723
  simp only [CollatzResearch.WordTrace]
  refine ⟨17387516251921463651506823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11591677501280975767671215 17387516251921463651506823)
  ·
    refine ⟨26081274377882195477260235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17387516251921463651506823 26081274377882195477260235)
    ·
      refine ⟨39121911566823293215890353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26081274377882195477260235 39121911566823293215890353)
      ·
        refine ⟨29341433675117469911917765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39121911566823293215890353 29341433675117469911917765)
        ·
          refine ⟨5501518814084525608484581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29341433675117469911917765 5501518814084525608484581)
          ·
            refine ⟨1031534777640848551590859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5501518814084525608484581 1031534777640848551590859)
            ·
              refine ⟨1547302166461272827386289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031534777640848551590859 1547302166461272827386289)
              ·
                refine ⟨1160476624845954620539717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547302166461272827386289 1160476624845954620539717)
                ·
                  refine ⟨217589367158616491351197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1160476624845954620539717 217589367158616491351197)
                  ·
                    rfl

theorem cell20_476723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_476723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476723 prefixEnd_476723 := by exact prefixLift 476723
  have htrace : WordTrace (prefixWord ++ tailWord_476723) baseStart_476723 baseEnd_476723 := by
    simpa [prefixWord, tailWord_476723, baseEnd_476723] using wordTrace_append hprefix tailTrace_476723
  have hstable : (prefixWord ++ tailWord_476723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476723).length < 2 ^ (prefixWord ++ tailWord_476723).sum := by decide
  have hdescent : baseEnd_476723 < baseStart_476723 := by decide
  rcases family_descends (prefixWord ++ tailWord_476723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476754 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_476754 : Nat := 118140960795 + 476754 * 2 ^ 59
def prefixEnd_476754 : Nat := 4983230072969 + 3 ^ 40 * 476754 * 2
def baseEnd_476754 : Nat := 217603516403318161317737

theorem tailTrace_476754 : CollatzResearch.WordTrace tailWord_476754 prefixEnd_476754 217603516403318161317737 := by
  unfold tailWord_476754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4347161728702288986471329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11592431276539437297256877 4347161728702288986471329)
  ·
    refine ⟨3260371296526716739853497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4347161728702288986471329 3260371296526716739853497)
    ·
      refine ⟨2445278472395037554890123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3260371296526716739853497 2445278472395037554890123)
      ·
        refine ⟨3667917708592556332335185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2445278472395037554890123 3667917708592556332335185)
        ·
          refine ⟨2750938281444417249251389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3667917708592556332335185 2750938281444417249251389)
          ·
            refine ⟨1031601855541656468469271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2750938281444417249251389 1031601855541656468469271)
            ·
              refine ⟨1547402783312484702703907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031601855541656468469271 1547402783312484702703907)
              ·
                refine ⟨2321104174968727054055861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547402783312484702703907 2321104174968727054055861)
                ·
                  refine ⟨217603516403318161317737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2321104174968727054055861 217603516403318161317737)
                  ·
                    rfl

theorem cell20_476754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_476754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476754 prefixEnd_476754 := by exact prefixLift 476754
  have htrace : WordTrace (prefixWord ++ tailWord_476754) baseStart_476754 baseEnd_476754 := by
    simpa [prefixWord, tailWord_476754, baseEnd_476754] using wordTrace_append hprefix tailTrace_476754
  have hstable : (prefixWord ++ tailWord_476754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476754).length < 2 ^ (prefixWord ++ tailWord_476754).sum := by decide
  have hdescent : baseEnd_476754 < baseStart_476754 := by decide
  rcases family_descends (prefixWord ++ tailWord_476754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476771 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 3]
def baseStart_476771 : Nat := 118140960795 + 476771 * 2 ^ 59
def prefixEnd_476771 : Nat := 4983230072969 + 3 ^ 40 * 476771 * 2
def baseEnd_476771 : Nat := 217611275666541657751001

theorem tailTrace_476771 : CollatzResearch.WordTrace tailWord_476771 prefixEnd_476771 217611275666541657751001 := by
  unfold tailWord_476771
  simp only [CollatzResearch.WordTrace]
  refine ⟨17389266955747567849254167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11592844637165045232836111 17389266955747567849254167)
  ·
    refine ⟨26083900433621351773881251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17389266955747567849254167 26083900433621351773881251)
    ·
      refine ⟨39125850650432027660821877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26083900433621351773881251 39125850650432027660821877)
      ·
        refine ⟨3668048498478002593202051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39125850650432027660821877 3668048498478002593202051)
        ·
          refine ⟨5502072747717003889803077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668048498478002593202051 5502072747717003889803077)
          ·
            refine ⟨1031638640196938229338077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5502072747717003889803077 1031638640196938229338077)
            ·
              refine ⟨386864490073851836001779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1031638640196938229338077 386864490073851836001779)
              ·
                refine ⟨580296735110777754002669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386864490073851836001779 580296735110777754002669)
                ·
                  refine ⟨217611275666541657751001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580296735110777754002669 217611275666541657751001)
                  ·
                    rfl

theorem cell20_476771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 3].length) (baseStart_476771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476771 prefixEnd_476771 := by exact prefixLift 476771
  have htrace : WordTrace (prefixWord ++ tailWord_476771) baseStart_476771 baseEnd_476771 := by
    simpa [prefixWord, tailWord_476771, baseEnd_476771] using wordTrace_append hprefix tailTrace_476771
  have hstable : (prefixWord ++ tailWord_476771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476771).length < 2 ^ (prefixWord ++ tailWord_476771).sum := by decide
  have hdescent : baseEnd_476771 < baseStart_476771 := by decide
  rcases family_descends (prefixWord ++ tailWord_476771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476781 : List Nat := [1, 5, 1, 1, 5, 1, 2, 4]
def baseStart_476781 : Nat := 118140960795 + 476781 * 2 ^ 59
def prefixEnd_476781 : Nat := 4983230072969 + 3 ^ 40 * 476781 * 2
def baseEnd_476781 : Nat := 72538613313008689139209

theorem tailTrace_476781 : CollatzResearch.WordTrace tailWord_476781 prefixEnd_476781 72538613313008689139209 := by
  unfold tailWord_476781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17389631685711339557118197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11593087790474226371412131 17389631685711339557118197)
  ·
    refine ⟨1630277970535438083479831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17389631685711339557118197 1630277970535438083479831)
    ·
      refine ⟨2445416955803157125219747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1630277970535438083479831 2445416955803157125219747)
      ·
        refine ⟨3668125433704735687829621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2445416955803157125219747 3668125433704735687829621)
        ·
          refine ⟨343886759409818970734027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3668125433704735687829621 343886759409818970734027)
          ·
            refine ⟨515830139114728456101041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343886759409818970734027 515830139114728456101041)
            ·
              refine ⟨386872604336046342075781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515830139114728456101041 386872604336046342075781)
              ·
                refine ⟨72538613313008689139209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386872604336046342075781 72538613313008689139209)
                ·
                  rfl

theorem cell20_476781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 4].length) (baseStart_476781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476781 prefixEnd_476781 := by exact prefixLift 476781
  have htrace : WordTrace (prefixWord ++ tailWord_476781) baseStart_476781 baseEnd_476781 := by
    simpa [prefixWord, tailWord_476781, baseEnd_476781] using wordTrace_append hprefix tailTrace_476781
  have hstable : (prefixWord ++ tailWord_476781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476781).length < 2 ^ (prefixWord ++ tailWord_476781).sum := by decide
  have hdescent : baseEnd_476781 < baseStart_476781 := by decide
  rcases family_descends (prefixWord ++ tailWord_476781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476896 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_476896 : Nat := 118140960795 + 476896 * 2 ^ 59
def prefixEnd_476896 : Nat := 4983230072969 + 3 ^ 40 * 476896 * 2
def baseEnd_476896 : Nat := 217668329072596778583823

theorem tailTrace_476896 : CollatzResearch.WordTrace tailWord_476896 prefixEnd_476896 217668329072596778583823 := by
  unfold tailWord_476896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696913040147357098777271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11595884053529809465036361 8696913040147357098777271)
  ·
    refine ⟨13045369560221035648165907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8696913040147357098777271 13045369560221035648165907)
    ·
      refine ⟨19568054340331553472248861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13045369560221035648165907 19568054340331553472248861)
      ·
        refine ⟨7338020377624332552093323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19568054340331553472248861 7338020377624332552093323)
        ·
          refine ⟨11007030566436498828139985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338020377624332552093323 11007030566436498828139985)
          ·
            refine ⟨8255272924827374121104989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11007030566436498828139985 8255272924827374121104989)
            ·
              refine ⟨3095727346810265295414371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8255272924827374121104989 3095727346810265295414371)
              ·
                refine ⟨4643591020215397943121557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095727346810265295414371 4643591020215397943121557)
                ·
                  refine ⟨217668329072596778583823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4643591020215397943121557 217668329072596778583823)
                  ·
                    rfl

theorem cell20_476896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_476896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476896 prefixEnd_476896 := by exact prefixLift 476896
  have htrace : WordTrace (prefixWord ++ tailWord_476896) baseStart_476896 baseEnd_476896 := by
    simpa [prefixWord, tailWord_476896, baseEnd_476896] using wordTrace_append hprefix tailTrace_476896
  have hstable : (prefixWord ++ tailWord_476896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476896).length < 2 ^ (prefixWord ++ tailWord_476896).sum := by decide
  have hdescent : baseEnd_476896 < baseStart_476896 := by decide
  rcases family_descends (prefixWord ++ tailWord_476896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476909 : List Nat := [1, 5, 1, 2, 1, 3, 2, 3, 2]
def baseStart_476909 : Nat := 118140960795 + 476909 * 2 ^ 59
def prefixEnd_476909 : Nat := 4983230072969 + 3 ^ 40 * 476909 * 2
def baseEnd_476909 : Nat := 217674262626826511150437

theorem tailTrace_476909 : CollatzResearch.WordTrace tailWord_476909 prefixEnd_476909 217674262626826511150437 := by
  unfold tailWord_476909
  simp only [CollatzResearch.WordTrace]
  refine ⟨17394300229247617417777781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11596200152831744945185187 17394300229247617417777781)
  ·
    refine ⟨1630715646491964132916667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17394300229247617417777781 1630715646491964132916667)
    ·
      refine ⟨2446073469737946199375001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1630715646491964132916667 2446073469737946199375001)
      ·
        refine ⟨1834555102303459649531251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2446073469737946199375001 1834555102303459649531251)
        ·
          refine ⟨2751832653455189474296877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834555102303459649531251 2751832653455189474296877)
          ·
            refine ⟨1031937245045696052861329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2751832653455189474296877 1031937245045696052861329)
            ·
              refine ⟨773952933784272039645997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031937245045696052861329 773952933784272039645997)
              ·
                refine ⟨290232350169102014867249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773952933784272039645997 290232350169102014867249)
                ·
                  refine ⟨217674262626826511150437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290232350169102014867249 217674262626826511150437)
                  ·
                    rfl

theorem cell20_476909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_476909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476909 prefixEnd_476909 := by exact prefixLift 476909
  have htrace : WordTrace (prefixWord ++ tailWord_476909) baseStart_476909 baseEnd_476909 := by
    simpa [prefixWord, tailWord_476909, baseEnd_476909] using wordTrace_append hprefix tailTrace_476909
  have hstable : (prefixWord ++ tailWord_476909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476909).length < 2 ^ (prefixWord ++ tailWord_476909).sum := by decide
  have hdescent : baseEnd_476909 < baseStart_476909 := by decide
  rcases family_descends (prefixWord ++ tailWord_476909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476916 : List Nat := [2, 6, 1, 1, 1, 2, 7]
def baseStart_476916 : Nat := 118140960795 + 476916 * 2 ^ 59
def prefixEnd_476916 : Nat := 4983230072969 + 3 ^ 40 * 476916 * 2
def baseEnd_476916 : Nat := 24186384179729510879675

theorem tailTrace_476916 : CollatzResearch.WordTrace tailWord_476916 prefixEnd_476916 24186384179729510879675 := by
  unfold tailWord_476916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697277770111128806641301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11596370360148171742188401 8697277770111128806641301)
  ·
    refine ⟨407684895473959162811311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8697277770111128806641301 407684895473959162811311)
    ·
      refine ⟨611527343210938744216967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407684895473959162811311 611527343210938744216967)
      ·
        refine ⟨917291014816408116325451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611527343210938744216967 917291014816408116325451)
        ·
          refine ⟨1375936522224612174488177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917291014816408116325451 1375936522224612174488177)
          ·
            refine ⟨1031952391668459130866133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1375936522224612174488177 1031952391668459130866133)
            ·
              refine ⟨24186384179729510879675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1031952391668459130866133 24186384179729510879675)
              ·
                rfl

theorem cell20_476916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 7].length) (baseStart_476916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476916 prefixEnd_476916 := by exact prefixLift 476916
  have htrace : WordTrace (prefixWord ++ tailWord_476916) baseStart_476916 baseEnd_476916 := by
    simpa [prefixWord, tailWord_476916, baseEnd_476916] using wordTrace_append hprefix tailTrace_476916
  have hstable : (prefixWord ++ tailWord_476916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476916).length < 2 ^ (prefixWord ++ tailWord_476916).sum := by decide
  have hdescent : baseEnd_476916 < baseStart_476916 := by decide
  rcases family_descends (prefixWord ++ tailWord_476916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476930 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_476930 : Nat := 118140960795 + 476930 * 2 ^ 59
def prefixEnd_476930 : Nat := 4983230072969 + 3 ^ 40 * 476930 * 2
def baseEnd_476930 : Nat := 217683847599043771450351

theorem tailTrace_476930 : CollatzResearch.WordTrace tailWord_476930 prefixEnd_476930 217683847599043771450351 := by
  unfold tailWord_476930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348766540542884501073061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11596710774781025336194829 4348766540542884501073061)
  ·
    refine ⟨815393726351790843951199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4348766540542884501073061 815393726351790843951199)
    ·
      refine ⟨1223090589527686265926799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815393726351790843951199 1223090589527686265926799)
      ·
        refine ⟨1834635884291529398890199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223090589527686265926799 1834635884291529398890199)
        ·
          refine ⟨2751953826437294098335299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834635884291529398890199 2751953826437294098335299)
          ·
            refine ⟨4127930739655941147502949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751953826437294098335299 4127930739655941147502949)
            ·
              refine ⟨773987013685488965156803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4127930739655941147502949 773987013685488965156803)
              ·
                refine ⟨1160980520528233447735205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773987013685488965156803 1160980520528233447735205)
                ·
                  refine ⟨217683847599043771450351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1160980520528233447735205 217683847599043771450351)
                  ·
                    rfl

theorem cell20_476930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_476930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476930 prefixEnd_476930 := by exact prefixLift 476930
  have htrace : WordTrace (prefixWord ++ tailWord_476930) baseStart_476930 baseEnd_476930 := by
    simpa [prefixWord, tailWord_476930, baseEnd_476930] using wordTrace_append hprefix tailTrace_476930
  have hstable : (prefixWord ++ tailWord_476930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476930).length < 2 ^ (prefixWord ++ tailWord_476930).sum := by decide
  have hdescent : baseEnd_476930 < baseStart_476930 := by decide
  rcases family_descends (prefixWord ++ tailWord_476930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476951 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_476951 : Nat := 118140960795 + 476951 * 2 ^ 59
def prefixEnd_476951 : Nat := 4983230072969 + 3 ^ 40 * 476951 * 2
def baseEnd_476951 : Nat := 217693432571261031750265

theorem tailTrace_476951 : CollatzResearch.WordTrace tailWord_476951 prefixEnd_476951 217693432571261031750265 := by
  unfold tailWord_476951
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395832095095458590806707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11597221396730305727204471 17395832095095458590806707)
  ·
    refine ⟨26093748142643187886210061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17395832095095458590806707 26093748142643187886210061)
    ·
      refine ⟨9785155553491195457328773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26093748142643187886210061 9785155553491195457328773)
      ·
        refine ⟨1834716666279599148249145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9785155553491195457328773 1834716666279599148249145)
        ·
          refine ⟨1376037499709699361186859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1834716666279599148249145 1376037499709699361186859)
          ·
            refine ⟨2064056249564549041780289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376037499709699361186859 2064056249564549041780289)
            ·
              refine ⟨1548042187173411781335217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064056249564549041780289 1548042187173411781335217)
              ·
                refine ⟨1161031640380058836001413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548042187173411781335217 1161031640380058836001413)
                ·
                  refine ⟨217693432571261031750265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161031640380058836001413 217693432571261031750265)
                  ·
                    rfl

theorem cell20_476951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_476951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476951 prefixEnd_476951 := by exact prefixLift 476951
  have htrace : WordTrace (prefixWord ++ tailWord_476951) baseStart_476951 baseEnd_476951 := by
    simpa [prefixWord, tailWord_476951, baseEnd_476951] using wordTrace_append hprefix tailTrace_476951
  have hstable : (prefixWord ++ tailWord_476951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476951).length < 2 ^ (prefixWord ++ tailWord_476951).sum := by decide
  have hdescent : baseEnd_476951 < baseStart_476951 := by decide
  rcases family_descends (prefixWord ++ tailWord_476951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476965 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_476965 : Nat := 118140960795 + 476965 * 2 ^ 59
def prefixEnd_476965 : Nat := 4983230072969 + 3 ^ 40 * 476965 * 2
def baseEnd_476965 : Nat := 217699822552739205283541

theorem tailTrace_476965 : CollatzResearch.WordTrace tailWord_476965 prefixEnd_476965 217699822552739205283541 := by
  unfold tailWord_476965
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396342717044738981816349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11597561811363159321210899 17396342717044738981816349)
  ·
    refine ⟨6523628518891777118181131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17396342717044738981816349 6523628518891777118181131)
    ·
      refine ⟨9785442778337665677271697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6523628518891777118181131 9785442778337665677271697)
      ·
        refine ⟨7339082083753249257953773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9785442778337665677271697 7339082083753249257953773)
        ·
          refine ⟨2752155781407468471732665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7339082083753249257953773 2752155781407468471732665)
          ·
            refine ⟨2064116836055601353799499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2752155781407468471732665 2064116836055601353799499)
            ·
              refine ⟨3096175254083402030699249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064116836055601353799499 3096175254083402030699249)
              ·
                refine ⟨2322131440562551523024437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096175254083402030699249 2322131440562551523024437)
                ·
                  refine ⟨217699822552739205283541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2322131440562551523024437 217699822552739205283541)
                  ·
                    rfl

theorem cell20_476965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_476965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476965 prefixEnd_476965 := by exact prefixLift 476965
  have htrace : WordTrace (prefixWord ++ tailWord_476965) baseStart_476965 baseEnd_476965 := by
    simpa [prefixWord, tailWord_476965, baseEnd_476965] using wordTrace_append hprefix tailTrace_476965
  have hstable : (prefixWord ++ tailWord_476965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476965).length < 2 ^ (prefixWord ++ tailWord_476965).sum := by decide
  have hdescent : baseEnd_476965 < baseStart_476965 := by decide
  rcases family_descends (prefixWord ++ tailWord_476965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476985 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 4]
def baseStart_476985 : Nat := 118140960795 + 476985 * 2 ^ 59
def prefixEnd_476985 : Nat := 4983230072969 + 3 ^ 40 * 476985 * 2
def baseEnd_476985 : Nat := 217708951097708024616793

theorem tailTrace_476985 : CollatzResearch.WordTrace tailWord_476985 prefixEnd_476985 217708951097708024616793 := by
  unfold tailWord_476985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17397072176972282397544409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11598048117981521598362939 17397072176972282397544409)
  ·
    refine ⟨13047804132729211798158307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17397072176972282397544409 13047804132729211798158307)
    ·
      refine ⟨19571706199093817697237461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13047804132729211798158307 19571706199093817697237461)
      ·
        refine ⟨458711864041261352279003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19571706199093817697237461 458711864041261352279003)
        ·
          refine ⟨688067796061892028418505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458711864041261352279003 688067796061892028418505)
          ·
            refine ⟨516050847046419021313879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688067796061892028418505 516050847046419021313879)
            ·
              refine ⟨774076270569628531970819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516050847046419021313879 774076270569628531970819)
              ·
                refine ⟨1161114405854442797956229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774076270569628531970819 1161114405854442797956229)
                ·
                  refine ⟨217708951097708024616793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161114405854442797956229 217708951097708024616793)
                  ·
                    rfl

theorem cell20_476985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_476985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_476985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_476985 prefixEnd_476985 := by exact prefixLift 476985
  have htrace : WordTrace (prefixWord ++ tailWord_476985) baseStart_476985 baseEnd_476985 := by
    simpa [prefixWord, tailWord_476985, baseEnd_476985] using wordTrace_append hprefix tailTrace_476985
  have hstable : (prefixWord ++ tailWord_476985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476985).length < 2 ^ (prefixWord ++ tailWord_476985).sum := by decide
  have hdescent : baseEnd_476985 < baseStart_476985 := by decide
  rcases family_descends (prefixWord ++ tailWord_476985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477017 : List Nat := [1, 2, 1, 2, 2, 3, 1, 8]
def baseStart_477017 : Nat := 118140960795 + 477017 * 2 ^ 59
def prefixEnd_477017 : Nat := 4983230072969 + 3 ^ 40 * 477017 * 2
def baseEnd_477017 : Nat := 72574518923219378516665

theorem tailTrace_477017 : CollatzResearch.WordTrace tailWord_477017 prefixEnd_477017 72574518923219378516665 := by
  unfold tailWord_477017
  simp only [CollatzResearch.WordTrace]
  refine ⟨17398239312856351862709305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11598826208570901241806203 17398239312856351862709305)
  ·
    refine ⟨13048679484642263897031979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17398239312856351862709305 13048679484642263897031979)
    ·
      refine ⟨19573019226963395845547969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13048679484642263897031979 19573019226963395845547969)
      ·
        refine ⟨14679764420222546884160977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19573019226963395845547969 14679764420222546884160977)
        ·
          refine ⟨11009823315166910163120733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14679764420222546884160977 11009823315166910163120733)
          ·
            refine ⟨4128683743187591311170275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11009823315166910163120733 4128683743187591311170275)
            ·
              refine ⟨6193025614781386966755413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128683743187591311170275 6193025614781386966755413)
              ·
                refine ⟨72574518923219378516665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6193025614781386966755413 72574518923219378516665)
                ·
                  rfl

theorem cell20_477017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_477017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477017 prefixEnd_477017 := by exact prefixLift 477017
  have htrace : WordTrace (prefixWord ++ tailWord_477017) baseStart_477017 baseEnd_477017 := by
    simpa [prefixWord, tailWord_477017, baseEnd_477017] using wordTrace_append hprefix tailTrace_477017
  have hstable : (prefixWord ++ tailWord_477017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477017).length < 2 ^ (prefixWord ++ tailWord_477017).sum := by decide
  have hdescent : baseEnd_477017 < baseStart_477017 := by decide
  rcases family_descends (prefixWord ++ tailWord_477017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477034 : List Nat := [3, 1, 3, 4, 9]
def baseStart_477034 : Nat := 118140960795 + 477034 * 2 ^ 59
def prefixEnd_477034 : Nat := 4983230072969 + 3 ^ 40 * 477034 * 2
def baseEnd_477034 : Nat := 2688040938677551012139

theorem tailTrace_477034 : CollatzResearch.WordTrace tailWord_477034 prefixEnd_477034 2688040938677551012139 := by
  unfold tailWord_477034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349714838448690941519539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11599239569196509177385437 4349714838448690941519539)
  ·
    refine ⟨6524572257673036412279309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4349714838448690941519539 6524572257673036412279309)
    ·
      refine ⟨2446714596627388654604741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6524572257673036412279309 2446714596627388654604741)
      ·
        refine ⟨458758986867635372738389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2446714596627388654604741 458758986867635372738389)
        ·
          refine ⟨2688040938677551012139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 458758986867635372738389 2688040938677551012139)
          ·
            rfl

theorem cell20_477034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 9].length) (baseStart_477034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477034 prefixEnd_477034 := by exact prefixLift 477034
  have htrace : WordTrace (prefixWord ++ tailWord_477034) baseStart_477034 baseEnd_477034 := by
    simpa [prefixWord, tailWord_477034, baseEnd_477034] using wordTrace_append hprefix tailTrace_477034
  have hstable : (prefixWord ++ tailWord_477034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477034).length < 2 ^ (prefixWord ++ tailWord_477034).sum := by decide
  have hdescent : baseEnd_477034 < baseStart_477034 := by decide
  rcases family_descends (prefixWord ++ tailWord_477034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477082 : List Nat := [3, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_477082 : Nat := 118140960795 + 477082 * 2 ^ 59
def prefixEnd_477082 : Nat := 4983230072969 + 3 ^ 40 * 477082 * 2
def baseEnd_477082 : Nat := 217753224540806798383063

theorem tailTrace_477082 : CollatzResearch.WordTrace tailWord_477082 prefixEnd_477082 217753224540806798383063 := by
  unfold tailWord_477082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350152514405216990956375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11600406705080578642550333 4350152514405216990956375)
  ·
    refine ⟨6525228771607825486434563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4350152514405216990956375 6525228771607825486434563)
    ·
      refine ⟨9787843157411738229651845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6525228771607825486434563 9787843157411738229651845)
      ·
        refine ⟨1835220592014700918059721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9787843157411738229651845 1835220592014700918059721)
        ·
          refine ⟨1376415444011025688544791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835220592014700918059721 1376415444011025688544791)
          ·
            refine ⟨2064623166016538532817187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376415444011025688544791 2064623166016538532817187)
            ·
              refine ⟨3096934749024807799225781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064623166016538532817187 3096934749024807799225781)
              ·
                refine ⟨290337632721075731177417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3096934749024807799225781 290337632721075731177417)
                ·
                  refine ⟨217753224540806798383063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290337632721075731177417 217753224540806798383063)
                  ·
                    rfl

theorem cell20_477082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_477082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477082 prefixEnd_477082 := by exact prefixLift 477082
  have htrace : WordTrace (prefixWord ++ tailWord_477082) baseStart_477082 baseEnd_477082 := by
    simpa [prefixWord, tailWord_477082, baseEnd_477082] using wordTrace_append hprefix tailTrace_477082
  have hstable : (prefixWord ++ tailWord_477082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477082).length < 2 ^ (prefixWord ++ tailWord_477082).sum := by decide
  have hdescent : baseEnd_477082 < baseStart_477082 := by decide
  rcases family_descends (prefixWord ++ tailWord_477082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477103 : List Nat := [1, 1, 2, 1, 2, 2, 3, 6, 2]
def baseStart_477103 : Nat := 118140960795 + 477103 * 2 ^ 59
def prefixEnd_477103 : Nat := 4983230072969 + 3 ^ 40 * 477103 * 2
def baseEnd_477103 : Nat := 217762809513024058682977

theorem tailTrace_477103 : CollatzResearch.WordTrace tailWord_477103 prefixEnd_477103 217762809513024058682977 := by
  unfold tailWord_477103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17401375990544788550339963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11600917327029859033559975 17401375990544788550339963)
  ·
    refine ⟨26102063985817182825509945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17401375990544788550339963 26102063985817182825509945)
    ·
      refine ⟨19576547989362887119132459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26102063985817182825509945 19576547989362887119132459)
      ·
        refine ⟨29364821984044330678698689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19576547989362887119132459 29364821984044330678698689)
        ·
          refine ⟨22023616488033248009024017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29364821984044330678698689 22023616488033248009024017)
          ·
            refine ⟨16517712366024936006768013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22023616488033248009024017 16517712366024936006768013)
            ·
              refine ⟨6194142137259351002538005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16517712366024936006768013 6194142137259351002538005)
              ·
                refine ⟨290350412684032078243969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6194142137259351002538005 290350412684032078243969)
                ·
                  refine ⟨217762809513024058682977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290350412684032078243969 217762809513024058682977)
                  ·
                    rfl

theorem cell20_477103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 2].length) (baseStart_477103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477103 prefixEnd_477103 := by exact prefixLift 477103
  have htrace : WordTrace (prefixWord ++ tailWord_477103) baseStart_477103 baseEnd_477103 := by
    simpa [prefixWord, tailWord_477103, baseEnd_477103] using wordTrace_append hprefix tailTrace_477103
  have hstable : (prefixWord ++ tailWord_477103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477103).length < 2 ^ (prefixWord ++ tailWord_477103).sum := by decide
  have hdescent : baseEnd_477103 < baseStart_477103 := by decide
  rcases family_descends (prefixWord ++ tailWord_477103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477131 : List Nat := [1, 1, 1, 1, 3, 4, 3, 6]
def baseStart_477131 : Nat := 118140960795 + 477131 * 2 ^ 59
def prefixEnd_477131 : Nat := 4983230072969 + 3 ^ 40 * 477131 * 2
def baseEnd_477131 : Nat := 72591863158660135249843

theorem tailTrace_477131 : CollatzResearch.WordTrace tailWord_477131 prefixEnd_477131 72591863158660135249843 := by
  unfold tailWord_477131
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402397234443349332359247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11601598156295566221572831 17402397234443349332359247)
  ·
    refine ⟨26103595851665023998538871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17402397234443349332359247 26103595851665023998538871)
    ·
      refine ⟨39155393777497535997808307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26103595851665023998538871 39155393777497535997808307)
      ·
        refine ⟨58733090666246303996712461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39155393777497535997808307 58733090666246303996712461)
        ·
          refine ⟨22024908999842363998767173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58733090666246303996712461 22024908999842363998767173)
          ·
            refine ⟨4129670437470443249768845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22024908999842363998767173 4129670437470443249768845)
            ·
              refine ⟨1548626414051416218663317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4129670437470443249768845 1548626414051416218663317)
              ·
                refine ⟨72591863158660135249843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1548626414051416218663317 72591863158660135249843)
                ·
                  rfl

theorem cell20_477131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_477131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477131 prefixEnd_477131 := by exact prefixLift 477131
  have htrace : WordTrace (prefixWord ++ tailWord_477131) baseStart_477131 baseEnd_477131 := by
    simpa [prefixWord, tailWord_477131, baseEnd_477131] using wordTrace_append hprefix tailTrace_477131
  have hstable : (prefixWord ++ tailWord_477131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477131).length < 2 ^ (prefixWord ++ tailWord_477131).sum := by decide
  have hdescent : baseEnd_477131 < baseStart_477131 := by decide
  rcases family_descends (prefixWord ++ tailWord_477131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477154 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_477154 : Nat := 118140960795 + 477154 * 2 ^ 59
def prefixEnd_477154 : Nat := 4983230072969 + 3 ^ 40 * 477154 * 2
def baseEnd_477154 : Nat := 217786087302694547982769

theorem tailTrace_477154 : CollatzResearch.WordTrace tailWord_477154 prefixEnd_477154 217786087302694547982769 := by
  unfold tailWord_477154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350809028340006065111629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11602157408906682840297677 4350809028340006065111629)
  ·
    refine ⟨1631553385627502274416861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4350809028340006065111629 1631553385627502274416861)
    ·
      refine ⟨611832519610313352906323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1631553385627502274416861 611832519610313352906323)
      ·
        refine ⟨917748779415470029359485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611832519610313352906323 917748779415470029359485)
        ·
          refine ⟨344155792280801261009807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 917748779415470029359485 344155792280801261009807)
          ·
            refine ⟨516233688421201891514711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344155792280801261009807 516233688421201891514711)
            ·
              refine ⟨774350532631802837272067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516233688421201891514711 774350532631802837272067)
              ·
                refine ⟨1161525798947704255908101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774350532631802837272067 1161525798947704255908101)
                ·
                  refine ⟨217786087302694547982769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161525798947704255908101 217786087302694547982769)
                  ·
                    rfl

theorem cell20_477154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_477154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477154 prefixEnd_477154 := by exact prefixLift 477154
  have htrace : WordTrace (prefixWord ++ tailWord_477154) baseStart_477154 baseEnd_477154 := by
    simpa [prefixWord, tailWord_477154, baseEnd_477154] using wordTrace_append hprefix tailTrace_477154
  have hstable : (prefixWord ++ tailWord_477154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477154).length < 2 ^ (prefixWord ++ tailWord_477154).sum := by decide
  have hdescent : baseEnd_477154 < baseStart_477154 := by decide
  rcases family_descends (prefixWord ++ tailWord_477154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477155 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_477155 : Nat := 118140960795 + 477155 * 2 ^ 59
def prefixEnd_477155 : Nat := 4983230072969 + 3 ^ 40 * 477155 * 2
def baseEnd_477155 : Nat := 217786543729942988949431

theorem tailTrace_477155 : CollatzResearch.WordTrace tailWord_477155 prefixEnd_477155 217786543729942988949431 := by
  unfold tailWord_477155
  simp only [CollatzResearch.WordTrace]
  refine ⟨17403272586356401431232919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11602181724237600954155279 17403272586356401431232919)
  ·
    refine ⟨26104908879534602146849379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17403272586356401431232919 26104908879534602146849379)
    ·
      refine ⟨39157363319301903220274069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26104908879534602146849379 39157363319301903220274069)
      ·
        refine ⟨1835501405592276713450347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39157363319301903220274069 1835501405592276713450347)
        ·
          refine ⟨2753252108388415070175521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835501405592276713450347 2753252108388415070175521)
          ·
            refine ⟨2064939081291311302631641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753252108388415070175521 2064939081291311302631641)
            ·
              refine ⟨1548704310968483476973731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064939081291311302631641 1548704310968483476973731)
              ·
                refine ⟨2323056466452725215460597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548704310968483476973731 2323056466452725215460597)
                ·
                  refine ⟨217786543729942988949431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323056466452725215460597 217786543729942988949431)
                  ·
                    rfl

theorem cell20_477155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_477155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477155 prefixEnd_477155 := by exact prefixLift 477155
  have htrace : WordTrace (prefixWord ++ tailWord_477155) baseStart_477155 baseEnd_477155 := by
    simpa [prefixWord, tailWord_477155, baseEnd_477155] using wordTrace_append hprefix tailTrace_477155
  have hstable : (prefixWord ++ tailWord_477155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477155).length < 2 ^ (prefixWord ++ tailWord_477155).sum := by decide
  have hdescent : baseEnd_477155 < baseStart_477155 := by decide
  rcases family_descends (prefixWord ++ tailWord_477155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477207 : List Nat := [1, 1, 3, 5, 10]
def baseStart_477207 : Nat := 118140960795 + 477207 * 2 ^ 59
def prefixEnd_477207 : Nat := 4983230072969 + 3 ^ 40 * 477207 * 2
def baseEnd_477207 : Nat := 2689015777121752089085

theorem tailTrace_477207 : CollatzResearch.WordTrace tailWord_477207 prefixEnd_477207 2689015777121752089085 := by
  unfold tailWord_477207
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405169182168014312125875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11603446121445342874750583 17405169182168014312125875)
  ·
    refine ⟨26107753773252021468188813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17405169182168014312125875 26107753773252021468188813)
    ·
      refine ⟨9790407664969508050570805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26107753773252021468188813 9790407664969508050570805)
      ·
        refine ⟨917850718590891379741013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9790407664969508050570805 917850718590891379741013)
        ·
          refine ⟨2689015777121752089085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 917850718590891379741013 2689015777121752089085)
          ·
            rfl

theorem cell20_477207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 10].length) (baseStart_477207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477207 prefixEnd_477207 := by exact prefixLift 477207
  have htrace : WordTrace (prefixWord ++ tailWord_477207) baseStart_477207 baseEnd_477207 := by
    simpa [prefixWord, tailWord_477207, baseEnd_477207] using wordTrace_append hprefix tailTrace_477207
  have hstable : (prefixWord ++ tailWord_477207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477207).length < 2 ^ (prefixWord ++ tailWord_477207).sum := by decide
  have hdescent : baseEnd_477207 < baseStart_477207 := by decide
  rcases family_descends (prefixWord ++ tailWord_477207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477210 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_477210 : Nat := 118140960795 + 477210 * 2 ^ 59
def prefixEnd_477210 : Nat := 4983230072969 + 3 ^ 40 * 477210 * 2
def baseEnd_477210 : Nat := 217811647228607242115873

theorem tailTrace_477210 : CollatzResearch.WordTrace tailWord_477210 prefixEnd_477210 217811647228607242115873 := by
  unfold tailWord_477210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4351319650289286456121271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11603519067438097216323389 4351319650289286456121271)
  ·
    refine ⟨6526979475433929684181907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4351319650289286456121271 6526979475433929684181907)
    ·
      refine ⟨9790469213150894526272861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6526979475433929684181907 9790469213150894526272861)
      ·
        refine ⟨3671425954931585447352323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9790469213150894526272861 3671425954931585447352323)
        ·
          refine ⟨5507138932397378171028485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3671425954931585447352323 5507138932397378171028485)
          ·
            refine ⟨1032588549824508407067841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5507138932397378171028485 1032588549824508407067841)
            ·
              refine ⟨774441412368381305300881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032588549824508407067841 774441412368381305300881)
              ·
                refine ⟨580831059276285978975661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774441412368381305300881 580831059276285978975661)
                ·
                  refine ⟨217811647228607242115873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580831059276285978975661 217811647228607242115873)
                  ·
                    rfl

theorem cell20_477210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_477210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477210 prefixEnd_477210 := by exact prefixLift 477210
  have htrace : WordTrace (prefixWord ++ tailWord_477210) baseStart_477210 baseEnd_477210 := by
    simpa [prefixWord, tailWord_477210, baseEnd_477210] using wordTrace_append hprefix tailTrace_477210
  have hstable : (prefixWord ++ tailWord_477210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477210).length < 2 ^ (prefixWord ++ tailWord_477210).sum := by decide
  have hdescent : baseEnd_477210 < baseStart_477210 := by decide
  rcases family_descends (prefixWord ++ tailWord_477210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477213 : List Nat := [1, 4, 2, 2, 2, 1, 4, 2, 2]
def baseStart_477213 : Nat := 118140960795 + 477213 * 2 ^ 59
def prefixEnd_477213 : Nat := 4983230072969 + 3 ^ 40 * 477213 * 2
def baseEnd_477213 : Nat := 217813016510352565015861

theorem tailTrace_477213 : CollatzResearch.WordTrace tailWord_477213 prefixEnd_477213 217813016510352565015861 := by
  unfold tailWord_477213
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405388020146277336844293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11603592013430851557896195 17405388020146277336844293)
  ·
    refine ⟨3263510253777427000658305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17405388020146277336844293 3263510253777427000658305)
    ·
      refine ⟨2447632690333070250493729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3263510253777427000658305 2447632690333070250493729)
      ·
        refine ⟨1835724517749802687870297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2447632690333070250493729 1835724517749802687870297)
        ·
          refine ⟨1376793388312352015902723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835724517749802687870297 1376793388312352015902723)
          ·
            refine ⟨2065190082468528023854085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376793388312352015902723 2065190082468528023854085)
            ·
              refine ⟨387223140462849004472641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2065190082468528023854085 387223140462849004472641)
              ·
                refine ⟨290417355347136753354481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387223140462849004472641 290417355347136753354481)
                ·
                  refine ⟨217813016510352565015861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290417355347136753354481 217813016510352565015861)
                  ·
                    rfl

theorem cell20_477213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_477213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477213 prefixEnd_477213 := by exact prefixLift 477213
  have htrace : WordTrace (prefixWord ++ tailWord_477213) baseStart_477213 baseEnd_477213 := by
    simpa [prefixWord, tailWord_477213, baseEnd_477213] using wordTrace_append hprefix tailTrace_477213
  have hstable : (prefixWord ++ tailWord_477213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477213).length < 2 ^ (prefixWord ++ tailWord_477213).sum := by decide
  have hdescent : baseEnd_477213 < baseStart_477213 := by decide
  rcases family_descends (prefixWord ++ tailWord_477213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477220 : List Nat := [2, 3, 1, 4, 3, 1, 1, 5]
def baseStart_477220 : Nat := 118140960795 + 477220 * 2 ^ 59
def prefixEnd_477220 : Nat := 4983230072969 + 3 ^ 40 * 477220 * 2
def baseEnd_477220 : Nat := 72605403833697217260833

theorem tailTrace_477220 : CollatzResearch.WordTrace tailWord_477220 prefixEnd_477220 72605403833697217260833 := by
  unfold tailWord_477220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8702821665560458766174557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11603762220747278354899409 8702821665560458766174557)
  ·
    refine ⟨3263558124585172037315459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8702821665560458766174557 3263558124585172037315459)
    ·
      refine ⟨4895337186877758055973189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3263558124585172037315459 4895337186877758055973189)
      ·
        refine ⟨917875722539579635494973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4895337186877758055973189 917875722539579635494973)
        ·
          refine ⟨344203395952342363310615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 917875722539579635494973 344203395952342363310615)
          ·
            refine ⟨516305093928513544965923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344203395952342363310615 516305093928513544965923)
            ·
              refine ⟨774457640892770317448885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516305093928513544965923 774457640892770317448885)
              ·
                refine ⟨72605403833697217260833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 774457640892770317448885 72605403833697217260833)
                ·
                  rfl

theorem cell20_477220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_477220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477220 prefixEnd_477220 := by exact prefixLift 477220
  have htrace : WordTrace (prefixWord ++ tailWord_477220) baseStart_477220 baseEnd_477220 := by
    simpa [prefixWord, tailWord_477220, baseEnd_477220] using wordTrace_append hprefix tailTrace_477220
  have hstable : (prefixWord ++ tailWord_477220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477220).length < 2 ^ (prefixWord ++ tailWord_477220).sum := by decide
  have hdescent : baseEnd_477220 < baseStart_477220 := by decide
  rcases family_descends (prefixWord ++ tailWord_477220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477241 : List Nat := [1, 2, 1, 5, 3, 1, 3, 4]
def baseStart_477241 : Nat := 118140960795 + 477241 * 2 ^ 59
def prefixEnd_477241 : Nat := 4983230072969 + 3 ^ 40 * 477241 * 2
def baseEnd_477241 : Nat := 72608598824436304027471

theorem tailTrace_477241 : CollatzResearch.WordTrace tailWord_477241 prefixEnd_477241 72608598824436304027471 := by
  unfold tailWord_477241
  simp only [CollatzResearch.WordTrace]
  refine ⟨17406409264044838118863577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11604272842696558745909051 17406409264044838118863577)
  ·
    refine ⟨13054806948033628589147683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17406409264044838118863577 13054806948033628589147683)
    ·
      refine ⟨19582210422050442883721525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13054806948033628589147683 19582210422050442883721525)
      ·
        refine ⟨1835832227067229020348893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19582210422050442883721525 1835832227067229020348893)
        ·
          refine ⟨688437085150210882630835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1835832227067229020348893 688437085150210882630835)
          ·
            refine ⟨1032655627725316323946253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688437085150210882630835 1032655627725316323946253)
            ·
              refine ⟨387245860396993621479845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1032655627725316323946253 387245860396993621479845)
              ·
                refine ⟨72608598824436304027471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387245860396993621479845 72608598824436304027471)
                ·
                  rfl

theorem cell20_477241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_477241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477241 prefixEnd_477241 := by exact prefixLift 477241
  have htrace : WordTrace (prefixWord ++ tailWord_477241) baseStart_477241 baseEnd_477241 := by
    simpa [prefixWord, tailWord_477241, baseEnd_477241] using wordTrace_append hprefix tailTrace_477241
  have hstable : (prefixWord ++ tailWord_477241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477241).length < 2 ^ (prefixWord ++ tailWord_477241).sum := by decide
  have hdescent : baseEnd_477241 < baseStart_477241 := by decide
  rcases family_descends (prefixWord ++ tailWord_477241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477269 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_477269 : Nat := 118140960795 + 477269 * 2 ^ 59
def prefixEnd_477269 : Nat := 4983230072969 + 3 ^ 40 * 477269 * 2
def baseEnd_477269 : Nat := 217838576436265259148965

theorem tailTrace_477269 : CollatzResearch.WordTrace tailWord_477269 prefixEnd_477269 217838576436265259148965 := by
  unfold tailWord_477269
  simp only [CollatzResearch.WordTrace]
  refine ⟨17407430507943398900882861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11604953671962265933921907 17407430507943398900882861)
  ·
    refine ⟨6527786440478774587831073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17407430507943398900882861 6527786440478774587831073)
    ·
      refine ⟨4895839830359080940873305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6527786440478774587831073 4895839830359080940873305)
      ·
        refine ⟨3671879872769310705654979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4895839830359080940873305 3671879872769310705654979)
        ·
          refine ⟨5507819809153966058482469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3671879872769310705654979 5507819809153966058482469)
          ·
            refine ⟨1032716214216368635965463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5507819809153966058482469 1032716214216368635965463)
            ·
              refine ⟨1549074321324552953948195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032716214216368635965463 1549074321324552953948195)
              ·
                refine ⟨2323611481986829430922293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549074321324552953948195 2323611481986829430922293)
                ·
                  refine ⟨217838576436265259148965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323611481986829430922293 217838576436265259148965)
                  ·
                    rfl

theorem cell20_477269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_477269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477269 prefixEnd_477269 := by exact prefixLift 477269
  have htrace : WordTrace (prefixWord ++ tailWord_477269) baseStart_477269 baseEnd_477269 := by
    simpa [prefixWord, tailWord_477269, baseEnd_477269] using wordTrace_append hprefix tailTrace_477269
  have hstable : (prefixWord ++ tailWord_477269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477269).length < 2 ^ (prefixWord ++ tailWord_477269).sum := by decide
  have hdescent : baseEnd_477269 < baseStart_477269 := by decide
  rcases family_descends (prefixWord ++ tailWord_477269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477282 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_477282 : Nat := 118140960795 + 477282 * 2 ^ 59
def prefixEnd_477282 : Nat := 4983230072969 + 3 ^ 40 * 477282 * 2
def baseEnd_477282 : Nat := 217844509990494991715579

theorem tailTrace_477282 : CollatzResearch.WordTrace tailWord_477282 prefixEnd_477282 217844509990494991715579 := by
  unfold tailWord_477282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4351976164224075530276525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11605269771264201414070733 4351976164224075530276525)
  ·
    refine ⟨1631991061584028323853697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4351976164224075530276525 1631991061584028323853697)
    ·
      refine ⟨1223993296188021242890273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1631991061584028323853697 1223993296188021242890273)
      ·
        refine ⟨917994972141015932167705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1223993296188021242890273 917994972141015932167705)
        ·
          refine ⟨688496229105761949125779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917994972141015932167705 688496229105761949125779)
          ·
            refine ⟨1032744343658642923688669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688496229105761949125779 1032744343658642923688669)
            ·
              refine ⟨387279128871991096383251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1032744343658642923688669 387279128871991096383251)
              ·
                refine ⟨580918693307986644574877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387279128871991096383251 580918693307986644574877)
                ·
                  refine ⟨217844509990494991715579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580918693307986644574877 217844509990494991715579)
                  ·
                    rfl

theorem cell20_477282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_477282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477282 prefixEnd_477282 := by exact prefixLift 477282
  have htrace : WordTrace (prefixWord ++ tailWord_477282) baseStart_477282 baseEnd_477282 := by
    simpa [prefixWord, tailWord_477282, baseEnd_477282] using wordTrace_append hprefix tailTrace_477282
  have hstable : (prefixWord ++ tailWord_477282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477282).length < 2 ^ (prefixWord ++ tailWord_477282).sum := by decide
  have hdescent : baseEnd_477282 < baseStart_477282 := by decide
  rcases family_descends (prefixWord ++ tailWord_477282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477328 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_477328 : Nat := 118140960795 + 477328 * 2 ^ 59
def prefixEnd_477328 : Nat := 4983230072969 + 3 ^ 40 * 477328 * 2
def baseEnd_477328 : Nat := 217865505643923276182057

theorem tailTrace_477328 : CollatzResearch.WordTrace tailWord_477328 prefixEnd_477328 217865505643923276182057 := by
  unfold tailWord_477328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8704791207364825988640319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11606388276486434651520425 8704791207364825988640319)
  ·
    refine ⟨13057186811047238982960479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8704791207364825988640319 13057186811047238982960479)
    ·
      refine ⟨19585780216570858474440719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13057186811047238982960479 19585780216570858474440719)
      ·
        refine ⟨29378670324856287711661079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19585780216570858474440719 29378670324856287711661079)
        ·
          refine ⟨44068005487284431567491619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29378670324856287711661079 44068005487284431567491619)
          ·
            refine ⟨66102008230926647351237429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44068005487284431567491619 66102008230926647351237429)
            ·
              refine ⟨6197063271649373189178509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66102008230926647351237429 6197063271649373189178509)
              ·
                refine ⟨2323898726868514945941941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6197063271649373189178509 2323898726868514945941941)
                ·
                  refine ⟨217865505643923276182057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323898726868514945941941 217865505643923276182057)
                  ·
                    rfl

theorem cell20_477328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_477328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477328 prefixEnd_477328 := by exact prefixLift 477328
  have htrace : WordTrace (prefixWord ++ tailWord_477328) baseStart_477328 baseEnd_477328 := by
    simpa [prefixWord, tailWord_477328, baseEnd_477328] using wordTrace_append hprefix tailTrace_477328
  have hstable : (prefixWord ++ tailWord_477328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477328).length < 2 ^ (prefixWord ++ tailWord_477328).sum := by decide
  have hdescent : baseEnd_477328 < baseStart_477328 := by decide
  rcases family_descends (prefixWord ++ tailWord_477328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477341 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 3]
def baseStart_477341 : Nat := 118140960795 + 477341 * 2 ^ 59
def prefixEnd_477341 : Nat := 4983230072969 + 3 ^ 40 * 477341 * 2
def baseEnd_477341 : Nat := 217871439198153008748671

theorem tailTrace_477341 : CollatzResearch.WordTrace tailWord_477341 prefixEnd_477341 217871439198153008748671 := by
  unfold tailWord_477341
  simp only [CollatzResearch.WordTrace]
  refine ⟨17410056563682555197503877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11606704375788370131669251 17410056563682555197503877)
  ·
    refine ⟨3264385605690479099531977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17410056563682555197503877 3264385605690479099531977)
    ·
      refine ⟨2448289204267859324648983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3264385605690479099531977 2448289204267859324648983)
      ·
        refine ⟨3672433806401788986973475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448289204267859324648983 3672433806401788986973475)
        ·
          refine ⟨5508650709602683480460213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672433806401788986973475 5508650709602683480460213)
          ·
            refine ⟨516436004025251576293145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5508650709602683480460213 516436004025251576293145)
            ·
              refine ⟨387327003018938682219859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516436004025251576293145 387327003018938682219859)
              ·
                refine ⟨580990504528408023329789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387327003018938682219859 580990504528408023329789)
                ·
                  refine ⟨217871439198153008748671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580990504528408023329789 217871439198153008748671)
                  ·
                    rfl

theorem cell20_477341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_477341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477341 prefixEnd_477341 := by exact prefixLift 477341
  have htrace : WordTrace (prefixWord ++ tailWord_477341) baseStart_477341 baseEnd_477341 := by
    simpa [prefixWord, tailWord_477341, baseEnd_477341] using wordTrace_append hprefix tailTrace_477341
  have hstable : (prefixWord ++ tailWord_477341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477341).length < 2 ^ (prefixWord ++ tailWord_477341).sum := by decide
  have hdescent : baseEnd_477341 < baseStart_477341 := by decide
  rcases family_descends (prefixWord ++ tailWord_477341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477369 : List Nat := [1, 2, 1, 4, 1, 2, 2, 5, 2]
def baseStart_477369 : Nat := 118140960795 + 477369 * 2 ^ 59
def prefixEnd_477369 : Nat := 4983230072969 + 3 ^ 40 * 477369 * 2
def baseEnd_477369 : Nat := 217884219161109355815223

theorem tailTrace_477369 : CollatzResearch.WordTrace tailWord_477369 prefixEnd_477369 217884219161109355815223 := by
  unfold tailWord_477369
  simp only [CollatzResearch.WordTrace]
  refine ⟨17411077807581115979523161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11607385205054077319682107 17411077807581115979523161)
  ·
    refine ⟨13058308355685836984642371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17411077807581115979523161 13058308355685836984642371)
    ·
      refine ⟨19587462533528755476963557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13058308355685836984642371 19587462533528755476963557)
      ·
        refine ⟨3672649225036641651930667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19587462533528755476963557 3672649225036641651930667)
        ·
          refine ⟨5508973837554962477896001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672649225036641651930667 5508973837554962477896001)
          ·
            refine ⟨4131730378166221858422001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508973837554962477896001 4131730378166221858422001)
            ·
              refine ⟨3098797783624666393816501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131730378166221858422001 3098797783624666393816501)
              ·
                refine ⟨290512292214812474420297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3098797783624666393816501 290512292214812474420297)
                ·
                  refine ⟨217884219161109355815223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290512292214812474420297 217884219161109355815223)
                  ·
                    rfl

theorem cell20_477369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_477369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477369 prefixEnd_477369 := by exact prefixLift 477369
  have htrace : WordTrace (prefixWord ++ tailWord_477369) baseStart_477369 baseEnd_477369 := by
    simpa [prefixWord, tailWord_477369, baseEnd_477369] using wordTrace_append hprefix tailTrace_477369
  have hstable : (prefixWord ++ tailWord_477369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477369).length < 2 ^ (prefixWord ++ tailWord_477369).sum := by decide
  have hdescent : baseEnd_477369 < baseStart_477369 := by decide
  rcases family_descends (prefixWord ++ tailWord_477369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477486 : List Nat := [4, 1, 3, 3, 2, 1, 6]
def baseStart_477486 : Nat := 118140960795 + 477486 * 2 ^ 59
def prefixEnd_477486 : Nat := 4983230072969 + 3 ^ 40 * 477486 * 2
def baseEnd_477486 : Nat := 24215291238797438768305

theorem tailTrace_477486 : CollatzResearch.WordTrace tailWord_477486 prefixEnd_477486 24215291238797438768305 := by
  unfold tailWord_477486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176918143519655620191539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11610230098771496641021541 2176918143519655620191539)
  ·
    refine ⟨3265377215279483430287309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176918143519655620191539 3265377215279483430287309)
    ·
      refine ⟨1224516455729806286357741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3265377215279483430287309 1224516455729806286357741)
      ·
        refine ⟨459193670898677357384153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1224516455729806286357741 459193670898677357384153)
        ·
          refine ⟨344395253174008018038115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459193670898677357384153 344395253174008018038115)
          ·
            refine ⟨516592879761012027057173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344395253174008018038115 516592879761012027057173)
            ·
              refine ⟨24215291238797438768305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 516592879761012027057173 24215291238797438768305)
              ·
                rfl

theorem cell20_477486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 6].length) (baseStart_477486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477486 prefixEnd_477486 := by exact prefixLift 477486
  have htrace : WordTrace (prefixWord ++ tailWord_477486) baseStart_477486 baseEnd_477486 := by
    simpa [prefixWord, tailWord_477486, baseEnd_477486] using wordTrace_append hprefix tailTrace_477486
  have hstable : (prefixWord ++ tailWord_477486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477486).length < 2 ^ (prefixWord ++ tailWord_477486).sum := by decide
  have hdescent : baseEnd_477486 < baseStart_477486 := by decide
  rcases family_descends (prefixWord ++ tailWord_477486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477487 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_477487 : Nat := 118140960795 + 477487 * 2 ^ 59
def prefixEnd_477487 : Nat := 4983230072969 + 3 ^ 40 * 477487 * 2
def baseEnd_477487 : Nat := 217938077576425389881407

theorem tailTrace_477487 : CollatzResearch.WordTrace tailWord_477487 prefixEnd_477487 217938077576425389881407 := by
  unfold tailWord_477487
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415381621153622132318715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11610254414102414754879143 17415381621153622132318715)
  ·
    refine ⟨26123072431730433198478073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17415381621153622132318715 26123072431730433198478073)
    ·
      refine ⟨19592304323797824898858555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26123072431730433198478073 19592304323797824898858555)
      ·
        refine ⟨29388456485696737348287833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592304323797824898858555 29388456485696737348287833)
        ·
          refine ⟨22041342364272553011215875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29388456485696737348287833 22041342364272553011215875)
          ·
            refine ⟨33062013546408829516823813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22041342364272553011215875 33062013546408829516823813)
            ·
              refine ⟨6199127539951655534404465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33062013546408829516823813 6199127539951655534404465)
              ·
                refine ⟨4649345654963741650803349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6199127539951655534404465 4649345654963741650803349)
                ·
                  refine ⟨217938077576425389881407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4649345654963741650803349 217938077576425389881407)
                  ·
                    rfl

theorem cell20_477487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_477487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477487 prefixEnd_477487 := by exact prefixLift 477487
  have htrace : WordTrace (prefixWord ++ tailWord_477487) baseStart_477487 baseEnd_477487 := by
    simpa [prefixWord, tailWord_477487, baseEnd_477487] using wordTrace_append hprefix tailTrace_477487
  have hstable : (prefixWord ++ tailWord_477487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477487).length < 2 ^ (prefixWord ++ tailWord_477487).sum := by decide
  have hdescent : baseEnd_477487 < baseStart_477487 := by decide
  rcases family_descends (prefixWord ++ tailWord_477487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477490 : List Nat := [3, 2, 1, 1, 5, 2, 6]
def baseStart_477490 : Nat := 118140960795 + 477490 * 2 ^ 59
def prefixEnd_477490 : Nat := 4983230072969 + 3 ^ 40 * 477490 * 2
def baseEnd_477490 : Nat := 24215494095352301420155

theorem tailTrace_477490 : CollatzResearch.WordTrace tailWord_477490 prefixEnd_477490 24215494095352301420155 := by
  unfold tailWord_477490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353872760035688411169481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11610327360095169096451949 4353872760035688411169481)
  ·
    refine ⟨3265404570026766308377111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4353872760035688411169481 3265404570026766308377111)
    ·
      refine ⟨4898106855040149462565667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265404570026766308377111 4898106855040149462565667)
      ·
        refine ⟨7347160282560224193848501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898106855040149462565667 7347160282560224193848501)
        ·
          refine ⟨688796276490021018173297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7347160282560224193848501 688796276490021018173297)
          ·
            refine ⟨516597207367515763629973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688796276490021018173297 516597207367515763629973)
            ·
              refine ⟨24215494095352301420155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 516597207367515763629973 24215494095352301420155)
              ·
                rfl

theorem cell20_477490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 6].length) (baseStart_477490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477490 prefixEnd_477490 := by exact prefixLift 477490
  have htrace : WordTrace (prefixWord ++ tailWord_477490) baseStart_477490 baseEnd_477490 := by
    simpa [prefixWord, tailWord_477490, baseEnd_477490] using wordTrace_append hprefix tailTrace_477490
  have hstable : (prefixWord ++ tailWord_477490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477490).length < 2 ^ (prefixWord ++ tailWord_477490).sum := by decide
  have hdescent : baseEnd_477490 < baseStart_477490 := by decide
  rcases family_descends (prefixWord ++ tailWord_477490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477497 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_477497 : Nat := 118140960795 + 477497 * 2 ^ 59
def prefixEnd_477497 : Nat := 4983230072969 + 3 ^ 40 * 477497 * 2
def baseEnd_477497 : Nat := 217942641848909799548033

theorem tailTrace_477497 : CollatzResearch.WordTrace tailWord_477497 prefixEnd_477497 217942641848909799548033 := by
  unfold tailWord_477497
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415746351117393840182745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11610497567411595893455163 17415746351117393840182745)
  ·
    refine ⟨13061809763338045380137059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17415746351117393840182745 13061809763338045380137059)
    ·
      refine ⟨19592714645007068070205589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061809763338045380137059 19592714645007068070205589)
      ·
        refine ⟨918408498984706315790887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19592714645007068070205589 918408498984706315790887)
        ·
          refine ⟨1377612748477059473686331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918408498984706315790887 1377612748477059473686331)
          ·
            refine ⟨2066419122715589210529497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377612748477059473686331 2066419122715589210529497)
            ·
              refine ⟨1549814342036691907897123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066419122715589210529497 1549814342036691907897123)
              ·
                refine ⟨2324721513055037861845685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549814342036691907897123 2324721513055037861845685)
                ·
                  refine ⟨217942641848909799548033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2324721513055037861845685 217942641848909799548033)
                  ·
                    rfl

theorem cell20_477497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_477497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477497 prefixEnd_477497 := by exact prefixLift 477497
  have htrace : WordTrace (prefixWord ++ tailWord_477497) baseStart_477497 baseEnd_477497 := by
    simpa [prefixWord, tailWord_477497, baseEnd_477497] using wordTrace_append hprefix tailTrace_477497
  have hstable : (prefixWord ++ tailWord_477497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477497).length < 2 ^ (prefixWord ++ tailWord_477497).sum := by decide
  have hdescent : baseEnd_477497 < baseStart_477497 := by decide
  rcases family_descends (prefixWord ++ tailWord_477497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477500 : List Nat := [2, 2, 2, 2, 1, 2, 5, 2, 2]
def baseStart_477500 : Nat := 118140960795 + 477500 * 2 ^ 59
def prefixEnd_477500 : Nat := 4983230072969 + 3 ^ 40 * 477500 * 2
def baseEnd_477500 : Nat := 217944011130655122448021

theorem tailTrace_477500 : CollatzResearch.WordTrace tailWord_477500 prefixEnd_477500 217944011130655122448021 := by
  unfold tailWord_477500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707927885053262676270977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11610570513404350235027969 8707927885053262676270977)
  ·
    refine ⟨6530945913789947007203233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8707927885053262676270977 6530945913789947007203233)
    ·
      refine ⟨4898209435342460255402425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6530945913789947007203233 4898209435342460255402425)
      ·
        refine ⟨3673657076506845191551819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4898209435342460255402425 3673657076506845191551819)
        ·
          refine ⟨5510485614760267787327729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673657076506845191551819 5510485614760267787327729)
          ·
            refine ⟨4132864211070200840495797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5510485614760267787327729 4132864211070200840495797)
            ·
              refine ⟨387456019787831328796481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4132864211070200840495797 387456019787831328796481)
              ·
                refine ⟨290592014840873496597361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387456019787831328796481 290592014840873496597361)
                ·
                  refine ⟨217944011130655122448021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290592014840873496597361 217944011130655122448021)
                  ·
                    rfl

theorem cell20_477500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_477500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477500 prefixEnd_477500 := by exact prefixLift 477500
  have htrace : WordTrace (prefixWord ++ tailWord_477500) baseStart_477500 baseEnd_477500 := by
    simpa [prefixWord, tailWord_477500, baseEnd_477500] using wordTrace_append hprefix tailTrace_477500
  have hstable : (prefixWord ++ tailWord_477500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477500).length < 2 ^ (prefixWord ++ tailWord_477500).sum := by decide
  have hdescent : baseEnd_477500 < baseStart_477500 := by decide
  rcases family_descends (prefixWord ++ tailWord_477500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477511 : List Nat := [1, 1, 4, 1, 2, 2, 4, 5]
def baseStart_477511 : Nat := 118140960795 + 477511 * 2 ^ 59
def prefixEnd_477511 : Nat := 4983230072969 + 3 ^ 40 * 477511 * 2
def baseEnd_477511 : Nat := 72649677276795991027103

theorem tailTrace_477511 : CollatzResearch.WordTrace tailWord_477511 prefixEnd_477511 72649677276795991027103 := by
  unfold tailWord_477511
  simp only [CollatzResearch.WordTrace]
  refine ⟨17416256973066674231192387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11610837982044449487461591 17416256973066674231192387)
  ·
    refine ⟨26124385459600011346788581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17416256973066674231192387 26124385459600011346788581)
    ·
      refine ⟨4898322273675002127522859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26124385459600011346788581 4898322273675002127522859)
      ·
        refine ⟨7347483410512503191284289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898322273675002127522859 7347483410512503191284289)
        ·
          refine ⟨5510612557884377393463217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7347483410512503191284289 5510612557884377393463217)
          ·
            refine ⟨4132959418413283045097413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5510612557884377393463217 4132959418413283045097413)
            ·
              refine ⟨774929890952490570955765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4132959418413283045097413 774929890952490570955765)
              ·
                refine ⟨72649677276795991027103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 774929890952490570955765 72649677276795991027103)
                ·
                  rfl

theorem cell20_477511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_477511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477511 prefixEnd_477511 := by exact prefixLift 477511
  have htrace : WordTrace (prefixWord ++ tailWord_477511) baseStart_477511 baseEnd_477511 := by
    simpa [prefixWord, tailWord_477511, baseEnd_477511] using wordTrace_append hprefix tailTrace_477511
  have hstable : (prefixWord ++ tailWord_477511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477511).length < 2 ^ (prefixWord ++ tailWord_477511).sum := by decide
  have hdescent : baseEnd_477511 < baseStart_477511 := by decide
  rcases family_descends (prefixWord ++ tailWord_477511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477518 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_477518 : Nat := 118140960795 + 477518 * 2 ^ 59
def prefixEnd_477518 : Nat := 4983230072969 + 3 ^ 40 * 477518 * 2
def baseEnd_477518 : Nat := 217952226821127059847947

theorem tailTrace_477518 : CollatzResearch.WordTrace tailWord_477518 prefixEnd_477518 217952226821127059847947 := by
  unfold tailWord_477518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177064035505164303337151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11611008189360876284464805 2177064035505164303337151)
  ·
    refine ⟨3265596053257746455005727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177064035505164303337151 3265596053257746455005727)
    ·
      refine ⟨4898394079886619682508591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265596053257746455005727 4898394079886619682508591)
      ·
        refine ⟨7347591119829929523762887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898394079886619682508591 7347591119829929523762887)
        ·
          refine ⟨11021386679744894285644331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347591119829929523762887 11021386679744894285644331)
          ·
            refine ⟨16532080019617341428466497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021386679744894285644331 16532080019617341428466497)
            ·
              refine ⟨12399060014713006071349873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16532080019617341428466497 12399060014713006071349873)
              ·
                refine ⟨9299295011034754553512405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12399060014713006071349873 9299295011034754553512405)
                ·
                  refine ⟨217952226821127059847947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9299295011034754553512405 217952226821127059847947)
                  ·
                    rfl

theorem cell20_477518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_477518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477518 prefixEnd_477518 := by exact prefixLift 477518
  have htrace : WordTrace (prefixWord ++ tailWord_477518) baseStart_477518 baseEnd_477518 := by
    simpa [prefixWord, tailWord_477518, baseEnd_477518] using wordTrace_append hprefix tailTrace_477518
  have hstable : (prefixWord ++ tailWord_477518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477518).length < 2 ^ (prefixWord ++ tailWord_477518).sum := by decide
  have hdescent : baseEnd_477518 < baseStart_477518 := by decide
  rcases family_descends (prefixWord ++ tailWord_477518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477580 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_477580 : Nat := 118140960795 + 477580 * 2 ^ 59
def prefixEnd_477580 : Nat := 4983230072969 + 3 ^ 40 * 477580 * 2
def baseEnd_477580 : Nat := 217980525310530399781027

theorem tailTrace_477580 : CollatzResearch.WordTrace tailWord_477580 prefixEnd_477580 217980525310530399781027 := by
  unfold tailWord_477580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8709386804908349507727097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11612515739877799343636129 8709386804908349507727097)
  ·
    refine ⟨6532040103681262130795323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8709386804908349507727097 6532040103681262130795323)
    ·
      refine ⟨9798060155521893196192985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532040103681262130795323 9798060155521893196192985)
      ·
        refine ⟨7348545116641419897144739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9798060155521893196192985 7348545116641419897144739)
        ·
          refine ⟨11022817674962129845717109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7348545116641419897144739 11022817674962129845717109)
          ·
            refine ⟨1033389157027699673035979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11022817674962129845717109 1033389157027699673035979)
            ·
              refine ⟨1550083735541549509553969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033389157027699673035979 1550083735541549509553969)
              ·
                refine ⟨1162562801656162132165477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550083735541549509553969 1162562801656162132165477)
                ·
                  refine ⟨217980525310530399781027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162562801656162132165477 217980525310530399781027)
                  ·
                    rfl

theorem cell20_477580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_477580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477580 prefixEnd_477580 := by exact prefixLift 477580
  have htrace : WordTrace (prefixWord ++ tailWord_477580) baseStart_477580 baseEnd_477580 := by
    simpa [prefixWord, tailWord_477580, baseEnd_477580] using wordTrace_append hprefix tailTrace_477580
  have hstable : (prefixWord ++ tailWord_477580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477580).length < 2 ^ (prefixWord ++ tailWord_477580).sum := by decide
  have hdescent : baseEnd_477580 < baseStart_477580 := by decide
  rcases family_descends (prefixWord ++ tailWord_477580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477618 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_477618 : Nat := 118140960795 + 477618 * 2 ^ 59
def prefixEnd_477618 : Nat := 4983230072969 + 3 ^ 40 * 477618 * 2
def baseEnd_477618 : Nat := 217997869545971156514205

theorem tailTrace_477618 : CollatzResearch.WordTrace tailWord_477618 prefixEnd_477618 217997869545971156514205 := by
  unfold tailWord_477618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355039895919757876334377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11613439722452687670225005 4355039895919757876334377)
  ·
    refine ⟨3266279921939818407250783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4355039895919757876334377 3266279921939818407250783)
    ·
      refine ⟨4899419882909727610876175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3266279921939818407250783 4899419882909727610876175)
      ·
        refine ⟨7349129824364591416314263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899419882909727610876175 7349129824364591416314263)
        ·
          refine ⟨11023694736546887124471395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7349129824364591416314263 11023694736546887124471395)
          ·
            refine ⟨16535542104820330686707093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11023694736546887124471395 16535542104820330686707093)
            ·
              refine ⟨775103536163453000939395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16535542104820330686707093 775103536163453000939395)
              ·
                refine ⟨1162655304245179501409093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775103536163453000939395 1162655304245179501409093)
                ·
                  refine ⟨217997869545971156514205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162655304245179501409093 217997869545971156514205)
                  ·
                    rfl

theorem cell20_477618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_477618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477618 prefixEnd_477618 := by exact prefixLift 477618
  have htrace : WordTrace (prefixWord ++ tailWord_477618) baseStart_477618 baseEnd_477618 := by
    simpa [prefixWord, tailWord_477618, baseEnd_477618] using wordTrace_append hprefix tailTrace_477618
  have hstable : (prefixWord ++ tailWord_477618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477618).length < 2 ^ (prefixWord ++ tailWord_477618).sum := by decide
  have hdescent : baseEnd_477618 < baseStart_477618 := by decide
  rcases family_descends (prefixWord ++ tailWord_477618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477652 : List Nat := [2, 4, 1, 2, 2, 1, 3, 3, 2]
def baseStart_477652 : Nat := 118140960795 + 477652 * 2 ^ 59
def prefixEnd_477652 : Nat := 4983230072969 + 3 ^ 40 * 477652 * 2
def baseEnd_477652 : Nat := 218013388072418149380733

theorem tailTrace_477652 : CollatzResearch.WordTrace tailWord_477652 prefixEnd_477652 218013388072418149380733 := by
  unfold tailWord_477652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8710699832777927656037605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11614266443703903541383473 8710699832777927656037605)
  ·
    refine ⟨1633256218645861435507051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8710699832777927656037605 1633256218645861435507051)
    ·
      refine ⟨2449884327968792153260577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633256218645861435507051 2449884327968792153260577)
      ·
        refine ⟨1837413245976594114945433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2449884327968792153260577 1837413245976594114945433)
        ·
          refine ⟨1378059934482445586209075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837413245976594114945433 1378059934482445586209075)
          ·
            refine ⟨2067089901723668379313613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378059934482445586209075 2067089901723668379313613)
            ·
              refine ⟨775158713146375642242605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2067089901723668379313613 775158713146375642242605)
              ·
                refine ⟨290684517429890865840977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 775158713146375642242605 290684517429890865840977)
                ·
                  refine ⟨218013388072418149380733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290684517429890865840977 218013388072418149380733)
                  ·
                    rfl

theorem cell20_477652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_477652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477652 prefixEnd_477652 := by exact prefixLift 477652
  have htrace : WordTrace (prefixWord ++ tailWord_477652) baseStart_477652 baseEnd_477652 := by
    simpa [prefixWord, tailWord_477652, baseEnd_477652] using wordTrace_append hprefix tailTrace_477652
  have hstable : (prefixWord ++ tailWord_477652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477652).length < 2 ^ (prefixWord ++ tailWord_477652).sum := by decide
  have hdescent : baseEnd_477652 < baseStart_477652 := by decide
  rcases family_descends (prefixWord ++ tailWord_477652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477663 : List Nat := [1, 1, 2, 3, 3, 4, 6]
def baseStart_477663 : Nat := 118140960795 + 477663 * 2 ^ 59
def prefixEnd_477663 : Nat := 4983230072969 + 3 ^ 40 * 477663 * 2
def baseEnd_477663 : Nat := 24224267641350111112669

theorem tailTrace_477663 : CollatzResearch.WordTrace tailWord_477663 prefixEnd_477663 24224267641350111112669 := by
  unfold tailWord_477663
  simp only [CollatzResearch.WordTrace]
  refine ⟨17421800868516004190725643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11614533912344002793817095 17421800868516004190725643)
  ·
    refine ⟨26132701302774006286088465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17421800868516004190725643 26132701302774006286088465)
    ·
      refine ⟨19599525977080504714566349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26132701302774006286088465 19599525977080504714566349)
      ·
        refine ⟨7349822241405189267962381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19599525977080504714566349 7349822241405189267962381)
        ·
          refine ⟨2756183340526945975485893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7349822241405189267962381 2756183340526945975485893)
          ·
            refine ⟨516784376348802370403605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2756183340526945975485893 516784376348802370403605)
            ·
              refine ⟨24224267641350111112669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 516784376348802370403605 24224267641350111112669)
              ·
                rfl

theorem cell20_477663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 6].length) (baseStart_477663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477663 prefixEnd_477663 := by exact prefixLift 477663
  have htrace : WordTrace (prefixWord ++ tailWord_477663) baseStart_477663 baseEnd_477663 := by
    simpa [prefixWord, tailWord_477663, baseEnd_477663] using wordTrace_append hprefix tailTrace_477663
  have hstable : (prefixWord ++ tailWord_477663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477663).length < 2 ^ (prefixWord ++ tailWord_477663).sum := by decide
  have hdescent : baseEnd_477663 < baseStart_477663 := by decide
  rcases family_descends (prefixWord ++ tailWord_477663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477669 : List Nat := [1, 3, 1, 5, 2, 1, 3, 2, 2]
def baseStart_477669 : Nat := 118140960795 + 477669 * 2 ^ 59
def prefixEnd_477669 : Nat := 4983230072969 + 3 ^ 40 * 477669 * 2
def baseEnd_477669 : Nat := 218021147335641645813997

theorem tailTrace_477669 : CollatzResearch.WordTrace tailWord_477669 prefixEnd_477669 218021147335641645813997 := by
  unfold tailWord_477669
  simp only [CollatzResearch.WordTrace]
  refine ⟨17422019706494267215444061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11614679804329511476962707 17422019706494267215444061)
  ·
    refine ⟨6533257389935350205791523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17422019706494267215444061 6533257389935350205791523)
    ·
      refine ⟨9799886084903025308687285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533257389935350205791523 9799886084903025308687285)
      ·
        refine ⟨918739320459658622689433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9799886084903025308687285 918739320459658622689433)
        ·
          refine ⟨689054490344743967017075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918739320459658622689433 689054490344743967017075)
          ·
            refine ⟨1033581735517115950525613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689054490344743967017075 1033581735517115950525613)
            ·
              refine ⟨387593150818918481447105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033581735517115950525613 387593150818918481447105)
              ·
                refine ⟨290694863114188861085329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387593150818918481447105 290694863114188861085329)
                ·
                  refine ⟨218021147335641645813997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290694863114188861085329 218021147335641645813997)
                  ·
                    rfl

theorem cell20_477669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_477669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477669 prefixEnd_477669 := by exact prefixLift 477669
  have htrace : WordTrace (prefixWord ++ tailWord_477669) baseStart_477669 baseEnd_477669 := by
    simpa [prefixWord, tailWord_477669, baseEnd_477669] using wordTrace_append hprefix tailTrace_477669
  have hstable : (prefixWord ++ tailWord_477669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477669).length < 2 ^ (prefixWord ++ tailWord_477669).sum := by decide
  have hdescent : baseEnd_477669 < baseStart_477669 := by decide
  rcases family_descends (prefixWord ++ tailWord_477669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477725 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 3]
def baseStart_477725 : Nat := 118140960795 + 477725 * 2 ^ 59
def prefixEnd_477725 : Nat := 4983230072969 + 3 ^ 40 * 477725 * 2
def baseEnd_477725 : Nat := 218046707261554339947101

theorem tailTrace_477725 : CollatzResearch.WordTrace tailWord_477725 prefixEnd_477725 218046707261554339947101 := by
  unfold tailWord_477725
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424062194291388779482629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11616041462860925852988419 17424062194291388779482629)
  ·
    refine ⟨3267011661429635396152993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17424062194291388779482629 3267011661429635396152993)
    ·
      refine ⟨2450258746072226547114745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3267011661429635396152993 2450258746072226547114745)
      ·
        refine ⟨1837694059554169910336059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2450258746072226547114745 1837694059554169910336059)
        ·
          refine ⟨2756541089331254865504089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837694059554169910336059 2756541089331254865504089)
          ·
            refine ⟨2067405816998441149128067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756541089331254865504089 2067405816998441149128067)
            ·
              refine ⟨3101108725497661723692101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067405816998441149128067 3101108725497661723692101)
              ·
                refine ⟨581457886030811573192269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3101108725497661723692101 581457886030811573192269)
                ·
                  refine ⟨218046707261554339947101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581457886030811573192269 218046707261554339947101)
                  ·
                    rfl

theorem cell20_477725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_477725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477725 prefixEnd_477725 := by exact prefixLift 477725
  have htrace : WordTrace (prefixWord ++ tailWord_477725) baseStart_477725 baseEnd_477725 := by
    simpa [prefixWord, tailWord_477725, baseEnd_477725] using wordTrace_append hprefix tailTrace_477725
  have hstable : (prefixWord ++ tailWord_477725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477725).length < 2 ^ (prefixWord ++ tailWord_477725).sum := by decide
  have hdescent : baseEnd_477725 < baseStart_477725 := by decide
  rcases family_descends (prefixWord ++ tailWord_477725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477728 : List Nat := [2, 1, 1, 6, 2, 1, 1, 4, 2]
def baseStart_477728 : Nat := 118140960795 + 477728 * 2 ^ 59
def prefixEnd_477728 : Nat := 4983230072969 + 3 ^ 40 * 477728 * 2
def baseEnd_477728 : Nat := 218048076543299662847089

theorem tailTrace_477728 : CollatzResearch.WordTrace tailWord_477728 prefixEnd_477728 218048076543299662847089 := by
  unfold tailWord_477728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712085806640260145920919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11616114408853680194561225 8712085806640260145920919)
  ·
    refine ⟨13068128709960390218881379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8712085806640260145920919 13068128709960390218881379)
    ·
      refine ⟨19602193064940585328322069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13068128709960390218881379 19602193064940585328322069)
      ·
        refine ⟨918852799919089937265097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19602193064940585328322069 918852799919089937265097)
        ·
          refine ⟨689139599939317452948823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918852799919089937265097 689139599939317452948823)
          ·
            refine ⟨1033709399908976179423235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689139599939317452948823 1033709399908976179423235)
            ·
              refine ⟨1550564099863464269134853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033709399908976179423235 1550564099863464269134853)
              ·
                refine ⟨290730768724399550462785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1550564099863464269134853 290730768724399550462785)
                ·
                  refine ⟨218048076543299662847089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290730768724399550462785 218048076543299662847089)
                  ·
                    rfl

theorem cell20_477728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_477728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477728 prefixEnd_477728 := by exact prefixLift 477728
  have htrace : WordTrace (prefixWord ++ tailWord_477728) baseStart_477728 baseEnd_477728 := by
    simpa [prefixWord, tailWord_477728, baseEnd_477728] using wordTrace_append hprefix tailTrace_477728
  have hstable : (prefixWord ++ tailWord_477728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477728).length < 2 ^ (prefixWord ++ tailWord_477728).sum := by decide
  have hdescent : baseEnd_477728 < baseStart_477728 := by decide
  rcases family_descends (prefixWord ++ tailWord_477728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477756 : List Nat := [2, 2, 2, 2, 3, 2, 3, 4]
def baseStart_477756 : Nat := 118140960795 + 477756 * 2 ^ 59
def prefixEnd_477756 : Nat := 4983230072969 + 3 ^ 40 * 477756 * 2
def baseEnd_477756 : Nat := 72686952168752003304547

theorem tailTrace_477756 : CollatzResearch.WordTrace tailWord_477756 prefixEnd_477756 72686952168752003304547 := by
  unfold tailWord_477756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712596428589540536930561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11616795238119387382574081 8712596428589540536930561)
  ·
    refine ⟨6534447321442155402697921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8712596428589540536930561 6534447321442155402697921)
    ·
      refine ⟨4900835491081616552023441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6534447321442155402697921 4900835491081616552023441)
      ·
        refine ⟨3675626618311212414017581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900835491081616552023441 3675626618311212414017581)
        ·
          refine ⟨1378359981866704655256593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3675626618311212414017581 1378359981866704655256593)
          ·
            refine ⟨1033769986400028491442445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378359981866704655256593 1033769986400028491442445)
            ·
              refine ⟨387663744900010684290917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033769986400028491442445 387663744900010684290917)
              ·
                refine ⟨72686952168752003304547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387663744900010684290917 72686952168752003304547)
                ·
                  rfl

theorem cell20_477756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_477756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477756 prefixEnd_477756 := by exact prefixLift 477756
  have htrace : WordTrace (prefixWord ++ tailWord_477756) baseStart_477756 baseEnd_477756 := by
    simpa [prefixWord, tailWord_477756, baseEnd_477756] using wordTrace_append hprefix tailTrace_477756
  have hstable : (prefixWord ++ tailWord_477756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477756).length < 2 ^ (prefixWord ++ tailWord_477756).sum := by decide
  have hdescent : baseEnd_477756 < baseStart_477756 := by decide
  rcases family_descends (prefixWord ++ tailWord_477756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477760 : List Nat := [2, 1, 1, 2, 2, 2, 2, 8]
def baseStart_477760 : Nat := 118140960795 + 477760 * 2 ^ 59
def prefixEnd_477760 : Nat := 4983230072969 + 3 ^ 40 * 477760 * 2
def baseEnd_477760 : Nat := 72687560738416591260097

theorem tailTrace_477760 : CollatzResearch.WordTrace tailWord_477760 prefixEnd_477760 72687560738416591260097 := by
  unfold tailWord_477760
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712669374582294878503367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11616892499443059838004489 8712669374582294878503367)
  ·
    refine ⟨13069004061873442317755051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8712669374582294878503367 13069004061873442317755051)
    ·
      refine ⟨19603506092810163476632577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13069004061873442317755051 19603506092810163476632577)
      ·
        refine ⟨14702629569607622607474433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19603506092810163476632577 14702629569607622607474433)
        ·
          refine ⟨11026972177205716955605825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14702629569607622607474433 11026972177205716955605825)
          ·
            refine ⟨8270229132904287716704369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11026972177205716955605825 8270229132904287716704369)
            ·
              refine ⟨6202671849678215787528277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8270229132904287716704369 6202671849678215787528277)
              ·
                refine ⟨72687560738416591260097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6202671849678215787528277 72687560738416591260097)
                ·
                  rfl

theorem cell20_477760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_477760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477760 prefixEnd_477760 := by exact prefixLift 477760
  have htrace : WordTrace (prefixWord ++ tailWord_477760) baseStart_477760 baseEnd_477760 := by
    simpa [prefixWord, tailWord_477760, baseEnd_477760] using wordTrace_append hprefix tailTrace_477760
  have hstable : (prefixWord ++ tailWord_477760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477760).length < 2 ^ (prefixWord ++ tailWord_477760).sum := by decide
  have hdescent : baseEnd_477760 < baseStart_477760 := by decide
  rcases family_descends (prefixWord ++ tailWord_477760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477780 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_477780 : Nat := 118140960795 + 477780 * 2 ^ 59
def prefixEnd_477780 : Nat := 4983230072969 + 3 ^ 40 * 477780 * 2
def baseEnd_477780 : Nat := 218071810760218593113543

theorem tailTrace_477780 : CollatzResearch.WordTrace tailWord_477780 prefixEnd_477780 218071810760218593113543 := by
  unfold tailWord_477780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713034104546066586367397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11617378806061422115156529 8713034104546066586367397)
  ·
    refine ⟨1633693894602387484943887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8713034104546066586367397 1633693894602387484943887)
    ·
      refine ⟨2450540841903581227415831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633693894602387484943887 2450540841903581227415831)
      ·
        refine ⟨3675811262855371841123747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450540841903581227415831 3675811262855371841123747)
        ·
          refine ⟨5513716894283057761685621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675811262855371841123747 5513716894283057761685621)
          ·
            refine ⟨516910958839036665158027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5513716894283057761685621 516910958839036665158027)
            ·
              refine ⟨775366438258554997737041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516910958839036665158027 775366438258554997737041)
              ·
                refine ⟨581524828693916248302781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775366438258554997737041 581524828693916248302781)
                ·
                  refine ⟨218071810760218593113543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581524828693916248302781 218071810760218593113543)
                  ·
                    rfl

theorem cell20_477780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_477780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477780 prefixEnd_477780 := by exact prefixLift 477780
  have htrace : WordTrace (prefixWord ++ tailWord_477780) baseStart_477780 baseEnd_477780 := by
    simpa [prefixWord, tailWord_477780, baseEnd_477780] using wordTrace_append hprefix tailTrace_477780
  have hstable : (prefixWord ++ tailWord_477780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477780).length < 2 ^ (prefixWord ++ tailWord_477780).sum := by decide
  have hdescent : baseEnd_477780 < baseStart_477780 := by decide
  rcases family_descends (prefixWord ++ tailWord_477780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477815 : List Nat := [1, 1, 3, 1, 1, 3, 6, 4]
def baseStart_477815 : Nat := 118140960795 + 477815 * 2 ^ 59
def prefixEnd_477815 : Nat := 4983230072969 + 3 ^ 40 * 477815 * 2
def baseEnd_477815 : Nat := 72695928571304675648911

theorem tailTrace_477815 : CollatzResearch.WordTrace tailWord_477815 prefixEnd_477815 72695928571304675648911 := by
  unfold tailWord_477815
  simp only [CollatzResearch.WordTrace]
  refine ⟨17427344763965334150258899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11618229842643556100172599 17427344763965334150258899)
  ·
    refine ⟨26141017145948001225388349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17427344763965334150258899 26141017145948001225388349)
    ·
      refine ⟨9802881429730500459520631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26141017145948001225388349 9802881429730500459520631)
      ·
        refine ⟨14704322144595750689280947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9802881429730500459520631 14704322144595750689280947)
        ·
          refine ⟨22056483216893626033921421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14704322144595750689280947 22056483216893626033921421)
          ·
            refine ⟨8271181206335109762720533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22056483216893626033921421 8271181206335109762720533)
            ·
              refine ⟨387711619046958270127525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8271181206335109762720533 387711619046958270127525)
              ·
                refine ⟨72695928571304675648911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387711619046958270127525 72695928571304675648911)
                ·
                  rfl

theorem cell20_477815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_477815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477815 prefixEnd_477815 := by exact prefixLift 477815
  have htrace : WordTrace (prefixWord ++ tailWord_477815) baseStart_477815 baseEnd_477815 := by
    simpa [prefixWord, tailWord_477815, baseEnd_477815] using wordTrace_append hprefix tailTrace_477815
  have hstable : (prefixWord ++ tailWord_477815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477815).length < 2 ^ (prefixWord ++ tailWord_477815).sum := by decide
  have hdescent : baseEnd_477815 < baseStart_477815 := by decide
  rcases family_descends (prefixWord ++ tailWord_477815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477821 : List Nat := [1, 4, 1, 1, 6, 1, 1, 3, 2]
def baseStart_477821 : Nat := 118140960795 + 477821 * 2 ^ 59
def prefixEnd_477821 : Nat := 4983230072969 + 3 ^ 40 * 477821 * 2
def baseEnd_477821 : Nat := 218090524277404672746709

theorem tailTrace_477821 : CollatzResearch.WordTrace tailWord_477821 prefixEnd_477821 218090524277404672746709 := by
  unfold tailWord_477821
  simp only [CollatzResearch.WordTrace]
  refine ⟨17427563601943597174977317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11618375734629064783318211 17427563601943597174977317)
  ·
    refine ⟨3267668175364424470308247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17427563601943597174977317 3267668175364424470308247)
    ·
      refine ⟨4901502263046636705462371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267668175364424470308247 4901502263046636705462371)
      ·
        refine ⟨7352253394569955058193557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901502263046636705462371 7352253394569955058193557)
        ·
          refine ⟨344636877870466643352823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7352253394569955058193557 344636877870466643352823)
          ·
            refine ⟨516955316805699965029235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344636877870466643352823 516955316805699965029235)
            ·
              refine ⟨775432975208549947543853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516955316805699965029235 775432975208549947543853)
              ·
                refine ⟨290787365703206230328945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 775432975208549947543853 290787365703206230328945)
                ·
                  refine ⟨218090524277404672746709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290787365703206230328945 218090524277404672746709)
                  ·
                    rfl

theorem cell20_477821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_477821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477821 prefixEnd_477821 := by exact prefixLift 477821
  have htrace : WordTrace (prefixWord ++ tailWord_477821) baseStart_477821 baseEnd_477821 := by
    simpa [prefixWord, tailWord_477821, baseEnd_477821] using wordTrace_append hprefix tailTrace_477821
  have hstable : (prefixWord ++ tailWord_477821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477821).length < 2 ^ (prefixWord ++ tailWord_477821).sum := by decide
  have hdescent : baseEnd_477821 < baseStart_477821 := by decide
  rcases family_descends (prefixWord ++ tailWord_477821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477870 : List Nat := [4, 1, 4, 1, 1, 1, 2, 6]
def baseStart_477870 : Nat := 118140960795 + 477870 * 2 ^ 59
def prefixEnd_477870 : Nat := 4983230072969 + 3 ^ 40 * 477870 * 2
def baseEnd_477870 : Nat := 72704296404192760037725

theorem tailTrace_477870 : CollatzResearch.WordTrace tailWord_477870 prefixEnd_477870 72704296404192760037725 := by
  unfold tailWord_477870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178668847345759817938883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11619567185844052362340709 2178668847345759817938883)
  ·
    refine ⟨3268003271018639726908325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2178668847345759817938883 3268003271018639726908325)
    ·
      refine ⟨612750613315994948795311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3268003271018639726908325 612750613315994948795311)
      ·
        refine ⟨919125919973992423192967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612750613315994948795311 919125919973992423192967)
        ·
          refine ⟨1378688879960988634789451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919125919973992423192967 1378688879960988634789451)
          ·
            refine ⟨2068033319941482952184177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378688879960988634789451 2068033319941482952184177)
            ·
              refine ⟨1551024989956112214138133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068033319941482952184177 1551024989956112214138133)
              ·
                refine ⟨72704296404192760037725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1551024989956112214138133 72704296404192760037725)
                ·
                  rfl

theorem cell20_477870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_477870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477870 prefixEnd_477870 := by exact prefixLift 477870
  have htrace : WordTrace (prefixWord ++ tailWord_477870) baseStart_477870 baseEnd_477870 := by
    simpa [prefixWord, tailWord_477870, baseEnd_477870] using wordTrace_append hprefix tailTrace_477870
  have hstable : (prefixWord ++ tailWord_477870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477870).length < 2 ^ (prefixWord ++ tailWord_477870).sum := by decide
  have hdescent : baseEnd_477870 < baseStart_477870 := by decide
  rcases family_descends (prefixWord ++ tailWord_477870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477905 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_477905 : Nat := 118140960795 + 477905 * 2 ^ 59
def prefixEnd_477905 : Nat := 4983230072969 + 3 ^ 40 * 477905 * 2
def baseEnd_477905 : Nat := 218128864166273713946365

theorem tailTrace_477905 : CollatzResearch.WordTrace tailWord_477905 prefixEnd_477905 218128864166273713946365 := by
  unfold tailWord_477905
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430627333639279521035169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11620418222426186347356779 17430627333639279521035169)
  ·
    refine ⟨13072970500229459640776377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17430627333639279521035169 13072970500229459640776377)
    ·
      refine ⟨9804727875172094730582283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13072970500229459640776377 9804727875172094730582283)
      ·
        refine ⟨14707091812758142095873425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9804727875172094730582283 14707091812758142095873425)
        ·
          refine ⟨11030318859568606571905069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14707091812758142095873425 11030318859568606571905069)
          ·
            refine ⟨4136369572338227464464401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11030318859568606571905069 4136369572338227464464401)
            ·
              refine ⟨3102277179253670598348301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136369572338227464464401 3102277179253670598348301)
              ·
                refine ⟨1163353942220126474380613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3102277179253670598348301 1163353942220126474380613)
                ·
                  refine ⟨218128864166273713946365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163353942220126474380613 218128864166273713946365)
                  ·
                    rfl

theorem cell20_477905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_477905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477905 prefixEnd_477905 := by exact prefixLift 477905
  have htrace : WordTrace (prefixWord ++ tailWord_477905) baseStart_477905 baseEnd_477905 := by
    simpa [prefixWord, tailWord_477905, baseEnd_477905] using wordTrace_append hprefix tailTrace_477905
  have hstable : (prefixWord ++ tailWord_477905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477905).length < 2 ^ (prefixWord ++ tailWord_477905).sum := by decide
  have hdescent : baseEnd_477905 < baseStart_477905 := by decide
  rcases family_descends (prefixWord ++ tailWord_477905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477960 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_477960 : Nat := 118140960795 + 477960 * 2 ^ 59
def prefixEnd_477960 : Nat := 4983230072969 + 3 ^ 40 * 477960 * 2
def baseEnd_477960 : Nat := 218153967664937967112807

theorem tailTrace_477960 : CollatzResearch.WordTrace tailWord_477960 prefixEnd_477960 218153967664937967112807 := by
  unfold tailWord_477960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8716316674220011957143667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11621755565626682609524889 8716316674220011957143667)
  ·
    refine ⟨13074475011330017935715501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8716316674220011957143667 13074475011330017935715501)
    ·
      refine ⟨4902928129248756725893313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13074475011330017935715501 4902928129248756725893313)
      ·
        refine ⟨3677196096936567544419985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4902928129248756725893313 3677196096936567544419985)
        ·
          refine ⟨2757897072702425658314989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677196096936567544419985 2757897072702425658314989)
          ·
            refine ⟨1034211402263409621868121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2757897072702425658314989 1034211402263409621868121)
            ·
              refine ⟨775658551697557216401091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034211402263409621868121 775658551697557216401091)
              ·
                refine ⟨1163487827546335824601637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775658551697557216401091 1163487827546335824601637)
                ·
                  refine ⟨218153967664937967112807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163487827546335824601637 218153967664937967112807)
                  ·
                    rfl

theorem cell20_477960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_477960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477960 prefixEnd_477960 := by exact prefixLift 477960
  have htrace : WordTrace (prefixWord ++ tailWord_477960) baseStart_477960 baseEnd_477960 := by
    simpa [prefixWord, tailWord_477960, baseEnd_477960] using wordTrace_append hprefix tailTrace_477960
  have hstable : (prefixWord ++ tailWord_477960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477960).length < 2 ^ (prefixWord ++ tailWord_477960).sum := by decide
  have hdescent : baseEnd_477960 < baseStart_477960 := by decide
  rcases family_descends (prefixWord ++ tailWord_477960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477984 : List Nat := [2, 1, 1, 5, 1, 4, 2, 4]
def baseStart_477984 : Nat := 118140960795 + 477984 * 2 ^ 59
def prefixEnd_477984 : Nat := 4983230072969 + 3 ^ 40 * 477984 * 2
def baseEnd_477984 : Nat := 72721640639633516770903

theorem tailTrace_477984 : CollatzResearch.WordTrace tailWord_477984 prefixEnd_477984 72721640639633516770903 := by
  unfold tailWord_477984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8716754350176538006580503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11622339133568717342107337 8716754350176538006580503)
  ·
    refine ⟨13075131525264807009870755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8716754350176538006580503 13075131525264807009870755)
    ·
      refine ⟨19612697287897210514806133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13075131525264807009870755 19612697287897210514806133)
      ·
        refine ⟨1838690370740363485763075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19612697287897210514806133 1838690370740363485763075)
        ·
          refine ⟨2758035556110545228644613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838690370740363485763075 2758035556110545228644613)
          ·
            refine ⟨517131666770727230370865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2758035556110545228644613 517131666770727230370865)
            ·
              refine ⟨387848750078045422778149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517131666770727230370865 387848750078045422778149)
              ·
                refine ⟨72721640639633516770903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387848750078045422778149 72721640639633516770903)
                ·
                  rfl

theorem cell20_477984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_477984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477984 prefixEnd_477984 := by exact prefixLift 477984
  have htrace : WordTrace (prefixWord ++ tailWord_477984) baseStart_477984 baseEnd_477984 := by
    simpa [prefixWord, tailWord_477984, baseEnd_477984] using wordTrace_append hprefix tailTrace_477984
  have hstable : (prefixWord ++ tailWord_477984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477984).length < 2 ^ (prefixWord ++ tailWord_477984).sum := by decide
  have hdescent : baseEnd_477984 < baseStart_477984 := by decide
  rcases family_descends (prefixWord ++ tailWord_477984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477995 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_477995 : Nat := 118140960795 + 477995 * 2 ^ 59
def prefixEnd_477995 : Nat := 4983230072969 + 3 ^ 40 * 477995 * 2
def baseEnd_477995 : Nat := 218169942618633400945997

theorem tailTrace_477995 : CollatzResearch.WordTrace tailWord_477995 prefixEnd_477995 218169942618633400945997 := by
  unfold tailWord_477995
  simp only [CollatzResearch.WordTrace]
  refine ⟨17433909903313224891811439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11622606602208816594540959 17433909903313224891811439)
  ·
    refine ⟨26150864854969837337717159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17433909903313224891811439 26150864854969837337717159)
    ·
      refine ⟨39226297282454756006575739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26150864854969837337717159 39226297282454756006575739)
      ·
        refine ⟨58839445923682134009863609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39226297282454756006575739 58839445923682134009863609)
        ·
          refine ⟨44129584442761600507397707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58839445923682134009863609 44129584442761600507397707)
          ·
            refine ⟨66194376664142400761096561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44129584442761600507397707 66194376664142400761096561)
            ·
              refine ⟨49645782498106800570822421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66194376664142400761096561 49645782498106800570822421)
              ·
                refine ⟨2327146054598756276757301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49645782498106800570822421 2327146054598756276757301)
                ·
                  refine ⟨218169942618633400945997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2327146054598756276757301 218169942618633400945997)
                  ·
                    rfl

theorem cell20_477995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_477995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_477995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_477995 prefixEnd_477995 := by exact prefixLift 477995
  have htrace : WordTrace (prefixWord ++ tailWord_477995) baseStart_477995 baseEnd_477995 := by
    simpa [prefixWord, tailWord_477995, baseEnd_477995] using wordTrace_append hprefix tailTrace_477995
  have hstable : (prefixWord ++ tailWord_477995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477995).length < 2 ^ (prefixWord ++ tailWord_477995).sum := by decide
  have hdescent : baseEnd_477995 < baseStart_477995 := by decide
  rcases family_descends (prefixWord ++ tailWord_477995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478005 : List Nat := [1, 3, 3, 1, 3, 3, 6]
def baseStart_478005 : Nat := 118140960795 + 478005 * 2 ^ 59
def prefixEnd_478005 : Nat := 4983230072969 + 3 ^ 40 * 478005 * 2
def baseEnd_478005 : Nat := 24241611876790867845847

theorem tailTrace_478005 : CollatzResearch.WordTrace tailWord_478005 prefixEnd_478005 24241611876790867845847 := by
  unfold tailWord_478005
  simp only [CollatzResearch.WordTrace]
  refine ⟨17434274633276996599675469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11622849755517997733116979 17434274633276996599675469)
  ·
    refine ⟨6537852987478873724878301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17434274633276996599675469 6537852987478873724878301)
    ·
      refine ⟨2451694870304577646829363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6537852987478873724878301 2451694870304577646829363)
      ·
        refine ⟨3677542305456866470244045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451694870304577646829363 3677542305456866470244045)
        ·
          refine ⟨1379078364546324926341517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3677542305456866470244045 1379078364546324926341517)
          ·
            refine ⟨517154386704871847378069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1379078364546324926341517 517154386704871847378069)
            ·
              refine ⟨24241611876790867845847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 517154386704871847378069 24241611876790867845847)
              ·
                rfl

theorem cell20_478005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 6].length) (baseStart_478005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478005 prefixEnd_478005 := by exact prefixLift 478005
  have htrace : WordTrace (prefixWord ++ tailWord_478005) baseStart_478005 baseEnd_478005 := by
    simpa [prefixWord, tailWord_478005, baseEnd_478005] using wordTrace_append hprefix tailTrace_478005
  have hstable : (prefixWord ++ tailWord_478005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478005).length < 2 ^ (prefixWord ++ tailWord_478005).sum := by decide
  have hdescent : baseEnd_478005 < baseStart_478005 := by decide
  rcases family_descends (prefixWord ++ tailWord_478005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478012 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_478012 : Nat := 118140960795 + 478012 * 2 ^ 59
def prefixEnd_478012 : Nat := 4983230072969 + 3 ^ 40 * 478012 * 2
def baseEnd_478012 : Nat := 218177701881856897379261

theorem tailTrace_478012 : CollatzResearch.WordTrace tailWord_478012 prefixEnd_478012 218177701881856897379261 := by
  unfold tailWord_478012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717264972125818397590145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11623019962834424530120193 8717264972125818397590145)
  ·
    refine ⟨6537948729094363798192609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8717264972125818397590145 6537948729094363798192609)
    ·
      refine ⟨4903461546820772848644457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6537948729094363798192609 4903461546820772848644457)
      ·
        refine ⟨3677596160115579636483343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4903461546820772848644457 3677596160115579636483343)
        ·
          refine ⟨5516394240173369454725015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677596160115579636483343 5516394240173369454725015)
          ·
            refine ⟨8274591360260054182087523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516394240173369454725015 8274591360260054182087523)
            ·
              refine ⟨12411887040390081273131285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274591360260054182087523 12411887040390081273131285)
              ·
                refine ⟨581807205018285059678029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12411887040390081273131285 581807205018285059678029)
                ·
                  refine ⟨218177701881856897379261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581807205018285059678029 218177701881856897379261)
                  ·
                    rfl

theorem cell20_478012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_478012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478012 prefixEnd_478012 := by exact prefixLift 478012
  have htrace : WordTrace (prefixWord ++ tailWord_478012) baseStart_478012 baseEnd_478012 := by
    simpa [prefixWord, tailWord_478012, baseEnd_478012] using wordTrace_append hprefix tailTrace_478012
  have hstable : (prefixWord ++ tailWord_478012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478012).length < 2 ^ (prefixWord ++ tailWord_478012).sum := by decide
  have hdescent : baseEnd_478012 < baseStart_478012 := by decide
  rcases family_descends (prefixWord ++ tailWord_478012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478070 : List Nat := [5, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_478070 : Nat := 118140960795 + 478070 * 2 ^ 59
def prefixEnd_478070 : Nat := 4983230072969 + 3 ^ 40 * 478070 * 2
def baseEnd_478070 : Nat := 218204174662266473445691

theorem tailTrace_478070 : CollatzResearch.WordTrace tailWord_478070 prefixEnd_478070 218204174662266473445691 := by
  unfold tailWord_478070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089790336127594543799479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11624430252027675133861109 1089790336127594543799479)
  ·
    refine ⟨1634685504191391815699219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089790336127594543799479 1634685504191391815699219)
    ·
      refine ⟨2452028256287087723548829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634685504191391815699219 2452028256287087723548829)
      ·
        refine ⟨919510596107657896330811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2452028256287087723548829 919510596107657896330811)
        ·
          refine ⟨1379265894161486844496217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919510596107657896330811 1379265894161486844496217)
          ·
            refine ⟨1034449420621115133372163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1379265894161486844496217 1034449420621115133372163)
            ·
              refine ⟨1551674130931672700058245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034449420621115133372163 1551674130931672700058245)
              ·
                refine ⟨290938899549688631260921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1551674130931672700058245 290938899549688631260921)
                ·
                  refine ⟨218204174662266473445691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290938899549688631260921 218204174662266473445691)
                  ·
                    rfl

theorem cell20_478070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_478070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478070 prefixEnd_478070 := by exact prefixLift 478070
  have htrace : WordTrace (prefixWord ++ tailWord_478070) baseStart_478070 baseEnd_478070 := by
    simpa [prefixWord, tailWord_478070, baseEnd_478070] using wordTrace_append hprefix tailTrace_478070
  have hstable : (prefixWord ++ tailWord_478070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478070).length < 2 ^ (prefixWord ++ tailWord_478070).sum := by decide
  have hdescent : baseEnd_478070 < baseStart_478070 := by decide
  rcases family_descends (prefixWord ++ tailWord_478070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478071 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_478071 : Nat := 118140960795 + 478071 * 2 ^ 59
def prefixEnd_478071 : Nat := 4983230072969 + 3 ^ 40 * 478071 * 2
def baseEnd_478071 : Nat := 218204631089514914412353

theorem tailTrace_478071 : CollatzResearch.WordTrace tailWord_478071 prefixEnd_478071 218204631089514914412353 := by
  unfold tailWord_478071
  simp only [CollatzResearch.WordTrace]
  refine ⟨17436681851037889871578067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11624454567358593247718711 17436681851037889871578067)
  ·
    refine ⟨26155022776556834807367101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17436681851037889871578067 26155022776556834807367101)
    ·
      refine ⟨9808133541208813052762663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26155022776556834807367101 9808133541208813052762663)
      ·
        refine ⟨14712200311813219579143995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9808133541208813052762663 14712200311813219579143995)
        ·
          refine ⟨22068300467719829368715993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14712200311813219579143995 22068300467719829368715993)
          ·
            refine ⟨16551225350789872026536995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22068300467719829368715993 16551225350789872026536995)
            ·
              refine ⟨24826838026184808039805493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16551225350789872026536995 24826838026184808039805493)
              ·
                refine ⟨2327516064954825753731765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24826838026184808039805493 2327516064954825753731765)
                ·
                  refine ⟨218204631089514914412353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2327516064954825753731765 218204631089514914412353)
                  ·
                    rfl

theorem cell20_478071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_478071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478071 prefixEnd_478071 := by exact prefixLift 478071
  have htrace : WordTrace (prefixWord ++ tailWord_478071) baseStart_478071 baseEnd_478071 := by
    simpa [prefixWord, tailWord_478071, baseEnd_478071] using wordTrace_append hprefix tailTrace_478071
  have hstable : (prefixWord ++ tailWord_478071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478071).length < 2 ^ (prefixWord ++ tailWord_478071).sum := by decide
  have hdescent : baseEnd_478071 < baseStart_478071 := by decide
  rcases family_descends (prefixWord ++ tailWord_478071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478108 : List Nat := [2, 2, 3, 3, 2, 1, 2, 3, 2]
def baseStart_478108 : Nat := 118140960795 + 478108 * 2 ^ 59
def prefixEnd_478108 : Nat := 4983230072969 + 3 ^ 40 * 478108 * 2
def baseEnd_478108 : Nat := 218221518897707230178869

theorem tailTrace_478108 : CollatzResearch.WordTrace tailWord_478108 prefixEnd_478108 218221518897707230178869 := by
  unfold tailWord_478108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719015675951922595337489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11625354234602563460449985 8719015675951922595337489)
  ·
    refine ⟨6539261756963941946503117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8719015675951922595337489 6539261756963941946503117)
    ·
      refine ⟨2452223158861478229938669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6539261756963941946503117 2452223158861478229938669)
      ·
        refine ⟨919583684573054336227001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2452223158861478229938669 919583684573054336227001)
        ·
          refine ⟨689687763429790752170251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919583684573054336227001 689687763429790752170251)
          ·
            refine ⟨1034531645144686128255377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689687763429790752170251 1034531645144686128255377)
            ·
              refine ⟨775898733858514596191533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034531645144686128255377 775898733858514596191533)
              ·
                refine ⟨290962025196942973571825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 775898733858514596191533 290962025196942973571825)
                ·
                  refine ⟨218221518897707230178869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290962025196942973571825 218221518897707230178869)
                  ·
                    rfl

theorem cell20_478108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_478108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478108 prefixEnd_478108 := by exact prefixLift 478108
  have htrace : WordTrace (prefixWord ++ tailWord_478108) baseStart_478108 baseEnd_478108 := by
    simpa [prefixWord, tailWord_478108, baseEnd_478108] using wordTrace_append hprefix tailTrace_478108
  have hstable : (prefixWord ++ tailWord_478108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478108).length < 2 ^ (prefixWord ++ tailWord_478108).sum := by decide
  have hdescent : baseEnd_478108 < baseStart_478108 := by decide
  rcases family_descends (prefixWord ++ tailWord_478108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478112 : List Nat := [2, 1, 1, 4, 1, 1, 3, 5, 2]
def baseStart_478112 : Nat := 118140960795 + 478112 * 2 ^ 59
def prefixEnd_478112 : Nat := 4983230072969 + 3 ^ 40 * 478112 * 2
def baseEnd_478112 : Nat := 218223344606700994045519

theorem tailTrace_478112 : CollatzResearch.WordTrace tailWord_478112 prefixEnd_478112 218223344606700994045519 := by
  unfold tailWord_478112
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719088621944676936910295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11625451495926235915880393 8719088621944676936910295)
  ·
    refine ⟨13078632932917015405365443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8719088621944676936910295 13078632932917015405365443)
    ·
      refine ⟨19617949399375523108048165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13078632932917015405365443 19617949399375523108048165)
      ·
        refine ⟨3678365512382910582759031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19617949399375523108048165 3678365512382910582759031)
        ·
          refine ⟨5517548268574365874138547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678365512382910582759031 5517548268574365874138547)
          ·
            refine ⟨8276322402861548811207821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517548268574365874138547 8276322402861548811207821)
            ·
              refine ⟨3103620901073080804202933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8276322402861548811207821 3103620901073080804202933)
              ·
                refine ⟨290964459475601325394025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3103620901073080804202933 290964459475601325394025)
                ·
                  refine ⟨218223344606700994045519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290964459475601325394025 218223344606700994045519)
                  ·
                    rfl

theorem cell20_478112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_478112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478112 prefixEnd_478112 := by exact prefixLift 478112
  have htrace : WordTrace (prefixWord ++ tailWord_478112) baseStart_478112 baseEnd_478112 := by
    simpa [prefixWord, tailWord_478112, baseEnd_478112] using wordTrace_append hprefix tailTrace_478112
  have hstable : (prefixWord ++ tailWord_478112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478112).length < 2 ^ (prefixWord ++ tailWord_478112).sum := by decide
  have hdescent : baseEnd_478112 < baseStart_478112 := by decide
  rcases family_descends (prefixWord ++ tailWord_478112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478119 : List Nat := [1, 1, 6, 1, 3, 1, 7]
def baseStart_478119 : Nat := 118140960795 + 478119 * 2 ^ 59
def prefixEnd_478119 : Nat := 4983230072969 + 3 ^ 40 * 478119 * 2
def baseEnd_478119 : Nat := 24247393288604453423573

theorem tailTrace_478119 : CollatzResearch.WordTrace tailWord_478119 prefixEnd_478119 24247393288604453423573 := by
  unfold tailWord_478119
  simp only [CollatzResearch.WordTrace]
  refine ⟨17438432554863994069325411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11625621703242662712883607 17438432554863994069325411)
  ·
    refine ⟨26157648832295991103988117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17438432554863994069325411 26157648832295991103988117)
    ·
      refine ⟨1226139789013874582999443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26157648832295991103988117 1226139789013874582999443)
      ·
        refine ⟨1839209683520811874499165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226139789013874582999443 1839209683520811874499165)
        ·
          refine ⟨689703631320304452937187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1839209683520811874499165 689703631320304452937187)
          ·
            refine ⟨1034555446980456679405781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689703631320304452937187 1034555446980456679405781)
            ·
              refine ⟨24247393288604453423573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1034555446980456679405781 24247393288604453423573)
              ·
                rfl

theorem cell20_478119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 7].length) (baseStart_478119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478119 prefixEnd_478119 := by exact prefixLift 478119
  have htrace : WordTrace (prefixWord ++ tailWord_478119) baseStart_478119 baseEnd_478119 := by
    simpa [prefixWord, tailWord_478119, baseEnd_478119] using wordTrace_append hprefix tailTrace_478119
  have hstable : (prefixWord ++ tailWord_478119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478119).length < 2 ^ (prefixWord ++ tailWord_478119).sum := by decide
  have hdescent : baseEnd_478119 < baseStart_478119 := by decide
  rcases family_descends (prefixWord ++ tailWord_478119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478164 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_478164 : Nat := 118140960795 + 478164 * 2 ^ 59
def prefixEnd_478164 : Nat := 4983230072969 + 3 ^ 40 * 478164 * 2
def baseEnd_478164 : Nat := 218247078823619924311973

theorem tailTrace_478164 : CollatzResearch.WordTrace tailWord_478164 prefixEnd_478164 218247078823619924311973 := by
  unfold tailWord_478164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8720036919850483377356773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11626715893133977836475697 8720036919850483377356773)
  ·
    refine ⟨1635006922471965633254395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8720036919850483377356773 1635006922471965633254395)
    ·
      refine ⟨2452510383707948449881593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635006922471965633254395 2452510383707948449881593)
      ·
        refine ⟨1839382787780961337411195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2452510383707948449881593 1839382787780961337411195)
        ·
          refine ⟨2759074181671442006116793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839382787780961337411195 2759074181671442006116793)
          ·
            refine ⟨2069305636253581504587595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2759074181671442006116793 2069305636253581504587595)
            ·
              refine ⟨3103958454380372256881393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069305636253581504587595 3103958454380372256881393)
              ·
                refine ⟨2327968840785279192661045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103958454380372256881393 2327968840785279192661045)
                ·
                  refine ⟨218247078823619924311973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2327968840785279192661045 218247078823619924311973)
                  ·
                    rfl

theorem cell20_478164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_478164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478164 prefixEnd_478164 := by exact prefixLift 478164
  have htrace : WordTrace (prefixWord ++ tailWord_478164) baseStart_478164 baseEnd_478164 := by
    simpa [prefixWord, tailWord_478164, baseEnd_478164] using wordTrace_append hprefix tailTrace_478164
  have hstable : (prefixWord ++ tailWord_478164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478164).length < 2 ^ (prefixWord ++ tailWord_478164).sum := by decide
  have hdescent : baseEnd_478164 < baseStart_478164 := by decide
  rcases family_descends (prefixWord ++ tailWord_478164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478194 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_478194 : Nat := 118140960795 + 478194 * 2 ^ 59
def prefixEnd_478194 : Nat := 4983230072969 + 3 ^ 40 * 478194 * 2
def baseEnd_478194 : Nat := 218260771641073153311851

theorem tailTrace_478194 : CollatzResearch.WordTrace tailWord_478194 prefixEnd_478194 218260771641073153311851 := by
  unfold tailWord_478194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360292007398070469576409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11627445353061521252203757 4360292007398070469576409)
  ·
    refine ⟨3270219005548552852182307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4360292007398070469576409 3270219005548552852182307)
    ·
      refine ⟨4905328508322829278273461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270219005548552852182307 4905328508322829278273461)
      ·
        refine ⟨459874547655265244838137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4905328508322829278273461 459874547655265244838137)
        ·
          refine ⟨344905910741448933628603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459874547655265244838137 344905910741448933628603)
          ·
            refine ⟨517358866112173400442905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344905910741448933628603 517358866112173400442905)
            ·
              refine ⟨388019149584130050332179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517358866112173400442905 388019149584130050332179)
              ·
                refine ⟨582028724376195075498269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388019149584130050332179 582028724376195075498269)
                ·
                  refine ⟨218260771641073153311851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582028724376195075498269 218260771641073153311851)
                  ·
                    rfl

theorem cell20_478194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_478194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478194 prefixEnd_478194 := by exact prefixLift 478194
  have htrace : WordTrace (prefixWord ++ tailWord_478194) baseStart_478194 baseEnd_478194 := by
    simpa [prefixWord, tailWord_478194, baseEnd_478194] using wordTrace_append hprefix tailTrace_478194
  have hstable : (prefixWord ++ tailWord_478194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478194).length < 2 ^ (prefixWord ++ tailWord_478194).sum := by decide
  have hdescent : baseEnd_478194 < baseStart_478194 := by decide
  rcases family_descends (prefixWord ++ tailWord_478194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478198 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_478198 : Nat := 118140960795 + 478198 * 2 ^ 59
def prefixEnd_478198 : Nat := 4983230072969 + 3 ^ 40 * 478198 * 2
def baseEnd_478198 : Nat := 218262597350066917178501

theorem tailTrace_478198 : CollatzResearch.WordTrace tailWord_478198 prefixEnd_478198 218262597350066917178501 := by
  unfold tailWord_478198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090082120098611910090703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11627542614385193707634165 1090082120098611910090703)
  ·
    refine ⟨1635123180147917865136055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1090082120098611910090703 1635123180147917865136055)
    ·
      refine ⟨2452684770221876797704083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635123180147917865136055 2452684770221876797704083)
      ·
        refine ⟨3679027155332815196556125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452684770221876797704083 3679027155332815196556125)
        ·
          refine ⟨1379635183249805698708547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3679027155332815196556125 1379635183249805698708547)
          ·
            refine ⟨2069452774874708548062821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379635183249805698708547 2069452774874708548062821)
            ·
              refine ⟨388022395289007852761779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2069452774874708548062821 388022395289007852761779)
              ·
                refine ⟨582033592933511779142669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388022395289007852761779 582033592933511779142669)
                ·
                  refine ⟨218262597350066917178501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582033592933511779142669 218262597350066917178501)
                  ·
                    rfl

theorem cell20_478198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_478198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478198 prefixEnd_478198 := by exact prefixLift 478198
  have htrace : WordTrace (prefixWord ++ tailWord_478198) baseStart_478198 baseEnd_478198 := by
    simpa [prefixWord, tailWord_478198, baseEnd_478198] using wordTrace_append hprefix tailTrace_478198
  have hstable : (prefixWord ++ tailWord_478198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478198).length < 2 ^ (prefixWord ++ tailWord_478198).sum := by decide
  have hdescent : baseEnd_478198 < baseStart_478198 := by decide
  rcases family_descends (prefixWord ++ tailWord_478198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478216 : List Nat := [2, 1, 3, 2, 1, 3, 2, 6]
def baseStart_478216 : Nat := 118140960795 + 478216 * 2 ^ 59
def prefixEnd_478216 : Nat := 4983230072969 + 3 ^ 40 * 478216 * 2
def baseEnd_478216 : Nat := 72756937680179618192809

theorem tailTrace_478216 : CollatzResearch.WordTrace tailWord_478216 prefixEnd_478216 72756937680179618192809 := by
  unfold tailWord_478216
  simp only [CollatzResearch.WordTrace]
  refine ⟨8720985217756289817803251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11627980290341719757071001 8720985217756289817803251)
  ·
    refine ⟨13081477826634434726704877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8720985217756289817803251 13081477826634434726704877)
    ·
      refine ⟨4905554184987913022514329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13081477826634434726704877 4905554184987913022514329)
      ·
        refine ⟨3679165638740934766885747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4905554184987913022514329 3679165638740934766885747)
        ·
          refine ⟨5518748458111402150328621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679165638740934766885747 5518748458111402150328621)
          ·
            refine ⟨2069530671791775806373233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5518748458111402150328621 2069530671791775806373233)
            ·
              refine ⟨1552148003843831854779925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069530671791775806373233 1552148003843831854779925)
              ·
                refine ⟨72756937680179618192809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1552148003843831854779925 72756937680179618192809)
                ·
                  rfl

theorem cell20_478216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_478216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478216 prefixEnd_478216 := by exact prefixLift 478216
  have htrace : WordTrace (prefixWord ++ tailWord_478216) baseStart_478216 baseEnd_478216 := by
    simpa [prefixWord, tailWord_478216, baseEnd_478216] using wordTrace_append hprefix tailTrace_478216
  have hstable : (prefixWord ++ tailWord_478216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478216).length < 2 ^ (prefixWord ++ tailWord_478216).sum := by decide
  have hdescent : baseEnd_478216 < baseStart_478216 := by decide
  rcases family_descends (prefixWord ++ tailWord_478216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478243 : List Nat := [1, 1, 1, 4, 3, 2, 4, 2, 2]
def baseStart_478243 : Nat := 118140960795 + 478243 * 2 ^ 59
def prefixEnd_478243 : Nat := 4983230072969 + 3 ^ 40 * 478243 * 2
def baseEnd_478243 : Nat := 218283136576246760678317

theorem tailTrace_478243 : CollatzResearch.WordTrace tailWord_478243 prefixEnd_478243 218283136576246760678317 := by
  unfold tailWord_478243
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442955206414763246839383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11628636804276508831226255 17442955206414763246839383)
  ·
    refine ⟨26164432809622144870259075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17442955206414763246839383 26164432809622144870259075)
    ·
      refine ⟨39246649214433217305388613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26164432809622144870259075 39246649214433217305388613)
      ·
        refine ⟨7358746727706228244760365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39246649214433217305388613 7358746727706228244760365)
        ·
          refine ⟨2759530022889835591785137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7358746727706228244760365 2759530022889835591785137)
          ·
            refine ⟨2069647517167376693838853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2759530022889835591785137 2069647517167376693838853)
            ·
              refine ⟨388058909468883130094785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2069647517167376693838853 388058909468883130094785)
              ·
                refine ⟨291044182101662347571089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388058909468883130094785 291044182101662347571089)
                ·
                  refine ⟨218283136576246760678317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291044182101662347571089 218283136576246760678317)
                  ·
                    rfl

theorem cell20_478243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 2].length) (baseStart_478243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478243 prefixEnd_478243 := by exact prefixLift 478243
  have htrace : WordTrace (prefixWord ++ tailWord_478243) baseStart_478243 baseEnd_478243 := by
    simpa [prefixWord, tailWord_478243, baseEnd_478243] using wordTrace_append hprefix tailTrace_478243
  have hstable : (prefixWord ++ tailWord_478243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478243).length < 2 ^ (prefixWord ++ tailWord_478243).sum := by decide
  have hdescent : baseEnd_478243 < baseStart_478243 := by decide
  rcases family_descends (prefixWord ++ tailWord_478243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478250 : List Nat := [3, 1, 4, 1, 3, 2, 1, 5]
def baseStart_478250 : Nat := 118140960795 + 478250 * 2 ^ 59
def prefixEnd_478250 : Nat := 4983230072969 + 3 ^ 40 * 478250 * 2
def baseEnd_478250 : Nat := 72762110522328615814985

theorem tailTrace_478250 : CollatzResearch.WordTrace tailWord_478250 prefixEnd_478250 72762110522328615814985 := by
  unfold tailWord_478250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360802629347350860586051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11628807011592935628229469 4360802629347350860586051)
  ·
    refine ⟨6541203944021026290879077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4360802629347350860586051 6541203944021026290879077)
    ·
      refine ⟨1226475739503942429539827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6541203944021026290879077 1226475739503942429539827)
      ·
        refine ⟨1839713609255913644309741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226475739503942429539827 1839713609255913644309741)
        ·
          refine ⟨689892603470967616616153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1839713609255913644309741 689892603470967616616153)
          ·
            refine ⟨517419452603225712462115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689892603470967616616153 517419452603225712462115)
            ·
              refine ⟨776129178904838568693173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517419452603225712462115 776129178904838568693173)
              ·
                refine ⟨72762110522328615814985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 776129178904838568693173 72762110522328615814985)
                ·
                  rfl

theorem cell20_478250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_478250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478250 prefixEnd_478250 := by exact prefixLift 478250
  have htrace : WordTrace (prefixWord ++ tailWord_478250) baseStart_478250 baseEnd_478250 := by
    simpa [prefixWord, tailWord_478250, baseEnd_478250] using wordTrace_append hprefix tailTrace_478250
  have hstable : (prefixWord ++ tailWord_478250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478250).length < 2 ^ (prefixWord ++ tailWord_478250).sum := by decide
  have hdescent : baseEnd_478250 < baseStart_478250 := by decide
  rcases family_descends (prefixWord ++ tailWord_478250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478261 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_478261 : Nat := 118140960795 + 478261 * 2 ^ 59
def prefixEnd_478261 : Nat := 4983230072969 + 3 ^ 40 * 478261 * 2
def baseEnd_478261 : Nat := 218291352266718698078243

theorem tailTrace_478261 : CollatzResearch.WordTrace tailWord_478261 prefixEnd_478261 218291352266718698078243 := by
  unfold tailWord_478261
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443611720349552320994637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11629074480233034880663091 17443611720349552320994637)
  ·
    refine ⟨6541354395131082120372989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17443611720349552320994637 6541354395131082120372989)
    ·
      refine ⟨2453007898174155795139871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6541354395131082120372989 2453007898174155795139871)
      ·
        refine ⟨3679511847261233692709807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453007898174155795139871 3679511847261233692709807)
        ·
          refine ⟨5519267770891850539064711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679511847261233692709807 5519267770891850539064711)
          ·
            refine ⟨8278901656337775808597067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5519267770891850539064711 8278901656337775808597067)
            ·
              refine ⟨12418352484506663712895601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278901656337775808597067 12418352484506663712895601)
              ·
                refine ⟨9313764363379997784671701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12418352484506663712895601 9313764363379997784671701)
                ·
                  refine ⟨218291352266718698078243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9313764363379997784671701 218291352266718698078243)
                  ·
                    rfl

theorem cell20_478261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_478261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478261 prefixEnd_478261 := by exact prefixLift 478261
  have htrace : WordTrace (prefixWord ++ tailWord_478261) baseStart_478261 baseEnd_478261 := by
    simpa [prefixWord, tailWord_478261, baseEnd_478261] using wordTrace_append hprefix tailTrace_478261
  have hstable : (prefixWord ++ tailWord_478261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478261).length < 2 ^ (prefixWord ++ tailWord_478261).sum := by decide
  have hdescent : baseEnd_478261 < baseStart_478261 := by decide
  rcases family_descends (prefixWord ++ tailWord_478261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478354 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_478354 : Nat := 118140960795 + 478354 * 2 ^ 59
def prefixEnd_478354 : Nat := 4983230072969 + 3 ^ 40 * 478354 * 2
def baseEnd_478354 : Nat := 218333800000823707977863

theorem tailTrace_478354 : CollatzResearch.WordTrace tailWord_478354 prefixEnd_478354 218333800000823707977863 := by
  unfold tailWord_478354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361750927253157301032529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11631335806008419469420077 4361750927253157301032529)
  ·
    refine ⟨3271313195439867975774397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4361750927253157301032529 3271313195439867975774397)
    ·
      refine ⟨1226742448289950490915399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3271313195439867975774397 1226742448289950490915399)
      ·
        refine ⟨1840113672434925736373099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226742448289950490915399 1840113672434925736373099)
        ·
          refine ⟨2760170508652388604559649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840113672434925736373099 2760170508652388604559649)
          ·
            refine ⟨2070127881489291453419737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2760170508652388604559649 2070127881489291453419737)
            ·
              refine ⟨1552595911116968590064803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070127881489291453419737 1552595911116968590064803)
              ·
                refine ⟨2328893866675452885097205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552595911116968590064803 2328893866675452885097205)
                ·
                  refine ⟨218333800000823707977863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2328893866675452885097205 218333800000823707977863)
                  ·
                    rfl

theorem cell20_478354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_478354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478354 prefixEnd_478354 := by exact prefixLift 478354
  have htrace : WordTrace (prefixWord ++ tailWord_478354) baseStart_478354 baseEnd_478354 := by
    simpa [prefixWord, tailWord_478354, baseEnd_478354] using wordTrace_append hprefix tailTrace_478354
  have hstable : (prefixWord ++ tailWord_478354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478354).length < 2 ^ (prefixWord ++ tailWord_478354).sum := by decide
  have hdescent : baseEnd_478354 < baseStart_478354 := by decide
  rcases family_descends (prefixWord ++ tailWord_478354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478367 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 3]
def baseStart_478367 : Nat := 118140960795 + 478367 * 2 ^ 59
def prefixEnd_478367 : Nat := 4983230072969 + 3 ^ 40 * 478367 * 2
def baseEnd_478367 : Nat := 218339733555053440544477

theorem tailTrace_478367 : CollatzResearch.WordTrace tailWord_478367 prefixEnd_478367 218339733555053440544477 := by
  unfold tailWord_478367
  simp only [CollatzResearch.WordTrace]
  refine ⟨17447477857965532424353355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11631651905310354949568903 17447477857965532424353355)
  ·
    refine ⟨26171216786948298636530033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17447477857965532424353355 26171216786948298636530033)
    ·
      refine ⟨19628412590211223977397525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26171216786948298636530033 19628412590211223977397525)
      ·
        refine ⟨920081840166151123940509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19628412590211223977397525 920081840166151123940509)
        ·
          refine ⟨345030690062306671477691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920081840166151123940509 345030690062306671477691)
          ·
            refine ⟨517546035093460007216537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345030690062306671477691 517546035093460007216537)
            ·
              refine ⟨388159526320095005412403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517546035093460007216537 388159526320095005412403)
              ·
                refine ⟨582239289480142508118605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388159526320095005412403 582239289480142508118605)
                ·
                  refine ⟨218339733555053440544477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582239289480142508118605 218339733555053440544477)
                  ·
                    rfl

theorem cell20_478367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 3].length) (baseStart_478367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478367 prefixEnd_478367 := by exact prefixLift 478367
  have htrace : WordTrace (prefixWord ++ tailWord_478367) baseStart_478367 baseEnd_478367 := by
    simpa [prefixWord, tailWord_478367, baseEnd_478367] using wordTrace_append hprefix tailTrace_478367
  have hstable : (prefixWord ++ tailWord_478367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478367).length < 2 ^ (prefixWord ++ tailWord_478367).sum := by decide
  have hdescent : baseEnd_478367 < baseStart_478367 := by decide
  rcases family_descends (prefixWord ++ tailWord_478367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478368 : List Nat := [2, 1, 1, 4, 2, 1, 4, 5]
def baseStart_478368 : Nat := 118140960795 + 478368 * 2 ^ 59
def prefixEnd_478368 : Nat := 4983230072969 + 3 ^ 40 * 478368 * 2
def baseEnd_478368 : Nat := 72780063327433960503713

theorem tailTrace_478368 : CollatzResearch.WordTrace tailWord_478368 prefixEnd_478368 72780063327433960503713 := by
  unfold tailWord_478368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723757165480954797569879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11631676220641273063426505 8723757165480954797569879)
  ·
    refine ⟨13085635748221432196354819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8723757165480954797569879 13085635748221432196354819)
    ·
      refine ⟨19628453622332148294532229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13085635748221432196354819 19628453622332148294532229)
      ·
        refine ⟨3680335054187277805224793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19628453622332148294532229 3680335054187277805224793)
        ·
          refine ⟨2760251290640458353918595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3680335054187277805224793 2760251290640458353918595)
          ·
            refine ⟨4140376935960687530877893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760251290640458353918595 4140376935960687530877893)
            ·
              refine ⟨776320675492628912039605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4140376935960687530877893 776320675492628912039605)
              ·
                refine ⟨72780063327433960503713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 776320675492628912039605 72780063327433960503713)
                ·
                  rfl

theorem cell20_478368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_478368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478368 prefixEnd_478368 := by exact prefixLift 478368
  have htrace : WordTrace (prefixWord ++ tailWord_478368) baseStart_478368 baseEnd_478368 := by
    simpa [prefixWord, tailWord_478368, baseEnd_478368] using wordTrace_append hprefix tailTrace_478368
  have hstable : (prefixWord ++ tailWord_478368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478368).length < 2 ^ (prefixWord ++ tailWord_478368).sum := by decide
  have hdescent : baseEnd_478368 < baseStart_478368 := by decide
  rcases family_descends (prefixWord ++ tailWord_478368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478402 : List Nat := [3, 5, 1, 1, 2, 8]
def baseStart_478402 : Nat := 118140960795 + 478402 * 2 ^ 59
def prefixEnd_478402 : Nat := 4983230072969 + 3 ^ 40 * 478402 * 2
def baseEnd_478402 : Nat := 8087248463286995347321

theorem tailTrace_478402 : CollatzResearch.WordTrace tailWord_478402 prefixEnd_478402 8087248463286995347321 := by
  unfold tailWord_478402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362188603209683350469365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11632502941892488934584973 4362188603209683350469365)
  ·
    refine ⟨408955181550907814106503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4362188603209683350469365 408955181550907814106503)
    ·
      refine ⟨613432772326361721159755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408955181550907814106503 613432772326361721159755)
      ·
        refine ⟨920149158489542581739633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613432772326361721159755 920149158489542581739633)
        ·
          refine ⟨690111868867156936304725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920149158489542581739633 690111868867156936304725)
          ·
            refine ⟨8087248463286995347321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 690111868867156936304725 8087248463286995347321)
            ·
              rfl

theorem cell20_478402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 8].length) (baseStart_478402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478402 prefixEnd_478402 := by exact prefixLift 478402
  have htrace : WordTrace (prefixWord ++ tailWord_478402) baseStart_478402 baseEnd_478402 := by
    simpa [prefixWord, tailWord_478402, baseEnd_478402] using wordTrace_append hprefix tailTrace_478402
  have hstable : (prefixWord ++ tailWord_478402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478402).length < 2 ^ (prefixWord ++ tailWord_478402).sum := by decide
  have hdescent : baseEnd_478402 < baseStart_478402 := by decide
  rcases family_descends (prefixWord ++ tailWord_478402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478458 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_478458 : Nat := 118140960795 + 478458 * 2 ^ 59
def prefixEnd_478458 : Nat := 4983230072969 + 3 ^ 40 * 478458 * 2
def baseEnd_478458 : Nat := 218381268434661568510771

theorem tailTrace_478458 : CollatzResearch.WordTrace tailWord_478458 prefixEnd_478458 218381268434661568510771 := by
  unfold tailWord_478458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362699225158963741479007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11633864600423903310610685 4362699225158963741479007)
  ·
    refine ⟨6544048837738445612218511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4362699225158963741479007 6544048837738445612218511)
    ·
      refine ⟨9816073256607668418327767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6544048837738445612218511 9816073256607668418327767)
      ·
        refine ⟨14724109884911502627491651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9816073256607668418327767 14724109884911502627491651)
        ·
          refine ⟨22086164827367253941237477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14724109884911502627491651 22086164827367253941237477)
          ·
            refine ⟨4141155905131360113982027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22086164827367253941237477 4141155905131360113982027)
            ·
              refine ⟨6211733857697040170973041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141155905131360113982027 6211733857697040170973041)
              ·
                refine ⟨4658800393272780128229781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6211733857697040170973041 4658800393272780128229781)
                ·
                  refine ⟨218381268434661568510771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4658800393272780128229781 218381268434661568510771)
                  ·
                    rfl

theorem cell20_478458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_478458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478458 prefixEnd_478458 := by exact prefixLift 478458
  have htrace : WordTrace (prefixWord ++ tailWord_478458) baseStart_478458 baseEnd_478458 := by
    simpa [prefixWord, tailWord_478458, baseEnd_478458] using wordTrace_append hprefix tailTrace_478458
  have hstable : (prefixWord ++ tailWord_478458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478458).length < 2 ^ (prefixWord ++ tailWord_478458).sum := by decide
  have hdescent : baseEnd_478458 < baseStart_478458 := by decide
  rcases family_descends (prefixWord ++ tailWord_478458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478468 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_478468 : Nat := 118140960795 + 478468 * 2 ^ 59
def prefixEnd_478468 : Nat := 4983230072969 + 3 ^ 40 * 478468 * 2
def baseEnd_478468 : Nat := 218385832707145978177397

theorem tailTrace_478468 : CollatzResearch.WordTrace tailWord_478468 prefixEnd_478468 218385832707145978177397 := by
  unfold tailWord_478468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8725580815299813336890029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11634107753733084449186705 8725580815299813336890029)
  ·
    refine ⟨3272092805737430001333761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8725580815299813336890029 3272092805737430001333761)
    ·
      refine ⟨2454069604303072501000321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3272092805737430001333761 2454069604303072501000321)
      ·
        refine ⟨1840552203227304375750241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2454069604303072501000321 1840552203227304375750241)
        ·
          refine ⟨1380414152420478281812681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840552203227304375750241 1380414152420478281812681)
          ·
            refine ⟨1035310614315358711359511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380414152420478281812681 1035310614315358711359511)
            ·
              refine ⟨1552965921473038067039267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035310614315358711359511 1552965921473038067039267)
              ·
                refine ⟨2329448882209557100558901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552965921473038067039267 2329448882209557100558901)
                ·
                  refine ⟨218385832707145978177397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2329448882209557100558901 218385832707145978177397)
                  ·
                    rfl

theorem cell20_478468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_478468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478468 prefixEnd_478468 := by exact prefixLift 478468
  have htrace : WordTrace (prefixWord ++ tailWord_478468) baseStart_478468 baseEnd_478468 := by
    simpa [prefixWord, tailWord_478468, baseEnd_478468] using wordTrace_append hprefix tailTrace_478468
  have hstable : (prefixWord ++ tailWord_478468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478468).length < 2 ^ (prefixWord ++ tailWord_478468).sum := by decide
  have hdescent : baseEnd_478468 < baseStart_478468 := by decide
  rcases family_descends (prefixWord ++ tailWord_478468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478475 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_478475 : Nat := 118140960795 + 478475 * 2 ^ 59
def prefixEnd_478475 : Nat := 4983230072969 + 3 ^ 40 * 478475 * 2
def baseEnd_478475 : Nat := 218389027697885064944035

theorem tailTrace_478475 : CollatzResearch.WordTrace tailWord_478475 prefixEnd_478475 218389027697885064944035 := by
  unfold tailWord_478475
  simp only [CollatzResearch.WordTrace]
  refine ⟨17451416941574266869284879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11634277961049511246189919 17451416941574266869284879)
  ·
    refine ⟨26177125412361400303927319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17451416941574266869284879 26177125412361400303927319)
    ·
      refine ⟨39265688118542100455890979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26177125412361400303927319 39265688118542100455890979)
      ·
        refine ⟨58898532177813150683836469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39265688118542100455890979 58898532177813150683836469)
        ·
          refine ⟨5521737391669982876609669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58898532177813150683836469 5521737391669982876609669)
          ·
            refine ⟨1035325760938121789364313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5521737391669982876609669 1035325760938121789364313)
            ·
              refine ⟨776494320703591342023235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035325760938121789364313 776494320703591342023235)
              ·
                refine ⟨1164741481055387013034853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776494320703591342023235 1164741481055387013034853)
                ·
                  refine ⟨218389027697885064944035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1164741481055387013034853 218389027697885064944035)
                  ·
                    rfl

theorem cell20_478475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_478475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478475 prefixEnd_478475 := by exact prefixLift 478475
  have htrace : WordTrace (prefixWord ++ tailWord_478475) baseStart_478475 baseEnd_478475 := by
    simpa [prefixWord, tailWord_478475, baseEnd_478475] using wordTrace_append hprefix tailTrace_478475
  have hstable : (prefixWord ++ tailWord_478475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478475).length < 2 ^ (prefixWord ++ tailWord_478475).sum := by decide
  have hdescent : baseEnd_478475 < baseStart_478475 := by decide
  rcases family_descends (prefixWord ++ tailWord_478475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478499 : List Nat := [1, 1, 1, 4, 2, 5, 2, 4]
def baseStart_478499 : Nat := 118140960795 + 478499 * 2 ^ 59
def prefixEnd_478499 : Nat := 4983230072969 + 3 ^ 40 * 478499 * 2
def baseEnd_478499 : Nat := 72799993983949216047979

theorem tailTrace_478499 : CollatzResearch.WordTrace tailWord_478499 prefixEnd_478499 72799993983949216047979 := by
  unfold tailWord_478499
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452292293487318968158551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11634861528991545978772367 17452292293487318968158551)
  ·
    refine ⟨26178438440230978452237827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17452292293487318968158551 26178438440230978452237827)
    ·
      refine ⟨39267657660346467678356741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26178438440230978452237827 39267657660346467678356741)
      ·
        refine ⟨7362685811314962689691889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39267657660346467678356741 7362685811314962689691889)
        ·
          refine ⟨5522014358486222017268917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7362685811314962689691889 5522014358486222017268917)
          ·
            refine ⟨517688846108083314118961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5522014358486222017268917 517688846108083314118961)
            ·
              refine ⟨388266634581062485589221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517688846108083314118961 388266634581062485589221)
              ·
                refine ⟨72799993983949216047979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388266634581062485589221 72799993983949216047979)
                ·
                  rfl

theorem cell20_478499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 4].length) (baseStart_478499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478499 prefixEnd_478499 := by exact prefixLift 478499
  have htrace : WordTrace (prefixWord ++ tailWord_478499) baseStart_478499 baseEnd_478499 := by
    simpa [prefixWord, tailWord_478499, baseEnd_478499] using wordTrace_append hprefix tailTrace_478499
  have hstable : (prefixWord ++ tailWord_478499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478499).length < 2 ^ (prefixWord ++ tailWord_478499).sum := by decide
  have hdescent : baseEnd_478499 < baseStart_478499 := by decide
  rcases family_descends (prefixWord ++ tailWord_478499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478506 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_478506 : Nat := 118140960795 + 478506 * 2 ^ 59
def prefixEnd_478506 : Nat := 4983230072969 + 3 ^ 40 * 478506 * 2
def baseEnd_478506 : Nat := 218403176942586734910575

theorem tailTrace_478506 : CollatzResearch.WordTrace tailWord_478506 prefixEnd_478506 218403176942586734910575 := by
  unfold tailWord_478506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4363136901115489790915843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11635031736307972775775581 4363136901115489790915843)
  ·
    refine ⟨6544705351673234686373765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4363136901115489790915843 6544705351673234686373765)
    ·
      refine ⟨1227132253438731503695081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6544705351673234686373765 1227132253438731503695081)
      ·
        refine ⟨920349190079048627771311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1227132253438731503695081 920349190079048627771311)
        ·
          refine ⟨1380523785118572941656967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920349190079048627771311 1380523785118572941656967)
          ·
            refine ⟨2070785677677859412485451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380523785118572941656967 2070785677677859412485451)
            ·
              refine ⟨3106178516516789118728177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070785677677859412485451 3106178516516789118728177)
              ·
                refine ⟨2329633887387591839046133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106178516516789118728177 2329633887387591839046133)
                ·
                  refine ⟨218403176942586734910575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2329633887387591839046133 218403176942586734910575)
                  ·
                    rfl

theorem cell20_478506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_478506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478506 prefixEnd_478506 := by exact prefixLift 478506
  have htrace : WordTrace (prefixWord ++ tailWord_478506) baseStart_478506 baseEnd_478506 := by
    simpa [prefixWord, tailWord_478506, baseEnd_478506] using wordTrace_append hprefix tailTrace_478506
  have hstable : (prefixWord ++ tailWord_478506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478506).length < 2 ^ (prefixWord ++ tailWord_478506).sum := by decide
  have hdescent : baseEnd_478506 < baseStart_478506 := by decide
  rcases family_descends (prefixWord ++ tailWord_478506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478527 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_478527 : Nat := 118140960795 + 478527 * 2 ^ 59
def prefixEnd_478527 : Nat := 4983230072969 + 3 ^ 40 * 478527 * 2
def baseEnd_478527 : Nat := 218412761914803995210489

theorem tailTrace_478527 : CollatzResearch.WordTrace tailWord_478527 prefixEnd_478527 218412761914803995210489 := by
  unfold tailWord_478527
  simp only [CollatzResearch.WordTrace]
  refine ⟨17453313537385879750177835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11635542358257253166785223 17453313537385879750177835)
  ·
    refine ⟨26179970306078819625266753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17453313537385879750177835 26179970306078819625266753)
    ·
      refine ⟨19634977729559114718950065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26179970306078819625266753 19634977729559114718950065)
      ·
        refine ⟨14726233297169336039212549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19634977729559114718950065 14726233297169336039212549)
        ·
          refine ⟨2761168743219250507352353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14726233297169336039212549 2761168743219250507352353)
          ·
            refine ⟨2070876557414437880514265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761168743219250507352353 2070876557414437880514265)
            ·
              refine ⟨1553157418060828410385699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070876557414437880514265 1553157418060828410385699)
              ·
                refine ⟨2329736127091242615578549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553157418060828410385699 2329736127091242615578549)
                ·
                  refine ⟨218412761914803995210489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2329736127091242615578549 218412761914803995210489)
                  ·
                    rfl

theorem cell20_478527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_478527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478527 prefixEnd_478527 := by exact prefixLift 478527
  have htrace : WordTrace (prefixWord ++ tailWord_478527) baseStart_478527 baseEnd_478527 := by
    simpa [prefixWord, tailWord_478527, baseEnd_478527] using wordTrace_append hprefix tailTrace_478527
  have hstable : (prefixWord ++ tailWord_478527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478527).length < 2 ^ (prefixWord ++ tailWord_478527).sum := by decide
  have hdescent : baseEnd_478527 < baseStart_478527 := by decide
  rcases family_descends (prefixWord ++ tailWord_478527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478581 : List Nat := [1, 3, 4, 1, 4, 1, 2, 2, 2]
def baseStart_478581 : Nat := 118140960795 + 478581 * 2 ^ 59
def prefixEnd_478581 : Nat := 4983230072969 + 3 ^ 40 * 478581 * 2
def baseEnd_478581 : Nat := 218437408986219807410269

theorem tailTrace_478581 : CollatzResearch.WordTrace tailWord_478581 prefixEnd_478581 218437408986219807410269 := by
  unfold tailWord_478581
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455283079190246972643597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11636855386126831315095731 17455283079190246972643597)
  ·
    refine ⟨6545731154696342614741349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17455283079190246972643597 6545731154696342614741349)
    ·
      refine ⟨1227324591505564240264003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6545731154696342614741349 1227324591505564240264003)
      ·
        refine ⟨1840986887258346360396005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227324591505564240264003 1840986887258346360396005)
        ·
          refine ⟨345185041360939942574251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1840986887258346360396005 345185041360939942574251)
          ·
            refine ⟨517777562041409913861377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345185041360939942574251 517777562041409913861377)
            ·
              refine ⟨388333171531057435396033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517777562041409913861377 388333171531057435396033)
              ·
                refine ⟨291249878648293076547025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388333171531057435396033 291249878648293076547025)
                ·
                  refine ⟨218437408986219807410269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291249878648293076547025 218437408986219807410269)
                  ·
                    rfl

theorem cell20_478581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_478581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478581 prefixEnd_478581 := by exact prefixLift 478581
  have htrace : WordTrace (prefixWord ++ tailWord_478581) baseStart_478581 baseEnd_478581 := by
    simpa [prefixWord, tailWord_478581, baseEnd_478581] using wordTrace_append hprefix tailTrace_478581
  have hstable : (prefixWord ++ tailWord_478581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478581).length < 2 ^ (prefixWord ++ tailWord_478581).sum := by decide
  have hdescent : baseEnd_478581 < baseStart_478581 := by decide
  rcases family_descends (prefixWord ++ tailWord_478581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478596 : List Nat := [2, 3, 2, 1, 1, 3, 3, 5]
def baseStart_478596 : Nat := 118140960795 + 478596 * 2 ^ 59
def prefixEnd_478596 : Nat := 4983230072969 + 3 ^ 40 * 478596 * 2
def baseEnd_478596 : Nat := 72814751798315473970069

theorem tailTrace_478596 : CollatzResearch.WordTrace tailWord_478596 prefixEnd_478596 72814751798315473970069 := by
  unfold tailWord_478596
  simp only [CollatzResearch.WordTrace]
  refine ⟨8727915087067952267219821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11637220116090603022959761 8727915087067952267219821)
  ·
    refine ⟨3272968157650482100207433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8727915087067952267219821 3272968157650482100207433)
    ·
      refine ⟨2454726118237861575155575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3272968157650482100207433 2454726118237861575155575)
      ·
        refine ⟨3682089177356792362733363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454726118237861575155575 3682089177356792362733363)
        ·
          refine ⟨5523133766035188544100045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682089177356792362733363 5523133766035188544100045)
          ·
            refine ⟨2071175162263195704037517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5523133766035188544100045 2071175162263195704037517)
            ·
              refine ⟨776690685848698389014069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071175162263195704037517 776690685848698389014069)
              ·
                refine ⟨72814751798315473970069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 776690685848698389014069 72814751798315473970069)
                ·
                  rfl

theorem cell20_478596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_478596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478596 prefixEnd_478596 := by exact prefixLift 478596
  have htrace : WordTrace (prefixWord ++ tailWord_478596) baseStart_478596 baseEnd_478596 := by
    simpa [prefixWord, tailWord_478596, baseEnd_478596] using wordTrace_append hprefix tailTrace_478596
  have hstable : (prefixWord ++ tailWord_478596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478596).length < 2 ^ (prefixWord ++ tailWord_478596).sum := by decide
  have hdescent : baseEnd_478596 < baseStart_478596 := by decide
  rcases family_descends (prefixWord ++ tailWord_478596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478603 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 3]
def baseStart_478603 : Nat := 118140960795 + 478603 * 2 ^ 59
def prefixEnd_478603 : Nat := 4983230072969 + 3 ^ 40 * 478603 * 2
def baseEnd_478603 : Nat := 218447450385685508676845

theorem tailTrace_478603 : CollatzResearch.WordTrace tailWord_478603 prefixEnd_478603 218447450385685508676845 := by
  unfold tailWord_478603
  simp only [CollatzResearch.WordTrace]
  refine ⟨17456085485110544729944463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11637390323407029819962975 17456085485110544729944463)
  ·
    refine ⟨26184128227665817094916695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17456085485110544729944463 26184128227665817094916695)
    ·
      refine ⟨39276192341498725642375043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26184128227665817094916695 39276192341498725642375043)
      ·
        refine ⟨58914288512248088463562565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39276192341498725642375043 58914288512248088463562565)
        ·
          refine ⟨11046429096046516586917981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58914288512248088463562565 11046429096046516586917981)
          ·
            refine ⟨4142410911017443720094243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11046429096046516586917981 4142410911017443720094243)
            ·
              refine ⟨6213616366526165580141365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142410911017443720094243 6213616366526165580141365)
              ·
                refine ⟨582526534361828023138253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6213616366526165580141365 582526534361828023138253)
                ·
                  refine ⟨218447450385685508676845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582526534361828023138253 218447450385685508676845)
                  ·
                    rfl

theorem cell20_478603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_478603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478603 prefixEnd_478603 := by exact prefixLift 478603
  have htrace : WordTrace (prefixWord ++ tailWord_478603) baseStart_478603 baseEnd_478603 := by
    simpa [prefixWord, tailWord_478603, baseEnd_478603] using wordTrace_append hprefix tailTrace_478603
  have hstable : (prefixWord ++ tailWord_478603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478603).length < 2 ^ (prefixWord ++ tailWord_478603).sum := by decide
  have hdescent : baseEnd_478603 < baseStart_478603 := by decide
  rcases family_descends (prefixWord ++ tailWord_478603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478606 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_478606 : Nat := 118140960795 + 478606 * 2 ^ 59
def prefixEnd_478606 : Nat := 4983230072969 + 3 ^ 40 * 478606 * 2
def baseEnd_478606 : Nat := 218448819667430831576833

theorem tailTrace_478606 : CollatzResearch.WordTrace tailWord_478606 prefixEnd_478606 218448819667430831576833 := by
  unfold tailWord_478606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182024363012459530287959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11637463269399784161535781 2182024363012459530287959)
  ·
    refine ⟨3273036544518689295431939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2182024363012459530287959 3273036544518689295431939)
    ·
      refine ⟨4909554816778033943147909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3273036544518689295431939 4909554816778033943147909)
      ·
        refine ⟨920541528145881364340233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4909554816778033943147909 920541528145881364340233)
        ·
          refine ⟨690406146109411023255175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920541528145881364340233 690406146109411023255175)
          ·
            refine ⟨1035609219164116534882763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690406146109411023255175 1035609219164116534882763)
            ·
              refine ⟨1553413828746174802324145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035609219164116534882763 1553413828746174802324145)
              ·
                refine ⟨1165060371559631101743109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553413828746174802324145 1165060371559631101743109)
                ·
                  refine ⟨218448819667430831576833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165060371559631101743109 218448819667430831576833)
                  ·
                    rfl

theorem cell20_478606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_478606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478606 prefixEnd_478606 := by exact prefixLift 478606
  have htrace : WordTrace (prefixWord ++ tailWord_478606) baseStart_478606 baseEnd_478606 := by
    simpa [prefixWord, tailWord_478606, baseEnd_478606] using wordTrace_append hprefix tailTrace_478606
  have hstable : (prefixWord ++ tailWord_478606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478606).length < 2 ^ (prefixWord ++ tailWord_478606).sum := by decide
  have hdescent : baseEnd_478606 < baseStart_478606 := by decide
  rcases family_descends (prefixWord ++ tailWord_478606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478637 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 3]
def baseStart_478637 : Nat := 118140960795 + 478637 * 2 ^ 59
def prefixEnd_478637 : Nat := 4983230072969 + 3 ^ 40 * 478637 * 2
def baseEnd_478637 : Nat := 218462968912132501543373

theorem tailTrace_478637 : CollatzResearch.WordTrace tailWord_478637 prefixEnd_478637 218462968912132501543373 := by
  unfold tailWord_478637
  simp only [CollatzResearch.WordTrace]
  refine ⟨17457325566987368536682165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11638217044658245691121443 17457325566987368536682165)
  ·
    refine ⟨1636624271905065800313953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17457325566987368536682165 1636624271905065800313953)
    ·
      refine ⟨1227468203928799350235465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1636624271905065800313953 1227468203928799350235465)
      ·
        refine ⟨920601152946599512676599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1227468203928799350235465 920601152946599512676599)
        ·
          refine ⟨1380901729419899269014899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920601152946599512676599 1380901729419899269014899)
          ·
            refine ⟨2071352594129848903522349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380901729419899269014899 2071352594129848903522349)
            ·
              refine ⟨776757222798693338820881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071352594129848903522349 776757222798693338820881)
              ·
                refine ⟨582567917099020004115661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776757222798693338820881 582567917099020004115661)
                ·
                  refine ⟨218462968912132501543373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582567917099020004115661 218462968912132501543373)
                  ·
                    rfl

theorem cell20_478637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_478637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478637 prefixEnd_478637 := by exact prefixLift 478637
  have htrace : WordTrace (prefixWord ++ tailWord_478637) baseStart_478637 baseEnd_478637 := by
    simpa [prefixWord, tailWord_478637, baseEnd_478637] using wordTrace_append hprefix tailTrace_478637
  have hstable : (prefixWord ++ tailWord_478637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478637).length < 2 ^ (prefixWord ++ tailWord_478637).sum := by decide
  have hdescent : baseEnd_478637 < baseStart_478637 := by decide
  rcases family_descends (prefixWord ++ tailWord_478637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478641 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_478641 : Nat := 118140960795 + 478641 * 2 ^ 59
def prefixEnd_478641 : Nat := 4983230072969 + 3 ^ 40 * 478641 * 2
def baseEnd_478641 : Nat := 218464794621126265410023

theorem tailTrace_478641 : CollatzResearch.WordTrace tailWord_478641 prefixEnd_478641 218464794621126265410023 := by
  unfold tailWord_478641
  simp only [CollatzResearch.WordTrace]
  refine ⟨17457471458972877219827777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11638314305981918146551851 17457471458972877219827777)
  ·
    refine ⟨13093103594229657914870833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17457471458972877219827777 13093103594229657914870833)
    ·
      refine ⟨9819827695672243436153125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13093103594229657914870833 9819827695672243436153125)
      ·
        refine ⟨1841217692938545644278711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9819827695672243436153125 1841217692938545644278711)
        ·
          refine ⟨2761826539407818466418067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841217692938545644278711 2761826539407818466418067)
          ·
            refine ⟨4142739809111727699627101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761826539407818466418067 4142739809111727699627101)
            ·
              refine ⟨1553527428416897887360163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4142739809111727699627101 1553527428416897887360163)
              ·
                refine ⟨2330291142625346831040245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553527428416897887360163 2330291142625346831040245)
                ·
                  refine ⟨218464794621126265410023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2330291142625346831040245 218464794621126265410023)
                  ·
                    rfl

theorem cell20_478641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_478641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478641 prefixEnd_478641 := by exact prefixLift 478641
  have htrace : WordTrace (prefixWord ++ tailWord_478641) baseStart_478641 baseEnd_478641 := by
    simpa [prefixWord, tailWord_478641, baseEnd_478641] using wordTrace_append hprefix tailTrace_478641
  have hstable : (prefixWord ++ tailWord_478641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478641).length < 2 ^ (prefixWord ++ tailWord_478641).sum := by decide
  have hdescent : baseEnd_478641 < baseStart_478641 := by decide
  rcases family_descends (prefixWord ++ tailWord_478641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478648 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_478648 : Nat := 118140960795 + 478648 * 2 ^ 59
def prefixEnd_478648 : Nat := 4983230072969 + 3 ^ 40 * 478648 * 2
def baseEnd_478648 : Nat := 218467989611865352176661

theorem tailTrace_478648 : CollatzResearch.WordTrace tailWord_478648 prefixEnd_478648 218467989611865352176661 := by
  unfold tailWord_478648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8728863384973758707666299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11638484513298344943555065 8728863384973758707666299)
  ·
    refine ⟨13093295077460638061499449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8728863384973758707666299 13093295077460638061499449)
    ·
      refine ⟨9819971308095478546124587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13093295077460638061499449 9819971308095478546124587)
      ·
        refine ⟨14729956962143217819186881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9819971308095478546124587 14729956962143217819186881)
        ·
          refine ⟨11047467721607413364390161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14729956962143217819186881 11047467721607413364390161)
          ·
            refine ⟨8285600791205560023292621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11047467721607413364390161 8285600791205560023292621)
            ·
              refine ⟨3107100296702085008734733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8285600791205560023292621 3107100296702085008734733)
              ·
                refine ⟨1165162611263281878275525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3107100296702085008734733 1165162611263281878275525)
                ·
                  refine ⟨218467989611865352176661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165162611263281878275525 218467989611865352176661)
                  ·
                    rfl

theorem cell20_478648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_478648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478648 prefixEnd_478648 := by exact prefixLift 478648
  have htrace : WordTrace (prefixWord ++ tailWord_478648) baseStart_478648 baseEnd_478648 := by
    simpa [prefixWord, tailWord_478648, baseEnd_478648] using wordTrace_append hprefix tailTrace_478648
  have hstable : (prefixWord ++ tailWord_478648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478648).length < 2 ^ (prefixWord ++ tailWord_478648).sum := by decide
  have hdescent : baseEnd_478648 < baseStart_478648 := by decide
  rcases family_descends (prefixWord ++ tailWord_478648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478678 : List Nat := [5, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_478678 : Nat := 118140960795 + 478678 * 2 ^ 59
def prefixEnd_478678 : Nat := 4983230072969 + 3 ^ 40 * 478678 * 2
def baseEnd_478678 : Nat := 218481682429318581176539

theorem tailTrace_478678 : CollatzResearch.WordTrace tailWord_478678 prefixEnd_478678 218481682429318581176539 := by
  unfold tailWord_478678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091176309989927033682793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11639213973225888359283125 1091176309989927033682793)
  ·
    refine ⟨818382232492445275262095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1091176309989927033682793 818382232492445275262095)
    ·
      refine ⟨1227573348738667912893143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818382232492445275262095 1227573348738667912893143)
      ·
        refine ⟨1841360023108001869339715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227573348738667912893143 1841360023108001869339715)
        ·
          refine ⟨2762040034662002804009573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841360023108001869339715 2762040034662002804009573)
          ·
            refine ⟨517882506499125525751795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2762040034662002804009573 517882506499125525751795)
            ·
              refine ⟨776823759748688288627693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517882506499125525751795 776823759748688288627693)
              ·
                refine ⟨291308909905758108235385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 776823759748688288627693 291308909905758108235385)
                ·
                  refine ⟨218481682429318581176539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291308909905758108235385 218481682429318581176539)
                  ·
                    rfl

theorem cell20_478678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_478678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478678 prefixEnd_478678 := by exact prefixLift 478678
  have htrace : WordTrace (prefixWord ++ tailWord_478678) baseStart_478678 baseEnd_478678 := by
    simpa [prefixWord, tailWord_478678, baseEnd_478678] using wordTrace_append hprefix tailTrace_478678
  have hstable : (prefixWord ++ tailWord_478678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478678).length < 2 ^ (prefixWord ++ tailWord_478678).sum := by decide
  have hdescent : baseEnd_478678 < baseStart_478678 := by decide
  rcases family_descends (prefixWord ++ tailWord_478678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478682 : List Nat := [3, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_478682 : Nat := 118140960795 + 478682 * 2 ^ 59
def prefixEnd_478682 : Nat := 4983230072969 + 3 ^ 40 * 478682 * 2
def baseEnd_478682 : Nat := 218483508138312345043189

theorem tailTrace_478682 : CollatzResearch.WordTrace tailWord_478682 prefixEnd_478682 218483508138312345043189 := by
  unfold tailWord_478682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364741712956085305517575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11639311234549560814713533 4364741712956085305517575)
  ·
    refine ⟨6547112569434127958276363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4364741712956085305517575 6547112569434127958276363)
    ·
      refine ⟨9820668854151191937414545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6547112569434127958276363 9820668854151191937414545)
      ·
        refine ⟨7365501640613393953060909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9820668854151191937414545 7365501640613393953060909)
        ·
          refine ⟨2762063115230022732397841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7365501640613393953060909 2762063115230022732397841)
          ·
            refine ⟨2071547336422517049298381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762063115230022732397841 2071547336422517049298381)
            ·
              refine ⟨776830251158443893486893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071547336422517049298381 776830251158443893486893)
              ·
                refine ⟨291311344184416460057585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 776830251158443893486893 291311344184416460057585)
                ·
                  refine ⟨218483508138312345043189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291311344184416460057585 218483508138312345043189)
                  ·
                    rfl

theorem cell20_478682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_478682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478682 prefixEnd_478682 := by exact prefixLift 478682
  have htrace : WordTrace (prefixWord ++ tailWord_478682) baseStart_478682 baseEnd_478682 := by
    simpa [prefixWord, tailWord_478682, baseEnd_478682] using wordTrace_append hprefix tailTrace_478682
  have hstable : (prefixWord ++ tailWord_478682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478682).length < 2 ^ (prefixWord ++ tailWord_478682).sum := by decide
  have hdescent : baseEnd_478682 < baseStart_478682 := by decide
  rcases family_descends (prefixWord ++ tailWord_478682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478703 : List Nat := [1, 1, 2, 1, 4, 1, 2, 6, 2]
def baseStart_478703 : Nat := 118140960795 + 478703 * 2 ^ 59
def prefixEnd_478703 : Nat := 4983230072969 + 3 ^ 40 * 478703 * 2
def baseEnd_478703 : Nat := 218493093110529605343103

theorem tailTrace_478703 : CollatzResearch.WordTrace tailWord_478703 prefixEnd_478703 218493093110529605343103 := by
  unfold tailWord_478703
  simp only [CollatzResearch.WordTrace]
  refine ⟨17459732784748261808584763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11639821856498841205723175 17459732784748261808584763)
  ·
    refine ⟨26189599177122392712877145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17459732784748261808584763 26189599177122392712877145)
    ·
      refine ⟨19642199382841794534657859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26189599177122392712877145 19642199382841794534657859)
      ·
        refine ⟨29463299074262691801986789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19642199382841794534657859 29463299074262691801986789)
        ·
          refine ⟨5524368576424254712872523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29463299074262691801986789 5524368576424254712872523)
          ·
            refine ⟨8286552864636382069308785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524368576424254712872523 8286552864636382069308785)
            ·
              refine ⟨6214914648477286551981589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8286552864636382069308785 6214914648477286551981589)
              ·
                refine ⟨291324124147372807124137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6214914648477286551981589 291324124147372807124137)
                ·
                  refine ⟨218493093110529605343103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291324124147372807124137 218493093110529605343103)
                  ·
                    rfl

theorem cell20_478703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 2].length) (baseStart_478703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478703 prefixEnd_478703 := by exact prefixLift 478703
  have htrace : WordTrace (prefixWord ++ tailWord_478703) baseStart_478703 baseEnd_478703 := by
    simpa [prefixWord, tailWord_478703, baseEnd_478703] using wordTrace_append hprefix tailTrace_478703
  have hstable : (prefixWord ++ tailWord_478703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478703).length < 2 ^ (prefixWord ++ tailWord_478703).sum := by decide
  have hdescent : baseEnd_478703 < baseStart_478703 := by decide
  rcases family_descends (prefixWord ++ tailWord_478703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478710 : List Nat := [5, 1, 1, 1, 2, 2, 1, 7]
def baseStart_478710 : Nat := 118140960795 + 478710 * 2 ^ 59
def prefixEnd_478710 : Nat := 4983230072969 + 3 ^ 40 * 478710 * 2
def baseEnd_478710 : Nat := 72832096033756230703247

theorem tailTrace_478710 : CollatzResearch.WordTrace tailWord_478710 prefixEnd_478710 72832096033756230703247 := by
  unfold tailWord_478710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091249255982681375255599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11639992063815268002726389 1091249255982681375255599)
  ·
    refine ⟨1636873883974022062883399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1091249255982681375255599 1636873883974022062883399)
    ·
      refine ⟨2455310825961033094325099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636873883974022062883399 2455310825961033094325099)
      ·
        refine ⟨3682966238941549641487649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455310825961033094325099 3682966238941549641487649)
        ·
          refine ⟨2762224679206162231115737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682966238941549641487649 2762224679206162231115737)
          ·
            refine ⟨2071668509404621673336803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762224679206162231115737 2071668509404621673336803)
            ·
              refine ⟨3107502764106932510005205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071668509404621673336803 3107502764106932510005205)
              ·
                refine ⟨72832096033756230703247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3107502764106932510005205 72832096033756230703247)
                ·
                  rfl

theorem cell20_478710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_478710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478710 prefixEnd_478710 := by exact prefixLift 478710
  have htrace : WordTrace (prefixWord ++ tailWord_478710) baseStart_478710 baseEnd_478710 := by
    simpa [prefixWord, tailWord_478710, baseEnd_478710] using wordTrace_append hprefix tailTrace_478710
  have hstable : (prefixWord ++ tailWord_478710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478710).length < 2 ^ (prefixWord ++ tailWord_478710).sum := by decide
  have hdescent : baseEnd_478710 < baseStart_478710 := by decide
  rcases family_descends (prefixWord ++ tailWord_478710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478796 : List Nat := [2, 2, 1, 3, 1, 4, 2, 3, 2]
def baseStart_478796 : Nat := 118140960795 + 478796 * 2 ^ 59
def prefixEnd_478796 : Nat := 4983230072969 + 3 ^ 40 * 478796 * 2
def baseEnd_478796 : Nat := 218535540844634615242723

theorem tailTrace_478796 : CollatzResearch.WordTrace tailWord_478796 prefixEnd_478796 218535540844634615242723 := by
  unfold tailWord_478796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731562386705669345860121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11642083182274225794480161 8731562386705669345860121)
  ·
    refine ⟨6548671790029252009395091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8731562386705669345860121 6548671790029252009395091)
    ·
      refine ⟨9823007685043878014092637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6548671790029252009395091 9823007685043878014092637)
      ·
        refine ⟨3683627881891454255284739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9823007685043878014092637 3683627881891454255284739)
        ·
          refine ⟨5525441822837181382927109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683627881891454255284739 5525441822837181382927109)
          ·
            refine ⟨1036020341781971509298833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5525441822837181382927109 1036020341781971509298833)
            ·
              refine ⟨777015256336478631974125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036020341781971509298833 777015256336478631974125)
              ·
                refine ⟨291380721126179486990297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 777015256336478631974125 291380721126179486990297)
                ·
                  refine ⟨218535540844634615242723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291380721126179486990297 218535540844634615242723)
                  ·
                    rfl

theorem cell20_478796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_478796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478796 prefixEnd_478796 := by exact prefixLift 478796
  have htrace : WordTrace (prefixWord ++ tailWord_478796) baseStart_478796 baseEnd_478796 := by
    simpa [prefixWord, tailWord_478796, baseEnd_478796] using wordTrace_append hprefix tailTrace_478796
  have hstable : (prefixWord ++ tailWord_478796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478796).length < 2 ^ (prefixWord ++ tailWord_478796).sum := by decide
  have hdescent : baseEnd_478796 < baseStart_478796 := by decide
  rcases family_descends (prefixWord ++ tailWord_478796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478806 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_478806 : Nat := 118140960795 + 478806 * 2 ^ 59
def prefixEnd_478806 : Nat := 4983230072969 + 3 ^ 40 * 478806 * 2
def baseEnd_478806 : Nat := 218540105117119024909349

theorem tailTrace_478806 : CollatzResearch.WordTrace tailWord_478806 prefixEnd_478806 218540105117119024909349 := by
  unfold tailWord_478806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091468093960944399974017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11642326335583406933056181 1091468093960944399974017)
  ·
    refine ⟨818601070470708299980513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1091468093960944399974017 818601070470708299980513)
    ·
      refine ⟨613950802853031224985385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818601070470708299980513 613950802853031224985385)
      ·
        refine ⟨460463102139773418739039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613950802853031224985385 460463102139773418739039)
        ·
          refine ⟨690694653209660128108559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460463102139773418739039 690694653209660128108559)
          ·
            refine ⟨1036041979814490192162839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690694653209660128108559 1036041979814490192162839)
            ·
              refine ⟨1554062969721735288244259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036041979814490192162839 1554062969721735288244259)
              ·
                refine ⟨2331094454582602932366389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554062969721735288244259 2331094454582602932366389)
                ·
                  refine ⟨218540105117119024909349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2331094454582602932366389 218540105117119024909349)
                  ·
                    rfl

theorem cell20_478806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_478806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478806 prefixEnd_478806 := by exact prefixLift 478806
  have htrace : WordTrace (prefixWord ++ tailWord_478806) baseStart_478806 baseEnd_478806 := by
    simpa [prefixWord, tailWord_478806, baseEnd_478806] using wordTrace_append hprefix tailTrace_478806
  have hstable : (prefixWord ++ tailWord_478806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478806).length < 2 ^ (prefixWord ++ tailWord_478806).sum := by decide
  have hdescent : baseEnd_478806 < baseStart_478806 := by decide
  rcases family_descends (prefixWord ++ tailWord_478806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478807 : List Nat := [1, 1, 3, 2, 2, 4, 7]
def baseStart_478807 : Nat := 118140960795 + 478807 * 2 ^ 59
def prefixEnd_478807 : Nat := 4983230072969 + 3 ^ 40 * 478807 * 2
def baseEnd_478807 : Nat := 24282284616040829541779

theorem tailTrace_478807 : CollatzResearch.WordTrace tailWord_478807 prefixEnd_478807 24282284616040829541779 := by
  unfold tailWord_478807
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463525976371487570370675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11642350650914325046913783 17463525976371487570370675)
  ·
    refine ⟨26195288964557231355556013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17463525976371487570370675 26195288964557231355556013)
    ·
      refine ⟨9823233361708961758333505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26195288964557231355556013 9823233361708961758333505)
      ·
        refine ⟨7367425021281721318750129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9823233361708961758333505 7367425021281721318750129)
        ·
          refine ⟨5525568765961290989062597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7367425021281721318750129 5525568765961290989062597)
          ·
            refine ⟨1036044143617742060449237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5525568765961290989062597 1036044143617742060449237)
            ·
              refine ⟨24282284616040829541779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1036044143617742060449237 24282284616040829541779)
              ·
                rfl

theorem cell20_478807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_478807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478807 prefixEnd_478807 := by exact prefixLift 478807
  have htrace : WordTrace (prefixWord ++ tailWord_478807) baseStart_478807 baseEnd_478807 := by
    simpa [prefixWord, tailWord_478807, baseEnd_478807] using wordTrace_append hprefix tailTrace_478807
  have hstable : (prefixWord ++ tailWord_478807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478807).length < 2 ^ (prefixWord ++ tailWord_478807).sum := by decide
  have hdescent : baseEnd_478807 < baseStart_478807 := by decide
  rcases family_descends (prefixWord ++ tailWord_478807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478813 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 4]
def baseStart_478813 : Nat := 118140960795 + 478813 * 2 ^ 59
def prefixEnd_478813 : Nat := 4983230072969 + 3 ^ 40 * 478813 * 2
def baseEnd_478813 : Nat := 218543300107858111675987

theorem tailTrace_478813 : CollatzResearch.WordTrace tailWord_478813 prefixEnd_478813 218543300107858111675987 := by
  unfold tailWord_478813
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463744814349750595089093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11642496542899833730059395 17463744814349750595089093)
  ·
    refine ⟨3274452152690578236579205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17463744814349750595089093 3274452152690578236579205)
    ·
      refine ⟨613959778629483419358601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3274452152690578236579205 613959778629483419358601)
      ·
        refine ⟨460469833972112564518951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613959778629483419358601 460469833972112564518951)
        ·
          refine ⟨690704750958168846778427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460469833972112564518951 690704750958168846778427)
          ·
            refine ⟨1036057126437253270167641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690704750958168846778427 1036057126437253270167641)
            ·
              refine ⟨777042844827939952625731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036057126437253270167641 777042844827939952625731)
              ·
                refine ⟨1165564267241909928938597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777042844827939952625731 1165564267241909928938597)
                ·
                  refine ⟨218543300107858111675987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165564267241909928938597 218543300107858111675987)
                  ·
                    rfl

theorem cell20_478813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_478813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478813 prefixEnd_478813 := by exact prefixLift 478813
  have htrace : WordTrace (prefixWord ++ tailWord_478813) baseStart_478813 baseEnd_478813 := by
    simpa [prefixWord, tailWord_478813, baseEnd_478813] using wordTrace_append hprefix tailTrace_478813
  have hstable : (prefixWord ++ tailWord_478813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478813).length < 2 ^ (prefixWord ++ tailWord_478813).sum := by decide
  have hdescent : baseEnd_478813 < baseStart_478813 := by decide
  rcases family_descends (prefixWord ++ tailWord_478813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478817 : List Nat := [1, 2, 3, 1, 1, 3, 1, 6, 2]
def baseStart_478817 : Nat := 118140960795 + 478817 * 2 ^ 59
def prefixEnd_478817 : Nat := 4983230072969 + 3 ^ 40 * 478817 * 2
def baseEnd_478817 : Nat := 218545125816851875542637

theorem tailTrace_478817 : CollatzResearch.WordTrace tailWord_478817 prefixEnd_478817 218545125816851875542637 := by
  unfold tailWord_478817
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463890706335259278234705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11642593804223506185489803 17463890706335259278234705)
  ·
    refine ⟨13097918029751444458676029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17463890706335259278234705 13097918029751444458676029)
    ·
      refine ⟨4911719261156791672003511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13097918029751444458676029 4911719261156791672003511)
      ·
        refine ⟨7367578891735187508005267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4911719261156791672003511 7367578891735187508005267)
        ·
          refine ⟨11051368337602781262007901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367578891735187508005267 11051368337602781262007901)
          ·
            refine ⟨4144263126601042973252963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11051368337602781262007901 4144263126601042973252963)
            ·
              refine ⟨6216394689901564459879445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144263126601042973252963 6216394689901564459879445)
              ·
                refine ⟨291393501089135834056849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6216394689901564459879445 291393501089135834056849)
                ·
                  refine ⟨218545125816851875542637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291393501089135834056849 218545125816851875542637)
                  ·
                    rfl

theorem cell20_478817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_478817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478817 prefixEnd_478817 := by exact prefixLift 478817
  have htrace : WordTrace (prefixWord ++ tailWord_478817) baseStart_478817 baseEnd_478817 := by
    simpa [prefixWord, tailWord_478817, baseEnd_478817] using wordTrace_append hprefix tailTrace_478817
  have hstable : (prefixWord ++ tailWord_478817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478817).length < 2 ^ (prefixWord ++ tailWord_478817).sum := by decide
  have hdescent : baseEnd_478817 < baseStart_478817 := by decide
  rcases family_descends (prefixWord ++ tailWord_478817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478862 : List Nat := [4, 1, 1, 3, 1, 4, 6]
def baseStart_478862 : Nat := 118140960795 + 478862 * 2 ^ 59
def prefixEnd_478862 : Nat := 4983230072969 + 3 ^ 40 * 478862 * 2
def baseEnd_478862 : Nat := 24285073893670191004717

theorem tailTrace_478862 : CollatzResearch.WordTrace tailWord_478862 prefixEnd_478862 24285073893670191004717 := by
  unfold tailWord_478862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183191498896528995452855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11643687994114821309081893 2183191498896528995452855)
  ·
    refine ⟨3274787248344793493179283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183191498896528995452855 3274787248344793493179283)
    ·
      refine ⟨4912180872517190239768925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3274787248344793493179283 4912180872517190239768925)
      ·
        refine ⟨1842067827193946339913347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4912180872517190239768925 1842067827193946339913347)
        ·
          refine ⟨2763101740790919509870021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842067827193946339913347 2763101740790919509870021)
          ·
            refine ⟨518081576398297408100629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2763101740790919509870021 518081576398297408100629)
            ·
              refine ⟨24285073893670191004717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 518081576398297408100629 24285073893670191004717)
              ·
                rfl

theorem cell20_478862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 6].length) (baseStart_478862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478862 prefixEnd_478862 := by exact prefixLift 478862
  have htrace : WordTrace (prefixWord ++ tailWord_478862) baseStart_478862 baseEnd_478862 := by
    simpa [prefixWord, tailWord_478862, baseEnd_478862] using wordTrace_append hprefix tailTrace_478862
  have hstable : (prefixWord ++ tailWord_478862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478862).length < 2 ^ (prefixWord ++ tailWord_478862).sum := by decide
  have hdescent : baseEnd_478862 < baseStart_478862 := by decide
  rcases family_descends (prefixWord ++ tailWord_478862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478868 : List Nat := [2, 4, 2, 2, 2, 1, 3, 2, 2]
def baseStart_478868 : Nat := 118140960795 + 478868 * 2 ^ 59
def prefixEnd_478868 : Nat := 4983230072969 + 3 ^ 40 * 478868 * 2
def baseEnd_478868 : Nat := 218568403606522364842429

theorem tailTrace_478868 : CollatzResearch.WordTrace tailWord_478868 prefixEnd_478868 218568403606522364842429 := by
  unfold tailWord_478868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8732875414575247494170629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11643833886100329992227505 8732875414575247494170629)
  ·
    refine ⟨1637414140232858905156993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8732875414575247494170629 1637414140232858905156993)
    ·
      refine ⟨1228060605174644178867745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1637414140232858905156993 1228060605174644178867745)
      ·
        refine ⟨921045453880983134150809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1228060605174644178867745 921045453880983134150809)
        ·
          refine ⟨690784090410737350613107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921045453880983134150809 690784090410737350613107)
          ·
            refine ⟨1036176135616106025919661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690784090410737350613107 1036176135616106025919661)
            ·
              refine ⟨388566050856039759719873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1036176135616106025919661 388566050856039759719873)
              ·
                refine ⟨291424538142029819789905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388566050856039759719873 291424538142029819789905)
                ·
                  refine ⟨218568403606522364842429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291424538142029819789905 218568403606522364842429)
                  ·
                    rfl

theorem cell20_478868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_478868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478868 prefixEnd_478868 := by exact prefixLift 478868
  have htrace : WordTrace (prefixWord ++ tailWord_478868) baseStart_478868 baseEnd_478868 := by
    simpa [prefixWord, tailWord_478868, baseEnd_478868] using wordTrace_append hprefix tailTrace_478868
  have hstable : (prefixWord ++ tailWord_478868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478868).length < 2 ^ (prefixWord ++ tailWord_478868).sum := by decide
  have hdescent : baseEnd_478868 < baseStart_478868 := by decide
  rcases family_descends (prefixWord ++ tailWord_478868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478879 : List Nat := [1, 1, 2, 7, 1, 1, 2, 5]
def baseStart_478879 : Nat := 118140960795 + 478879 * 2 ^ 59
def prefixEnd_478879 : Nat := 4983230072969 + 3 ^ 40 * 478879 * 2
def baseEnd_478879 : Nat := 72857808102085071825239

theorem tailTrace_478879 : CollatzResearch.WordTrace tailWord_478879 prefixEnd_478879 72857808102085071825239 := by
  unfold tailWord_478879
  simp only [CollatzResearch.WordTrace]
  refine ⟨17466152032110643866991691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11644101354740429244661127 17466152032110643866991691)
  ·
    refine ⟨26199228048165965800487537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17466152032110643866991691 26199228048165965800487537)
    ·
      refine ⟨19649421036124474350365653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26199228048165965800487537 19649421036124474350365653)
      ·
        refine ⟨460533305534167367586695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19649421036124474350365653 460533305534167367586695)
        ·
          refine ⟨690799958301251051380043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460533305534167367586695 690799958301251051380043)
          ·
            refine ⟨1036199937451876577070065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690799958301251051380043 1036199937451876577070065)
            ·
              refine ⟨777149953088907432802549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036199937451876577070065 777149953088907432802549)
              ·
                refine ⟨72857808102085071825239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777149953088907432802549 72857808102085071825239)
                ·
                  rfl

theorem cell20_478879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_478879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478879 prefixEnd_478879 := by exact prefixLift 478879
  have htrace : WordTrace (prefixWord ++ tailWord_478879) baseStart_478879 baseEnd_478879 := by
    simpa [prefixWord, tailWord_478879, baseEnd_478879] using wordTrace_append hprefix tailTrace_478879
  have hstable : (prefixWord ++ tailWord_478879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478879).length < 2 ^ (prefixWord ++ tailWord_478879).sum := by decide
  have hdescent : baseEnd_478879 < baseStart_478879 := by decide
  rcases family_descends (prefixWord ++ tailWord_478879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478883 : List Nat := [1, 1, 1, 4, 1, 1, 6, 5]
def baseStart_478883 : Nat := 118140960795 + 478883 * 2 ^ 59
def prefixEnd_478883 : Nat := 4983230072969 + 3 ^ 40 * 478883 * 2
def baseEnd_478883 : Nat := 72858416671749659780789

theorem tailTrace_478883 : CollatzResearch.WordTrace tailWord_478883 prefixEnd_478883 72858416671749659780789 := by
  unfold tailWord_478883
  simp only [CollatzResearch.WordTrace]
  refine ⟨17466297924096152550137303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11644198616064101700091535 17466297924096152550137303)
  ·
    refine ⟨26199446886144228825205955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17466297924096152550137303 26199446886144228825205955)
    ·
      refine ⟨39299170329216343237808933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26199446886144228825205955 39299170329216343237808933)
      ·
        refine ⟨7368594436728064357089175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39299170329216343237808933 7368594436728064357089175)
        ·
          refine ⟨11052891655092096535633763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368594436728064357089175 11052891655092096535633763)
          ·
            refine ⟨16579337482638144803450645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11052891655092096535633763 16579337482638144803450645)
            ·
              refine ⟨777156444498663037661749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16579337482638144803450645 777156444498663037661749)
              ·
                refine ⟨72858416671749659780789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777156444498663037661749 72858416671749659780789)
                ·
                  rfl

theorem cell20_478883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_478883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478883 prefixEnd_478883 := by exact prefixLift 478883
  have htrace : WordTrace (prefixWord ++ tailWord_478883) baseStart_478883 baseEnd_478883 := by
    simpa [prefixWord, tailWord_478883, baseEnd_478883] using wordTrace_append hprefix tailTrace_478883
  have hstable : (prefixWord ++ tailWord_478883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478883).length < 2 ^ (prefixWord ++ tailWord_478883).sum := by decide
  have hdescent : baseEnd_478883 < baseStart_478883 := by decide
  rcases family_descends (prefixWord ++ tailWord_478883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478938 : List Nat := [3, 1, 1, 2, 2, 5, 1, 5]
def baseStart_478938 : Nat := 118140960795 + 478938 * 2 ^ 59
def prefixEnd_478938 : Nat := 4983230072969 + 3 ^ 40 * 478938 * 2
def baseEnd_478938 : Nat := 72866784504637744169603

theorem tailTrace_478938 : CollatzResearch.WordTrace tailWord_478938 prefixEnd_478938 72866784504637744169603 := by
  unfold tailWord_478938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4367075984724224235847367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11645535959264597962259645 4367075984724224235847367)
  ·
    refine ⟨6550613977086336353771051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4367075984724224235847367 6550613977086336353771051)
    ·
      refine ⟨9825920965629504530656577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6550613977086336353771051 9825920965629504530656577)
      ·
        refine ⟨7369440724222128397992433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9825920965629504530656577 7369440724222128397992433)
        ·
          refine ⟨5527080543166596298494325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7369440724222128397992433 5527080543166596298494325)
          ·
            refine ⟨518163800921868402983843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5527080543166596298494325 518163800921868402983843)
            ·
              refine ⟨777245701382802604475765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518163800921868402983843 777245701382802604475765)
              ·
                refine ⟨72866784504637744169603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777245701382802604475765 72866784504637744169603)
                ·
                  rfl

theorem cell20_478938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_478938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478938 prefixEnd_478938 := by exact prefixLift 478938
  have htrace : WordTrace (prefixWord ++ tailWord_478938) baseStart_478938 baseEnd_478938 := by
    simpa [prefixWord, tailWord_478938, baseEnd_478938] using wordTrace_append hprefix tailTrace_478938
  have hstable : (prefixWord ++ tailWord_478938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478938).length < 2 ^ (prefixWord ++ tailWord_478938).sum := by decide
  have hdescent : baseEnd_478938 < baseStart_478938 := by decide
  rcases family_descends (prefixWord ++ tailWord_478938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478952 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_478952 : Nat := 118140960795 + 478952 * 2 ^ 59
def prefixEnd_478952 : Nat := 4983230072969 + 3 ^ 40 * 478952 * 2
def baseEnd_478952 : Nat := 218606743495391406042085

theorem tailTrace_478952 : CollatzResearch.WordTrace tailWord_478952 prefixEnd_478952 218606743495391406042085 := by
  unfold tailWord_478952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8734407280423088667199555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11645876373897451556266073 8734407280423088667199555)
  ·
    refine ⟨13101610920634633000799333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8734407280423088667199555 13101610920634633000799333)
    ·
      refine ⟨2456552047618993687649875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13101610920634633000799333 2456552047618993687649875)
      ·
        refine ⟨3684828071428490531474813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456552047618993687649875 3684828071428490531474813)
        ·
          refine ⟨1381810526785683949303055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3684828071428490531474813 1381810526785683949303055)
          ·
            refine ⟨2072715790178525923954583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381810526785683949303055 2072715790178525923954583)
            ·
              refine ⟨3109073685267788885931875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072715790178525923954583 3109073685267788885931875)
              ·
                refine ⟨4663610527901683328897813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109073685267788885931875 4663610527901683328897813)
                ·
                  refine ⟨218606743495391406042085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4663610527901683328897813 218606743495391406042085)
                  ·
                    rfl

theorem cell20_478952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_478952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478952 prefixEnd_478952 := by exact prefixLift 478952
  have htrace : WordTrace (prefixWord ++ tailWord_478952) baseStart_478952 baseEnd_478952 := by
    simpa [prefixWord, tailWord_478952, baseEnd_478952] using wordTrace_append hprefix tailTrace_478952
  have hstable : (prefixWord ++ tailWord_478952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478952).length < 2 ^ (prefixWord ++ tailWord_478952).sum := by decide
  have hdescent : baseEnd_478952 < baseStart_478952 := by decide
  rcases family_descends (prefixWord ++ tailWord_478952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478990 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_478990 : Nat := 118140960795 + 478990 * 2 ^ 59
def prefixEnd_478990 : Nat := 4983230072969 + 3 ^ 40 * 478990 * 2
def baseEnd_478990 : Nat := 218624087730832162775263

theorem tailTrace_478990 : CollatzResearch.WordTrace tailWord_478990 prefixEnd_478990 218624087730832162775263 := by
  unfold tailWord_478990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183775066838563728035303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11646800356472339882854949 2183775066838563728035303)
  ·
    refine ⟨3275662600257845592052955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183775066838563728035303 3275662600257845592052955)
    ·
      refine ⟨4913493900386768388079433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275662600257845592052955 4913493900386768388079433)
      ·
        refine ⟨3685120425290076291059575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4913493900386768388079433 3685120425290076291059575)
        ·
          refine ⟨5527680637935114436589363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685120425290076291059575 5527680637935114436589363)
          ·
            refine ⟨8291520956902671654884045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527680637935114436589363 8291520956902671654884045)
            ·
              refine ⟨3109320358838501870581517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8291520956902671654884045 3109320358838501870581517)
              ·
                refine ⟨1165995134564438201468069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3109320358838501870581517 1165995134564438201468069)
                ·
                  refine ⟨218624087730832162775263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165995134564438201468069 218624087730832162775263)
                  ·
                    rfl

theorem cell20_478990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_478990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_478990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_478990 prefixEnd_478990 := by exact prefixLift 478990
  have htrace : WordTrace (prefixWord ++ tailWord_478990) baseStart_478990 baseEnd_478990 := by
    simpa [prefixWord, tailWord_478990, baseEnd_478990] using wordTrace_append hprefix tailTrace_478990
  have hstable : (prefixWord ++ tailWord_478990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478990).length < 2 ^ (prefixWord ++ tailWord_478990).sum := by decide
  have hdescent : baseEnd_478990 < baseStart_478990 := by decide
  rcases family_descends (prefixWord ++ tailWord_478990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479006 : List Nat := [4, 3, 2, 2, 2, 1, 2, 4]
def baseStart_479006 : Nat := 118140960795 + 479006 * 2 ^ 59
def prefixEnd_479006 : Nat := 4983230072969 + 3 ^ 40 * 479006 * 2
def baseEnd_479006 : Nat := 72877130188935739413955

theorem tailTrace_479006 : CollatzResearch.WordTrace tailWord_479006 prefixEnd_479006 72877130188935739413955 := by
  unfold tailWord_479006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183848012831318069608109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11647189401767029704576581 2183848012831318069608109)
  ·
    refine ⟨818943004811744276103041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2183848012831318069608109 818943004811744276103041)
    ·
      refine ⟨614207253608808207077281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818943004811744276103041 614207253608808207077281)
      ·
        refine ⟨460655440206606155307961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614207253608808207077281 460655440206606155307961)
        ·
          refine ⟨345491580154954616480971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460655440206606155307961 345491580154954616480971)
          ·
            refine ⟨518237370232431924721457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345491580154954616480971 518237370232431924721457)
            ·
              refine ⟨388678027674323943541093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518237370232431924721457 388678027674323943541093)
              ·
                refine ⟨72877130188935739413955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388678027674323943541093 72877130188935739413955)
                ·
                  rfl

theorem cell20_479006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_479006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479006 prefixEnd_479006 := by exact prefixLift 479006
  have htrace : WordTrace (prefixWord ++ tailWord_479006) baseStart_479006 baseEnd_479006 := by
    simpa [prefixWord, tailWord_479006, baseEnd_479006] using wordTrace_append hprefix tailTrace_479006
  have hstable : (prefixWord ++ tailWord_479006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479006).length < 2 ^ (prefixWord ++ tailWord_479006).sum := by decide
  have hdescent : baseEnd_479006 < baseStart_479006 := by decide
  rcases family_descends (prefixWord ++ tailWord_479006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479052 : List Nat := [2, 2, 1, 3, 4, 1, 2, 5]
def baseStart_479052 : Nat := 118140960795 + 479052 * 2 ^ 59
def prefixEnd_479052 : Nat := 4983230072969 + 3 ^ 40 * 479052 * 2
def baseEnd_479052 : Nat := 72884128740078500902781

theorem tailTrace_479052 : CollatzResearch.WordTrace tailWord_479052 prefixEnd_479052 72884128740078500902781 := by
  unfold tailWord_479052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8736230930241947206519705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11648307906989262942026273 8736230930241947206519705)
  ·
    refine ⟨6552173197681460404889779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8736230930241947206519705 6552173197681460404889779)
    ·
      refine ⟨9828259796522190607334669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6552173197681460404889779 9828259796522190607334669)
      ·
        refine ⟨3685597423695821477750501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9828259796522190607334669 3685597423695821477750501)
        ·
          refine ⟨691049516942966527078219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3685597423695821477750501 691049516942966527078219)
          ·
            refine ⟨1036574275414449790617329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691049516942966527078219 1036574275414449790617329)
            ·
              refine ⟨777430706560837342962997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036574275414449790617329 777430706560837342962997)
              ·
                refine ⟨72884128740078500902781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777430706560837342962997 72884128740078500902781)
                ·
                  rfl

theorem cell20_479052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_479052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479052 prefixEnd_479052 := by exact prefixLift 479052
  have htrace : WordTrace (prefixWord ++ tailWord_479052) baseStart_479052 baseEnd_479052 := by
    simpa [prefixWord, tailWord_479052, baseEnd_479052] using wordTrace_append hprefix tailTrace_479052
  have hstable : (prefixWord ++ tailWord_479052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479052).length < 2 ^ (prefixWord ++ tailWord_479052).sum := by decide
  have hdescent : baseEnd_479052 < baseStart_479052 := by decide
  rcases family_descends (prefixWord ++ tailWord_479052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479097 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 3]
def baseStart_479097 : Nat := 118140960795 + 479097 * 2 ^ 59
def prefixEnd_479097 : Nat := 4983230072969 + 3 ^ 40 * 479097 * 2
def baseEnd_479097 : Nat := 218672925446415346208159

theorem tailTrace_479097 : CollatzResearch.WordTrace tailWord_479097 prefixEnd_479097 218672925446415346208159 := by
  unfold tailWord_479097
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474103145320867098427545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11649402096880578065618363 17474103145320867098427545)
  ·
    refine ⟨13105577358990650323820659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17474103145320867098427545 13105577358990650323820659)
    ·
      refine ⟨19658366038485975485730989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13105577358990650323820659 19658366038485975485730989)
      ·
        refine ⟨7371887264432240807149121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19658366038485975485730989 7371887264432240807149121)
        ·
          refine ⟨5528915448324180605361841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7371887264432240807149121 5528915448324180605361841)
          ·
            refine ⟨4146686586243135454021381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5528915448324180605361841 4146686586243135454021381)
            ·
              refine ⟨777503734920587897629009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4146686586243135454021381 777503734920587897629009)
              ·
                refine ⟨583127801190440923221757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777503734920587897629009 583127801190440923221757)
                ·
                  refine ⟨218672925446415346208159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583127801190440923221757 218672925446415346208159)
                  ·
                    rfl

theorem cell20_479097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_479097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479097 prefixEnd_479097 := by exact prefixLift 479097
  have htrace : WordTrace (prefixWord ++ tailWord_479097) baseStart_479097 baseEnd_479097 := by
    simpa [prefixWord, tailWord_479097, baseEnd_479097] using wordTrace_append hprefix tailTrace_479097
  have hstable : (prefixWord ++ tailWord_479097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479097).length < 2 ^ (prefixWord ++ tailWord_479097).sum := by decide
  have hdescent : baseEnd_479097 < baseStart_479097 := by decide
  rcases family_descends (prefixWord ++ tailWord_479097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479134 : List Nat := [4, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_479134 : Nat := 118140960795 + 479134 * 2 ^ 59
def prefixEnd_479134 : Nat := 4983230072969 + 3 ^ 40 * 479134 * 2
def baseEnd_479134 : Nat := 218689813254607661974675

theorem tailTrace_479134 : CollatzResearch.WordTrace tailWord_479134 prefixEnd_479134 218689813254607661974675 := by
  unfold tailWord_479134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2184431580773352802190557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11650301764124548278349637 2184431580773352802190557)
  ·
    refine ⟨819161842790007300821459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2184431580773352802190557 819161842790007300821459)
    ·
      refine ⟨1228742764185010951232189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819161842790007300821459 1228742764185010951232189)
      ·
        refine ⟨460778536569379106712071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1228742764185010951232189 460778536569379106712071)
        ·
          refine ⟨691167804854068660068107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460778536569379106712071 691167804854068660068107)
          ·
            refine ⟨1036751707281102990102161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691167804854068660068107 1036751707281102990102161)
            ·
              refine ⟨777563780460827242576621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036751707281102990102161 777563780460827242576621)
              ·
                refine ⟨291586417672810215966233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 777563780460827242576621 291586417672810215966233)
                ·
                  refine ⟨218689813254607661974675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291586417672810215966233 218689813254607661974675)
                  ·
                    rfl

theorem cell20_479134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_479134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479134 prefixEnd_479134 := by exact prefixLift 479134
  have htrace : WordTrace (prefixWord ++ tailWord_479134) baseStart_479134 baseEnd_479134 := by
    simpa [prefixWord, tailWord_479134, baseEnd_479134] using wordTrace_append hprefix tailTrace_479134
  have hstable : (prefixWord ++ tailWord_479134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479134).length < 2 ^ (prefixWord ++ tailWord_479134).sum := by decide
  have hdescent : baseEnd_479134 < baseStart_479134 := by decide
  rcases family_descends (prefixWord ++ tailWord_479134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479163 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_479163 : Nat := 118140960795 + 479163 * 2 ^ 59
def prefixEnd_479163 : Nat := 4983230072969 + 3 ^ 40 * 479163 * 2
def baseEnd_479163 : Nat := 218703049644812450007889

theorem tailTrace_479163 : CollatzResearch.WordTrace tailWord_479163 prefixEnd_479163 218703049644812450007889 := by
  unfold tailWord_479163
  simp only [CollatzResearch.WordTrace]
  refine ⟨17476510363081760370330143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11651006908721173580220095 17476510363081760370330143)
  ·
    refine ⟨26214765544622640555495215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17476510363081760370330143 26214765544622640555495215)
    ·
      refine ⟨39322148316933960833242823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26214765544622640555495215 39322148316933960833242823)
      ·
        refine ⟨58983222475400941249864235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39322148316933960833242823 58983222475400941249864235)
        ·
          refine ⟨88474833713101411874796353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58983222475400941249864235 88474833713101411874796353)
          ·
            refine ⟨66356125284826058906097265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88474833713101411874796353 66356125284826058906097265)
            ·
              refine ⟨49767093963619544179572949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66356125284826058906097265 49767093963619544179572949)
              ·
                refine ⟨1166416264772333066708741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49767093963619544179572949 1166416264772333066708741)
                ·
                  refine ⟨218703049644812450007889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166416264772333066708741 218703049644812450007889)
                  ·
                    rfl

theorem cell20_479163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_479163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479163 prefixEnd_479163 := by exact prefixLift 479163
  have htrace : WordTrace (prefixWord ++ tailWord_479163) baseStart_479163 baseEnd_479163 := by
    simpa [prefixWord, tailWord_479163, baseEnd_479163] using wordTrace_append hprefix tailTrace_479163
  have hstable : (prefixWord ++ tailWord_479163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479163).length < 2 ^ (prefixWord ++ tailWord_479163).sum := by decide
  have hdescent : baseEnd_479163 < baseStart_479163 := by decide
  rcases family_descends (prefixWord ++ tailWord_479163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479180 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_479180 : Nat := 118140960795 + 479180 * 2 ^ 59
def prefixEnd_479180 : Nat := 4983230072969 + 3 ^ 40 * 479180 * 2
def baseEnd_479180 : Nat := 218710808908035946441153

theorem tailTrace_479180 : CollatzResearch.WordTrace tailWord_479180 prefixEnd_479180 218710808908035946441153 := by
  unfold tailWord_479180
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738565202010086136849497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11651420269346781515799329 8738565202010086136849497)
  ·
    refine ⟨6553923901507564602637123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8738565202010086136849497 6553923901507564602637123)
    ·
      refine ⟨9830885852261346903955685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6553923901507564602637123 9830885852261346903955685)
      ·
        refine ⟨1843291097299002544491691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9830885852261346903955685 1843291097299002544491691)
        ·
          refine ⟨2764936645948503816737537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843291097299002544491691 2764936645948503816737537)
          ·
            refine ⟨2073702484461377862553153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2764936645948503816737537 2073702484461377862553153)
            ·
              refine ⟨1555276863346033396914865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073702484461377862553153 1555276863346033396914865)
              ·
                refine ⟨1166457647509525047686149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555276863346033396914865 1166457647509525047686149)
                ·
                  refine ⟨218710808908035946441153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166457647509525047686149 218710808908035946441153)
                  ·
                    rfl

theorem cell20_479180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_479180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479180 prefixEnd_479180 := by exact prefixLift 479180
  have htrace : WordTrace (prefixWord ++ tailWord_479180) baseStart_479180 baseEnd_479180 := by
    simpa [prefixWord, tailWord_479180, baseEnd_479180] using wordTrace_append hprefix tailTrace_479180
  have hstable : (prefixWord ++ tailWord_479180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479180).length < 2 ^ (prefixWord ++ tailWord_479180).sum := by decide
  have hdescent : baseEnd_479180 < baseStart_479180 := by decide
  rcases family_descends (prefixWord ++ tailWord_479180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479193 : List Nat := [1, 2, 1, 2, 7, 1, 1, 3, 2]
def baseStart_479193 : Nat := 118140960795 + 479193 * 2 ^ 59
def prefixEnd_479193 : Nat := 4983230072969 + 3 ^ 40 * 479193 * 2
def baseEnd_479193 : Nat := 218716742462265679007767

theorem tailTrace_479193 : CollatzResearch.WordTrace tailWord_479193 prefixEnd_479193 218716742462265679007767 := by
  unfold tailWord_479193
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477604552973075493922233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11651736368648716995948155 17477604552973075493922233)
  ·
    refine ⟨13108203414729806620441675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17477604552973075493922233 13108203414729806620441675)
    ·
      refine ⟨19662305122094709930662513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13108203414729806620441675 19662305122094709930662513)
      ·
        refine ⟨14746728841571032447996885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19662305122094709930662513 14746728841571032447996885)
        ·
          refine ⟨345626457224321072999927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14746728841571032447996885 345626457224321072999927)
          ·
            refine ⟨518439685836481609499891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345626457224321072999927 518439685836481609499891)
            ·
              refine ⟨777659528754722414249837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518439685836481609499891 777659528754722414249837)
              ·
                refine ⟨291622323283020905343689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 777659528754722414249837 291622323283020905343689)
                ·
                  refine ⟨218716742462265679007767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291622323283020905343689 218716742462265679007767)
                  ·
                    rfl

theorem cell20_479193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_479193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479193 prefixEnd_479193 := by exact prefixLift 479193
  have htrace : WordTrace (prefixWord ++ tailWord_479193) baseStart_479193 baseEnd_479193 := by
    simpa [prefixWord, tailWord_479193, baseEnd_479193] using wordTrace_append hprefix tailTrace_479193
  have hstable : (prefixWord ++ tailWord_479193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479193).length < 2 ^ (prefixWord ++ tailWord_479193).sum := by decide
  have hdescent : baseEnd_479193 < baseStart_479193 := by decide
  rcases family_descends (prefixWord ++ tailWord_479193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479201 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_479201 : Nat := 118140960795 + 479201 * 2 ^ 59
def prefixEnd_479201 : Nat := 4983230072969 + 3 ^ 40 * 479201 * 2
def baseEnd_479201 : Nat := 218720393880253206741067

theorem tailTrace_479201 : CollatzResearch.WordTrace tailWord_479201 prefixEnd_479201 218720393880253206741067 := by
  unfold tailWord_479201
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477896336944092860213457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11651930891296061906808971 17477896336944092860213457)
  ·
    refine ⟨13108422252708069645160093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17477896336944092860213457 13108422252708069645160093)
    ·
      refine ⟨4915658344765526116935035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13108422252708069645160093 4915658344765526116935035)
      ·
        refine ⟨7373487517148289175402553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4915658344765526116935035 7373487517148289175402553)
        ·
          refine ⟨5530115637861216881551915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7373487517148289175402553 5530115637861216881551915)
          ·
            refine ⟨8295173456791825322327873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530115637861216881551915 8295173456791825322327873)
            ·
              refine ⟨6221380092593868991745905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8295173456791825322327873 6221380092593868991745905)
              ·
                refine ⟨4666035069445401743809429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6221380092593868991745905 4666035069445401743809429)
                ·
                  refine ⟨218720393880253206741067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4666035069445401743809429 218720393880253206741067)
                  ·
                    rfl

theorem cell20_479201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_479201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479201 prefixEnd_479201 := by exact prefixLift 479201
  have htrace : WordTrace (prefixWord ++ tailWord_479201) baseStart_479201 baseEnd_479201 := by
    simpa [prefixWord, tailWord_479201, baseEnd_479201] using wordTrace_append hprefix tailTrace_479201
  have hstable : (prefixWord ++ tailWord_479201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479201).length < 2 ^ (prefixWord ++ tailWord_479201).sum := by decide
  have hdescent : baseEnd_479201 < baseStart_479201 := by decide
  rcases family_descends (prefixWord ++ tailWord_479201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479225 : List Nat := [1, 2, 1, 3, 1, 5, 2, 5]
def baseStart_479225 : Nat := 118140960795 + 479225 * 2 ^ 59
def prefixEnd_479225 : Nat := 4983230072969 + 3 ^ 40 * 479225 * 2
def baseEnd_479225 : Nat := 72910449378071929980323

theorem tailTrace_479225 : CollatzResearch.WordTrace tailWord_479225 prefixEnd_479225 72910449378071929980323 := by
  unfold tailWord_479225
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478771688857144959087129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11652514459238096639391419 17478771688857144959087129)
  ·
    refine ⟨13109078766642858719315347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17478771688857144959087129 13109078766642858719315347)
    ·
      refine ⟨19663618149964288078973021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13109078766642858719315347 19663618149964288078973021)
      ·
        refine ⟨7373856806236608029614883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19663618149964288078973021 7373856806236608029614883)
        ·
          refine ⟨11060785209354912044422325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373856806236608029614883 11060785209354912044422325)
          ·
            refine ⟨1036948613377023004164593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11060785209354912044422325 1036948613377023004164593)
            ·
              refine ⟨777711460032767253123445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036948613377023004164593 777711460032767253123445)
              ·
                refine ⟨72910449378071929980323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777711460032767253123445 72910449378071929980323)
                ·
                  rfl

theorem cell20_479225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_479225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479225 prefixEnd_479225 := by exact prefixLift 479225
  have htrace : WordTrace (prefixWord ++ tailWord_479225) baseStart_479225 baseEnd_479225 := by
    simpa [prefixWord, tailWord_479225, baseEnd_479225] using wordTrace_append hprefix tailTrace_479225
  have hstable : (prefixWord ++ tailWord_479225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479225).length < 2 ^ (prefixWord ++ tailWord_479225).sum := by decide
  have hdescent : baseEnd_479225 < baseStart_479225 := by decide
  rcases family_descends (prefixWord ++ tailWord_479225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479322 : List Nat := [3, 1, 1, 2, 1, 1, 11]
def baseStart_479322 : Nat := 118140960795 + 479322 * 2 ^ 59
def prefixEnd_479322 : Nat := 4983230072969 + 3 ^ 40 * 479322 * 2
def baseEnd_479322 : Nat := 24308402397479395967471

theorem tailTrace_479322 : CollatzResearch.WordTrace tailWord_479322 prefixEnd_479322 24308402397479395967471 := by
  unfold tailWord_479322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370577392376432631342055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11654873046337153683578813 4370577392376432631342055)
  ·
    refine ⟨6555866088564648947013083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4370577392376432631342055 6555866088564648947013083)
    ·
      refine ⟨9833799132846973420519625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6555866088564648947013083 9833799132846973420519625)
      ·
        refine ⟨7375349349635230065389719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9833799132846973420519625 7375349349635230065389719)
        ·
          refine ⟨11063024024452845098084579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375349349635230065389719 11063024024452845098084579)
          ·
            refine ⟨16594536036679267647126869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063024024452845098084579 16594536036679267647126869)
            ·
              refine ⟨24308402397479395967471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16594536036679267647126869 24308402397479395967471)
              ·
                rfl

theorem cell20_479322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 11].length) (baseStart_479322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479322 prefixEnd_479322 := by exact prefixLift 479322
  have htrace : WordTrace (prefixWord ++ tailWord_479322) baseStart_479322 baseEnd_479322 := by
    simpa [prefixWord, tailWord_479322, baseEnd_479322] using wordTrace_append hprefix tailTrace_479322
  have hstable : (prefixWord ++ tailWord_479322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479322).length < 2 ^ (prefixWord ++ tailWord_479322).sum := by decide
  have hdescent : baseEnd_479322 < baseStart_479322 := by decide
  rcases family_descends (prefixWord ++ tailWord_479322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479342 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_479342 : Nat := 118140960795 + 479342 * 2 ^ 59
def prefixEnd_479342 : Nat := 4983230072969 + 3 ^ 40 * 479342 * 2
def baseEnd_479342 : Nat := 218784750122283383040491

theorem tailTrace_479342 : CollatzResearch.WordTrace tailWord_479342 prefixEnd_479342 218784750122283383040491 := by
  unfold tailWord_479342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185379878679159242637035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11655359352955515960730853 2185379878679159242637035)
  ·
    refine ⟨3278069818018738863955553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185379878679159242637035 3278069818018738863955553)
    ·
      refine ⟨2458552363514054147966665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3278069818018738863955553 2458552363514054147966665)
      ·
        refine ⟨1843914272635540610974999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458552363514054147966665 1843914272635540610974999)
        ·
          refine ⟨2765871408953310916462499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843914272635540610974999 2765871408953310916462499)
          ·
            refine ⟨4148807113429966374693749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765871408953310916462499 4148807113429966374693749)
            ·
              refine ⟨388950666884059347627539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4148807113429966374693749 388950666884059347627539)
              ·
                refine ⟨583426000326089021441309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388950666884059347627539 583426000326089021441309)
                ·
                  refine ⟨218784750122283383040491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583426000326089021441309 218784750122283383040491)
                  ·
                    rfl

theorem cell20_479342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_479342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479342 prefixEnd_479342 := by exact prefixLift 479342
  have htrace : WordTrace (prefixWord ++ tailWord_479342) baseStart_479342 baseEnd_479342 := by
    simpa [prefixWord, tailWord_479342, baseEnd_479342] using wordTrace_append hprefix tailTrace_479342
  have hstable : (prefixWord ++ tailWord_479342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479342).length < 2 ^ (prefixWord ++ tailWord_479342).sum := by decide
  have hdescent : baseEnd_479342 < baseStart_479342 := by decide
  rcases family_descends (prefixWord ++ tailWord_479342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479356 : List Nat := [2, 2, 2, 1, 1, 6, 2, 4]
def baseStart_479356 : Nat := 118140960795 + 479356 * 2 ^ 59
def prefixEnd_479356 : Nat := 4983230072969 + 3 ^ 40 * 479356 * 2
def baseEnd_479356 : Nat := 72930380034587185524589

theorem tailTrace_479356 : CollatzResearch.WordTrace tailWord_479356 prefixEnd_479356 72930380034587185524589 := by
  unfold tailWord_479356
  simp only [CollatzResearch.WordTrace]
  refine ⟨8741774825691277166052961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11655699767588369554737281 8741774825691277166052961)
  ·
    refine ⟨6556331119268457874539721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8741774825691277166052961 6556331119268457874539721)
    ·
      refine ⟨4917248339451343405904791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6556331119268457874539721 4917248339451343405904791)
      ·
        refine ⟨7375872509177015108857187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917248339451343405904791 7375872509177015108857187)
        ·
          refine ⟨11063808763765522663285781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375872509177015108857187 11063808763765522663285781)
          ·
            refine ⟨518616035801508874841521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11063808763765522663285781 518616035801508874841521)
            ·
              refine ⟨388962026851131656131141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518616035801508874841521 388962026851131656131141)
              ·
                refine ⟨72930380034587185524589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388962026851131656131141 72930380034587185524589)
                ·
                  rfl

theorem cell20_479356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_479356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479356 prefixEnd_479356 := by exact prefixLift 479356
  have htrace : WordTrace (prefixWord ++ tailWord_479356) baseStart_479356 baseEnd_479356 := by
    simpa [prefixWord, tailWord_479356, baseEnd_479356] using wordTrace_append hprefix tailTrace_479356
  have hstable : (prefixWord ++ tailWord_479356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479356).length < 2 ^ (prefixWord ++ tailWord_479356).sum := by decide
  have hdescent : baseEnd_479356 < baseStart_479356 := by decide
  rcases family_descends (prefixWord ++ tailWord_479356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479394 : List Nat := [3, 3, 1, 3, 1, 2, 2, 5]
def baseStart_479394 : Nat := 118140960795 + 479394 * 2 ^ 59
def prefixEnd_479394 : Nat := 4983230072969 + 3 ^ 40 * 479394 * 2
def baseEnd_479394 : Nat := 72936161446400771102315

theorem tailTrace_479394 : CollatzResearch.WordTrace tailWord_479394 prefixEnd_479394 72936161446400771102315 := by
  unfold tailWord_479394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371233906311221705497309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11656623750163257881326157 4371233906311221705497309)
  ·
    refine ⟨1639212714866708139561491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4371233906311221705497309 1639212714866708139561491)
    ·
      refine ⟨2458819072300062209342237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639212714866708139561491 2458819072300062209342237)
      ·
        refine ⟨922057152112523328503339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2458819072300062209342237 922057152112523328503339)
        ·
          refine ⟨1383085728168784992755009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922057152112523328503339 1383085728168784992755009)
          ·
            refine ⟨1037314296126588744566257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383085728168784992755009 1037314296126588744566257)
            ·
              refine ⟨777985722094941558424693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037314296126588744566257 777985722094941558424693)
              ·
                refine ⟨72936161446400771102315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777985722094941558424693 72936161446400771102315)
                ·
                  rfl

theorem cell20_479394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_479394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479394 prefixEnd_479394 := by exact prefixLift 479394
  have htrace : WordTrace (prefixWord ++ tailWord_479394) baseStart_479394 baseEnd_479394 := by
    simpa [prefixWord, tailWord_479394, baseEnd_479394] using wordTrace_append hprefix tailTrace_479394
  have hstable : (prefixWord ++ tailWord_479394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479394).length < 2 ^ (prefixWord ++ tailWord_479394).sum := by decide
  have hdescent : baseEnd_479394 < baseStart_479394 := by decide
  rcases family_descends (prefixWord ++ tailWord_479394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479442 : List Nat := [3, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_479442 : Nat := 118140960795 + 479442 * 2 ^ 59
def prefixEnd_479442 : Nat := 4983230072969 + 3 ^ 40 * 479442 * 2
def baseEnd_479442 : Nat := 218830392847127479706749

theorem tailTrace_479442 : CollatzResearch.WordTrace tailWord_479442 prefixEnd_479442 218830392847127479706749 := by
  unfold tailWord_479442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371671582267747754934145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11657790886047327346491053 4371671582267747754934145)
  ·
    refine ⟨3278753686700810816200609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4371671582267747754934145 3278753686700810816200609)
    ·
      refine ⟨2459065265025608112150457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3278753686700810816200609 2459065265025608112150457)
      ·
        refine ⟨1844298948769206084112843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2459065265025608112150457 1844298948769206084112843)
        ·
          refine ⟨2766448423153809126169265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844298948769206084112843 2766448423153809126169265)
          ·
            refine ⟨2074836317365356844626949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766448423153809126169265 2074836317365356844626949)
            ·
              refine ⟨389031809506004408367553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2074836317365356844626949 389031809506004408367553)
              ·
                refine ⟨291773857129503306275665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389031809506004408367553 291773857129503306275665)
                ·
                  refine ⟨218830392847127479706749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291773857129503306275665 218830392847127479706749)
                  ·
                    rfl

theorem cell20_479442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_479442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479442 prefixEnd_479442 := by exact prefixLift 479442
  have htrace : WordTrace (prefixWord ++ tailWord_479442) baseStart_479442 baseEnd_479442 := by
    simpa [prefixWord, tailWord_479442, baseEnd_479442] using wordTrace_append hprefix tailTrace_479442
  have hstable : (prefixWord ++ tailWord_479442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479442).length < 2 ^ (prefixWord ++ tailWord_479442).sum := by decide
  have hdescent : baseEnd_479442 < baseStart_479442 := by decide
  rcases family_descends (prefixWord ++ tailWord_479442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479467 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_479467 : Nat := 118140960795 + 479467 * 2 ^ 59
def prefixEnd_479467 : Nat := 4983230072969 + 3 ^ 40 * 479467 * 2
def baseEnd_479467 : Nat := 218841803528338503873313

theorem tailTrace_479467 : CollatzResearch.WordTrace tailWord_479467 prefixEnd_479467 218841803528338503873313 := by
  unfold tailWord_479467
  simp only [CollatzResearch.WordTrace]
  refine ⟨17487598153980420289396655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11658398769320280192931103 17487598153980420289396655)
  ·
    refine ⟨26231397230970630434094983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17487598153980420289396655 26231397230970630434094983)
    ·
      refine ⟨39347095846455945651142475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26231397230970630434094983 39347095846455945651142475)
      ·
        refine ⟨59020643769683918476713713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39347095846455945651142475 59020643769683918476713713)
        ·
          refine ⟨44265482827262938857535285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59020643769683918476713713 44265482827262938857535285)
          ·
            refine ⟨4149889015055900517893933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44265482827262938857535285 4149889015055900517893933)
            ·
              refine ⟨1556208380645962694210225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4149889015055900517893933 1556208380645962694210225)
              ·
                refine ⟨1167156285484472020657669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556208380645962694210225 1167156285484472020657669)
                ·
                  refine ⟨218841803528338503873313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167156285484472020657669 218841803528338503873313)
                  ·
                    rfl

theorem cell20_479467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_479467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479467 prefixEnd_479467 := by exact prefixLift 479467
  have htrace : WordTrace (prefixWord ++ tailWord_479467) baseStart_479467 baseEnd_479467 := by
    simpa [prefixWord, tailWord_479467, baseEnd_479467] using wordTrace_append hprefix tailTrace_479467
  have hstable : (prefixWord ++ tailWord_479467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479467).length < 2 ^ (prefixWord ++ tailWord_479467).sum := by decide
  have hdescent : baseEnd_479467 < baseStart_479467 := by decide
  rcases family_descends (prefixWord ++ tailWord_479467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479505 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_479505 : Nat := 118140960795 + 479505 * 2 ^ 59
def prefixEnd_479505 : Nat := 4983230072969 + 3 ^ 40 * 479505 * 2
def baseEnd_479505 : Nat := 218859147763779260606491

theorem tailTrace_479505 : CollatzResearch.WordTrace tailWord_479505 prefixEnd_479505 218859147763779260606491 := by
  unfold tailWord_479505
  simp only [CollatzResearch.WordTrace]
  refine ⟨17488984127842752779279969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11659322751895168519519979 17488984127842752779279969)
  ·
    refine ⟨13116738095882064584459977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17488984127842752779279969 13116738095882064584459977)
    ·
      refine ⟨9837553571911548438344983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13116738095882064584459977 9837553571911548438344983)
      ·
        refine ⟨14756330357867322657517475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837553571911548438344983 14756330357867322657517475)
        ·
          refine ⟨22134495536800983986276213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756330357867322657517475 22134495536800983986276213)
          ·
            refine ⟨2075108956575092248713395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22134495536800983986276213 2075108956575092248713395)
            ·
              refine ⟨3112663434862638373070093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075108956575092248713395 3112663434862638373070093)
              ·
                refine ⟨1167248788073489389901285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112663434862638373070093 1167248788073489389901285)
                ·
                  refine ⟨218859147763779260606491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167248788073489389901285 218859147763779260606491)
                  ·
                    rfl

theorem cell20_479505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_479505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479505 prefixEnd_479505 := by exact prefixLift 479505
  have htrace : WordTrace (prefixWord ++ tailWord_479505) baseStart_479505 baseEnd_479505 := by
    simpa [prefixWord, tailWord_479505, baseEnd_479505] using wordTrace_append hprefix tailTrace_479505
  have hstable : (prefixWord ++ tailWord_479505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479505).length < 2 ^ (prefixWord ++ tailWord_479505).sum := by decide
  have hdescent : baseEnd_479505 < baseStart_479505 := by decide
  rcases family_descends (prefixWord ++ tailWord_479505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479512 : List Nat := [2, 1, 2, 3, 1, 2, 2, 7]
def baseStart_479512 : Nat := 118140960795 + 479512 * 2 ^ 59
def prefixEnd_479512 : Nat := 4983230072969 + 3 ^ 40 * 479512 * 2
def baseEnd_479512 : Nat := 72954114251506115791043

theorem tailTrace_479512 : CollatzResearch.WordTrace tailWord_479512 prefixEnd_479512 72954114251506115791043 := by
  unfold tailWord_479512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8744619719408696487392395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11659492959211595316523193 8744619719408696487392395)
  ·
    refine ⟨13116929579113044731088593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8744619719408696487392395 13116929579113044731088593)
    ·
      refine ⟨9837697184334783548316445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13116929579113044731088593 9837697184334783548316445)
      ·
        refine ⟨3689136444125543830618667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9837697184334783548316445 3689136444125543830618667)
        ·
          refine ⟨5533704666188315745928001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689136444125543830618667 5533704666188315745928001)
          ·
            refine ⟨4150278499641236809446001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5533704666188315745928001 4150278499641236809446001)
            ·
              refine ⟨3112708874730927607084501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150278499641236809446001 3112708874730927607084501)
              ·
                refine ⟨72954114251506115791043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3112708874730927607084501 72954114251506115791043)
                ·
                  rfl

theorem cell20_479512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_479512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479512 prefixEnd_479512 := by exact prefixLift 479512
  have htrace : WordTrace (prefixWord ++ tailWord_479512) baseStart_479512 baseEnd_479512 := by
    simpa [prefixWord, tailWord_479512, baseEnd_479512] using wordTrace_append hprefix tailTrace_479512
  have hstable : (prefixWord ++ tailWord_479512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479512).length < 2 ^ (prefixWord ++ tailWord_479512).sum := by decide
  have hdescent : baseEnd_479512 < baseStart_479512 := by decide
  rcases family_descends (prefixWord ++ tailWord_479512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479522 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_479522 : Nat := 118140960795 + 479522 * 2 ^ 59
def prefixEnd_479522 : Nat := 4983230072969 + 3 ^ 40 * 479522 * 2
def baseEnd_479522 : Nat := 218866907027002757039755

theorem tailTrace_479522 : CollatzResearch.WordTrace tailWord_479522 prefixEnd_479522 218866907027002757039755 := by
  unfold tailWord_479522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372401042195291170662205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11659736112520776455099213 4372401042195291170662205)
  ·
    refine ⟨1639650390823234188998327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4372401042195291170662205 1639650390823234188998327)
    ·
      refine ⟨2459475586234851283497491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639650390823234188998327 2459475586234851283497491)
      ·
        refine ⟨3689213379352276925246237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459475586234851283497491 3689213379352276925246237)
        ·
          refine ⟨1383455017257103846967339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3689213379352276925246237 1383455017257103846967339)
          ·
            refine ⟨2075182525885655770451009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383455017257103846967339 2075182525885655770451009)
            ·
              refine ⟨1556386894414241827838257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075182525885655770451009 1556386894414241827838257)
              ·
                refine ⟨1167290170810681370878693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556386894414241827838257 1167290170810681370878693)
                ·
                  refine ⟨218866907027002757039755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167290170810681370878693 218866907027002757039755)
                  ·
                    rfl

theorem cell20_479522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_479522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479522 prefixEnd_479522 := by exact prefixLift 479522
  have htrace : WordTrace (prefixWord ++ tailWord_479522) baseStart_479522 baseEnd_479522 := by
    simpa [prefixWord, tailWord_479522, baseEnd_479522] using wordTrace_append hprefix tailTrace_479522
  have hstable : (prefixWord ++ tailWord_479522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479522).length < 2 ^ (prefixWord ++ tailWord_479522).sum := by decide
  have hdescent : baseEnd_479522 < baseStart_479522 := by decide
  rcases family_descends (prefixWord ++ tailWord_479522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479525 : List Nat := [1, 3, 1, 2, 6, 1, 2, 4]
def baseStart_479525 : Nat := 118140960795 + 479525 * 2 ^ 59
def prefixEnd_479525 : Nat := 4983230072969 + 3 ^ 40 * 479525 * 2
def baseEnd_479525 : Nat := 72956092102916026646581

theorem tailTrace_479525 : CollatzResearch.WordTrace tailWord_479525 prefixEnd_479525 72956092102916026646581 := by
  unfold tailWord_479525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489713587770296195008029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11659809058513530796672019 17489713587770296195008029)
  ·
    refine ⟨6558642595413861073128011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17489713587770296195008029 6558642595413861073128011)
    ·
      refine ⟨9837963893120791609692017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6558642595413861073128011 9837963893120791609692017)
      ·
        refine ⟨7378472919840593707269013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9837963893120791609692017 7378472919840593707269013)
        ·
          refine ⟨345865918117527830028235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7378472919840593707269013 345865918117527830028235)
          ·
            refine ⟨518798877176291745042353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345865918117527830028235 518798877176291745042353)
            ·
              refine ⟨389099157882218808781765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518798877176291745042353 389099157882218808781765)
              ·
                refine ⟨72956092102916026646581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389099157882218808781765 72956092102916026646581)
                ·
                  rfl

theorem cell20_479525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 4].length) (baseStart_479525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479525 prefixEnd_479525 := by exact prefixLift 479525
  have htrace : WordTrace (prefixWord ++ tailWord_479525) baseStart_479525 baseEnd_479525 := by
    simpa [prefixWord, tailWord_479525, baseEnd_479525] using wordTrace_append hprefix tailTrace_479525
  have hstable : (prefixWord ++ tailWord_479525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479525).length < 2 ^ (prefixWord ++ tailWord_479525).sum := by decide
  have hdescent : baseEnd_479525 < baseStart_479525 := by decide
  rcases family_descends (prefixWord ++ tailWord_479525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479556 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_479556 : Nat := 118140960795 + 479556 * 2 ^ 59
def prefixEnd_479556 : Nat := 4983230072969 + 3 ^ 40 * 479556 * 2
def baseEnd_479556 : Nat := 218882425553449749906283

theorem tailTrace_479556 : CollatzResearch.WordTrace tailWord_479556 prefixEnd_479556 218882425553449749906283 := by
  unfold tailWord_479556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745422125328994244693261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11660562833771992326257681 8745422125328994244693261)
  ·
    refine ⟨3279533296998372841759973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8745422125328994244693261 3279533296998372841759973)
    ·
      refine ⟨614912493187194907829995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3279533296998372841759973 614912493187194907829995)
      ·
        refine ⟨922368739780792361744993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614912493187194907829995 922368739780792361744993)
        ·
          refine ⟨691776554835594271308745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922368739780792361744993 691776554835594271308745)
          ·
            refine ⟨518832416126695703481559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691776554835594271308745 518832416126695703481559)
            ·
              refine ⟨778248624190043555222339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518832416126695703481559 778248624190043555222339)
              ·
                refine ⟨1167372936285065332833509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778248624190043555222339 1167372936285065332833509)
                ·
                  refine ⟨218882425553449749906283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1167372936285065332833509 218882425553449749906283)
                  ·
                    rfl

theorem cell20_479556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_479556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479556 prefixEnd_479556 := by exact prefixLift 479556
  have htrace : WordTrace (prefixWord ++ tailWord_479556) baseStart_479556 baseEnd_479556 := by
    simpa [prefixWord, tailWord_479556, baseEnd_479556] using wordTrace_append hprefix tailTrace_479556
  have hstable : (prefixWord ++ tailWord_479556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479556).length < 2 ^ (prefixWord ++ tailWord_479556).sum := by decide
  have hdescent : baseEnd_479556 < baseStart_479556 := by decide
  rcases family_descends (prefixWord ++ tailWord_479556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479560 : List Nat := [2, 1, 3, 1, 1, 2, 2, 6, 2]
def baseStart_479560 : Nat := 118140960795 + 479560 * 2 ^ 59
def prefixEnd_479560 : Nat := 4983230072969 + 3 ^ 40 * 479560 * 2
def baseEnd_479560 : Nat := 218884251262443513772933

theorem tailTrace_479560 : CollatzResearch.WordTrace tailWord_479560 prefixEnd_479560 218884251262443513772933 := by
  unfold tailWord_479560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745495071321748586266067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11660660095095664781688089 8745495071321748586266067)
  ·
    refine ⟨13118242606982622879399101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8745495071321748586266067 13118242606982622879399101)
    ·
      refine ⟨4919340977618483579774663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13118242606982622879399101 4919340977618483579774663)
      ·
        refine ⟨7379011466427725369661995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919340977618483579774663 7379011466427725369661995)
        ·
          refine ⟨11068517199641588054492993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379011466427725369661995 11068517199641588054492993)
          ·
            refine ⟨8301387899731191040869745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11068517199641588054492993 8301387899731191040869745)
            ·
              refine ⟨6226040924798393280652309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8301387899731191040869745 6226040924798393280652309)
              ·
                refine ⟨291845668349924685030577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6226040924798393280652309 291845668349924685030577)
                ·
                  refine ⟨218884251262443513772933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291845668349924685030577 218884251262443513772933)
                  ·
                    rfl

theorem cell20_479560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_479560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479560 prefixEnd_479560 := by exact prefixLift 479560
  have htrace : WordTrace (prefixWord ++ tailWord_479560) baseStart_479560 baseEnd_479560 := by
    simpa [prefixWord, tailWord_479560, baseEnd_479560] using wordTrace_append hprefix tailTrace_479560
  have hstable : (prefixWord ++ tailWord_479560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479560).length < 2 ^ (prefixWord ++ tailWord_479560).sum := by decide
  have hdescent : baseEnd_479560 < baseStart_479560 := by decide
  rcases family_descends (prefixWord ++ tailWord_479560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479588 : List Nat := [2, 3, 1, 1, 3, 1, 1, 8]
def baseStart_479588 : Nat := 118140960795 + 479588 * 2 ^ 59
def prefixEnd_479588 : Nat := 4983230072969 + 3 ^ 40 * 479588 * 2
def baseEnd_479588 : Nat := 72965677075133286946495

theorem tailTrace_479588 : CollatzResearch.WordTrace tailWord_479588 prefixEnd_479588 72965677075133286946495 := by
  unfold tailWord_479588
  simp only [CollatzResearch.WordTrace]
  refine ⟨8746005693271028977275709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11661340924361371969700945 8746005693271028977275709)
  ·
    refine ⟨3279752134976635866478391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8746005693271028977275709 3279752134976635866478391)
    ·
      refine ⟨4919628202464953799717587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279752134976635866478391 4919628202464953799717587)
      ·
        refine ⟨7379442303697430699576381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919628202464953799717587 7379442303697430699576381)
        ·
          refine ⟨2767290863886536512341143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7379442303697430699576381 2767290863886536512341143)
          ·
            refine ⟨4150936295829804768511715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767290863886536512341143 4150936295829804768511715)
            ·
              refine ⟨6226404443744707152767573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150936295829804768511715 6226404443744707152767573)
              ·
                refine ⟨72965677075133286946495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6226404443744707152767573 72965677075133286946495)
                ·
                  rfl

theorem cell20_479588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_479588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479588 prefixEnd_479588 := by exact prefixLift 479588
  have htrace : WordTrace (prefixWord ++ tailWord_479588) baseStart_479588 baseEnd_479588 := by
    simpa [prefixWord, tailWord_479588, baseEnd_479588] using wordTrace_append hprefix tailTrace_479588
  have hstable : (prefixWord ++ tailWord_479588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479588).length < 2 ^ (prefixWord ++ tailWord_479588).sum := by decide
  have hdescent : baseEnd_479588 < baseStart_479588 := by decide
  rcases family_descends (prefixWord ++ tailWord_479588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479618 : List Nat := [3, 4, 2, 1, 3, 1, 1, 5]
def baseStart_479618 : Nat := 118140960795 + 479618 * 2 ^ 59
def prefixEnd_479618 : Nat := 4983230072969 + 3 ^ 40 * 479618 * 2
def baseEnd_479618 : Nat := 72970241347617696613121

theorem tailTrace_479618 : CollatzResearch.WordTrace tailWord_479618 prefixEnd_479618 72970241347617696613121 := by
  unfold tailWord_479618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373276394108343269535877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11662070384288915385429005 4373276394108343269535877)
  ·
    refine ⟨819989323895314363037977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4373276394108343269535877 819989323895314363037977)
    ·
      refine ⟨614991992921485772278483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 819989323895314363037977 614991992921485772278483)
      ·
        refine ⟨922487989382228658417725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614991992921485772278483 922487989382228658417725)
        ·
          refine ⟨345932996018335746906647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922487989382228658417725 345932996018335746906647)
          ·
            refine ⟨518899494027503620359971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345932996018335746906647 518899494027503620359971)
            ·
              refine ⟨778349241041255430539957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518899494027503620359971 778349241041255430539957)
              ·
                refine ⟨72970241347617696613121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778349241041255430539957 72970241347617696613121)
                ·
                  rfl

theorem cell20_479618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_479618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479618 prefixEnd_479618 := by exact prefixLift 479618
  have htrace : WordTrace (prefixWord ++ tailWord_479618) baseStart_479618 baseEnd_479618 := by
    simpa [prefixWord, tailWord_479618, baseEnd_479618] using wordTrace_append hprefix tailTrace_479618
  have hstable : (prefixWord ++ tailWord_479618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479618).length < 2 ^ (prefixWord ++ tailWord_479618).sum := by decide
  have hdescent : baseEnd_479618 < baseStart_479618 := by decide
  rcases family_descends (prefixWord ++ tailWord_479618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479650 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_479650 : Nat := 118140960795 + 479650 * 2 ^ 59
def prefixEnd_479650 : Nat := 4983230072969 + 3 ^ 40 * 479650 * 2
def baseEnd_479650 : Nat := 218925329714803200772565

theorem tailTrace_479650 : CollatzResearch.WordTrace tailWord_479650 prefixEnd_479650 218925329714803200772565 := by
  unfold tailWord_479650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373568178079360635827101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11662848474878295028872269 4373568178079360635827101)
  ·
    refine ⟨1640088066779760238435163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4373568178079360635827101 1640088066779760238435163)
    ·
      refine ⟨2460132100169640357652745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640088066779760238435163 2460132100169640357652745)
      ·
        refine ⟨1845099075127230268239559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2460132100169640357652745 1845099075127230268239559)
        ·
          refine ⟨2767648612690845402359339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845099075127230268239559 2767648612690845402359339)
          ·
            refine ⟨4151472919036268103539009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767648612690845402359339 4151472919036268103539009)
            ·
              refine ⟨3113604689277201077654257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4151472919036268103539009 3113604689277201077654257)
              ·
                refine ⟨2335203516957900808240693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113604689277201077654257 2335203516957900808240693)
                ·
                  refine ⟨218925329714803200772565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2335203516957900808240693 218925329714803200772565)
                  ·
                    rfl

theorem cell20_479650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_479650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479650 prefixEnd_479650 := by exact prefixLift 479650
  have htrace : WordTrace (prefixWord ++ tailWord_479650) baseStart_479650 baseEnd_479650 := by
    simpa [prefixWord, tailWord_479650, baseEnd_479650] using wordTrace_append hprefix tailTrace_479650
  have hstable : (prefixWord ++ tailWord_479650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479650).length < 2 ^ (prefixWord ++ tailWord_479650).sum := by decide
  have hdescent : baseEnd_479650 < baseStart_479650 := by decide
  rcases family_descends (prefixWord ++ tailWord_479650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479698 : List Nat := [3, 2, 2, 4, 1, 1, 1, 6]
def baseStart_479698 : Nat := 118140960795 + 479698 * 2 ^ 59
def prefixEnd_479698 : Nat := 4983230072969 + 3 ^ 40 * 479698 * 2
def baseEnd_479698 : Nat := 72982412740909455724123

theorem tailTrace_479698 : CollatzResearch.WordTrace tailWord_479698 prefixEnd_479698 72982412740909455724123 := by
  unfold tailWord_479698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374005854035886685263937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11664015610762364494037165 4374005854035886685263937)
  ·
    refine ⟨3280504390526915013947953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4374005854035886685263937 3280504390526915013947953)
    ·
      refine ⟨2460378292895186260460965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3280504390526915013947953 2460378292895186260460965)
      ·
        refine ⟨461320929917847423836431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2460378292895186260460965 461320929917847423836431)
        ·
          refine ⟨691981394876771135754647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461320929917847423836431 691981394876771135754647)
          ·
            refine ⟨1037972092315156703631971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691981394876771135754647 1037972092315156703631971)
            ·
              refine ⟨1556958138472735055447957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037972092315156703631971 1556958138472735055447957)
              ·
                refine ⟨72982412740909455724123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1556958138472735055447957 72982412740909455724123)
                ·
                  rfl

theorem cell20_479698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_479698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479698 prefixEnd_479698 := by exact prefixLift 479698
  have htrace : WordTrace (prefixWord ++ tailWord_479698) baseStart_479698 baseEnd_479698 := by
    simpa [prefixWord, tailWord_479698, baseEnd_479698] using wordTrace_append hprefix tailTrace_479698
  have hstable : (prefixWord ++ tailWord_479698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479698).length < 2 ^ (prefixWord ++ tailWord_479698).sum := by decide
  have hdescent : baseEnd_479698 < baseStart_479698 := by decide
  rcases family_descends (prefixWord ++ tailWord_479698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479726 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_479726 : Nat := 118140960795 + 479726 * 2 ^ 59
def prefixEnd_479726 : Nat := 4983230072969 + 3 ^ 40 * 479726 * 2
def baseEnd_479726 : Nat := 218960018185684714238921

theorem tailTrace_479726 : CollatzResearch.WordTrace tailWord_479726 prefixEnd_479726 218960018185684714238921 := by
  unfold tailWord_479726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187130582505263440384379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11664696440028071682050021 2187130582505263440384379)
  ·
    refine ⟨3280695873757895160576569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2187130582505263440384379 3280695873757895160576569)
    ·
      refine ⟨2460521905318421370432427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3280695873757895160576569 2460521905318421370432427)
      ·
        refine ⟨3690782857977632055648641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460521905318421370432427 3690782857977632055648641)
        ·
          refine ⟨2768087143483224041736481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3690782857977632055648641 2768087143483224041736481)
          ·
            refine ⟨2076065357612418031302361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768087143483224041736481 2076065357612418031302361)
            ·
              refine ⟨1557049018209313523476771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076065357612418031302361 1557049018209313523476771)
              ·
                refine ⟨2335573527313970285215157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557049018209313523476771 2335573527313970285215157)
                ·
                  refine ⟨218960018185684714238921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2335573527313970285215157 218960018185684714238921)
                  ·
                    rfl

theorem cell20_479726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_479726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479726 prefixEnd_479726 := by exact prefixLift 479726
  have htrace : WordTrace (prefixWord ++ tailWord_479726) baseStart_479726 baseEnd_479726 := by
    simpa [prefixWord, tailWord_479726, baseEnd_479726] using wordTrace_append hprefix tailTrace_479726
  have hstable : (prefixWord ++ tailWord_479726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479726).length < 2 ^ (prefixWord ++ tailWord_479726).sum := by decide
  have hdescent : baseEnd_479726 < baseStart_479726 := by decide
  rcases family_descends (prefixWord ++ tailWord_479726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479729 : List Nat := [1, 2, 2, 2, 3, 1, 5, 2, 2]
def baseStart_479729 : Nat := 118140960795 + 479729 * 2 ^ 59
def prefixEnd_479729 : Nat := 4983230072969 + 3 ^ 40 * 479729 * 2
def baseEnd_479729 : Nat := 218961387467430037138909

theorem tailTrace_479729 : CollatzResearch.WordTrace tailWord_479729 prefixEnd_479729 218961387467430037138909 := by
  unfold tailWord_479729
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497154079031239035434241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11664769386020826023622827 17497154079031239035434241)
  ·
    refine ⟨13122865559273429276575681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17497154079031239035434241 13122865559273429276575681)
    ·
      refine ⟨9842149169455071957431761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13122865559273429276575681 9842149169455071957431761)
      ·
        refine ⟨7381611877091303968073821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9842149169455071957431761 7381611877091303968073821)
        ·
          refine ⟨2768104453909238988027683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7381611877091303968073821 2768104453909238988027683)
          ·
            refine ⟨4152156680863858482041525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768104453909238988027683 4152156680863858482041525)
            ·
              refine ⟨389264688830986732691393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4152156680863858482041525 389264688830986732691393)
              ·
                refine ⟨291948516623240049518545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389264688830986732691393 291948516623240049518545)
                ·
                  refine ⟨218961387467430037138909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291948516623240049518545 218961387467430037138909)
                  ·
                    rfl

theorem cell20_479729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_479729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479729 prefixEnd_479729 := by exact prefixLift 479729
  have htrace : WordTrace (prefixWord ++ tailWord_479729) baseStart_479729 baseEnd_479729 := by
    simpa [prefixWord, tailWord_479729, baseEnd_479729] using wordTrace_append hprefix tailTrace_479729
  have hstable : (prefixWord ++ tailWord_479729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479729).length < 2 ^ (prefixWord ++ tailWord_479729).sum := by decide
  have hdescent : baseEnd_479729 < baseStart_479729 := by decide
  rcases family_descends (prefixWord ++ tailWord_479729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479780 : List Nat := [2, 3, 1, 5, 2, 1, 2, 2, 2]
def baseStart_479780 : Nat := 118140960795 + 479780 * 2 ^ 59
def prefixEnd_479780 : Nat := 4983230072969 + 3 ^ 40 * 479780 * 2
def baseEnd_479780 : Nat := 218984665257100526438701

theorem tailTrace_479780 : CollatzResearch.WordTrace tailWord_479780 prefixEnd_479780 218984665257100526438701 := by
  unfold tailWord_479780
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749507100923237372770397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11666009467897649830360529 8749507100923237372770397)
  ·
    refine ⟨3281065162846214014788899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8749507100923237372770397 3281065162846214014788899)
    ·
      refine ⟨4921597744269321022183349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281065162846214014788899 4921597744269321022183349)
      ·
        refine ⟨461399788525248845829689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4921597744269321022183349 461399788525248845829689)
        ·
          refine ⟨346049841393936634372267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461399788525248845829689 346049841393936634372267)
          ·
            refine ⟨519074762090904951558401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346049841393936634372267 519074762090904951558401)
            ·
              refine ⟨389306071568178713668801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519074762090904951558401 389306071568178713668801)
              ·
                refine ⟨291979553676134035251601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389306071568178713668801 291979553676134035251601)
                ·
                  refine ⟨218984665257100526438701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291979553676134035251601 218984665257100526438701)
                  ·
                    rfl

theorem cell20_479780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_479780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479780 prefixEnd_479780 := by exact prefixLift 479780
  have htrace : WordTrace (prefixWord ++ tailWord_479780) baseStart_479780 baseEnd_479780 := by
    simpa [prefixWord, tailWord_479780, baseEnd_479780] using wordTrace_append hprefix tailTrace_479780
  have hstable : (prefixWord ++ tailWord_479780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479780).length < 2 ^ (prefixWord ++ tailWord_479780).sum := by decide
  have hdescent : baseEnd_479780 < baseStart_479780 := by decide
  rcases family_descends (prefixWord ++ tailWord_479780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479784 : List Nat := [2, 1, 5, 2, 1, 1, 4, 2, 2]
def baseStart_479784 : Nat := 118140960795 + 479784 * 2 ^ 59
def prefixEnd_479784 : Nat := 4983230072969 + 3 ^ 40 * 479784 * 2
def baseEnd_479784 : Nat := 218986490966094290305351

theorem tailTrace_479784 : CollatzResearch.WordTrace tailWord_479784 prefixEnd_479784 218986490966094290305351 := by
  unfold tailWord_479784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749580046915991714343203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11666106729221322285790937 8749580046915991714343203)
  ·
    refine ⟨13124370070373987571514805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8749580046915991714343203 13124370070373987571514805)
    ·
      refine ⟨1230409694097561334829513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13124370070373987571514805 1230409694097561334829513)
      ·
        refine ⟨922807270573171001122135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1230409694097561334829513 922807270573171001122135)
        ·
          refine ⟨1384210905859756501683203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922807270573171001122135 1384210905859756501683203)
          ·
            refine ⟨2076316358789634752524805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384210905859756501683203 2076316358789634752524805)
            ·
              refine ⟨389309317273056516098401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2076316358789634752524805 389309317273056516098401)
              ·
                refine ⟨291981987954792387073801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389309317273056516098401 291981987954792387073801)
                ·
                  refine ⟨218986490966094290305351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291981987954792387073801 218986490966094290305351)
                  ·
                    rfl

theorem cell20_479784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_479784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479784 prefixEnd_479784 := by exact prefixLift 479784
  have htrace : WordTrace (prefixWord ++ tailWord_479784) baseStart_479784 baseEnd_479784 := by
    simpa [prefixWord, tailWord_479784, baseEnd_479784] using wordTrace_append hprefix tailTrace_479784
  have hstable : (prefixWord ++ tailWord_479784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479784).length < 2 ^ (prefixWord ++ tailWord_479784).sum := by decide
  have hdescent : baseEnd_479784 < baseStart_479784 := by decide
  rcases family_descends (prefixWord ++ tailWord_479784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479802 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_479802 : Nat := 118140960795 + 479802 * 2 ^ 59
def prefixEnd_479802 : Nat := 4983230072969 + 3 ^ 40 * 479802 * 2
def baseEnd_479802 : Nat := 218994706656566227705277

theorem tailTrace_479802 : CollatzResearch.WordTrace tailWord_479802 prefixEnd_479802 218994706656566227705277 := by
  unfold tailWord_479802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374954151941693125710415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11666544405177848335227773 4374954151941693125710415)
  ·
    refine ⟨6562431227912539688565623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4374954151941693125710415 6562431227912539688565623)
    ·
      refine ⟨9843646841868809532848435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6562431227912539688565623 9843646841868809532848435)
      ·
        refine ⟨14765470262803214299272653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9843646841868809532848435 14765470262803214299272653)
        ·
          refine ⟨5537051348551205362227245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14765470262803214299272653 5537051348551205362227245)
          ·
            refine ⟨2076394255706702010835217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5537051348551205362227245 2076394255706702010835217)
            ·
              refine ⟨1557295691780026508126413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076394255706702010835217 1557295691780026508126413)
              ·
                refine ⟨583985884417509940547405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1557295691780026508126413 583985884417509940547405)
                ·
                  refine ⟨218994706656566227705277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583985884417509940547405 218994706656566227705277)
                  ·
                    rfl

theorem cell20_479802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_479802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479802 prefixEnd_479802 := by exact prefixLift 479802
  have htrace : WordTrace (prefixWord ++ tailWord_479802) baseStart_479802 baseEnd_479802 := by
    simpa [prefixWord, tailWord_479802, baseEnd_479802] using wordTrace_append hprefix tailTrace_479802
  have hstable : (prefixWord ++ tailWord_479802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479802).length < 2 ^ (prefixWord ++ tailWord_479802).sum := by decide
  have hdescent : baseEnd_479802 < baseStart_479802 := by decide
  rcases family_descends (prefixWord ++ tailWord_479802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479809 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_479809 : Nat := 118140960795 + 479809 * 2 ^ 59
def prefixEnd_479809 : Nat := 4983230072969 + 3 ^ 40 * 479809 * 2
def baseEnd_479809 : Nat := 218997901647305314471915

theorem tailTrace_479809 : CollatzResearch.WordTrace tailWord_479809 prefixEnd_479809 218997901647305314471915 := by
  unfold tailWord_479809
  simp only [CollatzResearch.WordTrace]
  refine ⟨17500071918741412698346481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11666714612494275132230987 17500071918741412698346481)
  ·
    refine ⟨13125053939056059523759861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17500071918741412698346481 13125053939056059523759861)
    ·
      refine ⟨1230473806786505580352487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13125053939056059523759861 1230473806786505580352487)
      ·
        refine ⟨1845710710179758370528731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230473806786505580352487 1845710710179758370528731)
        ·
          refine ⟨2768566065269637555793097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845710710179758370528731 2768566065269637555793097)
          ·
            refine ⟨2076424548952228166844823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768566065269637555793097 2076424548952228166844823)
            ·
              refine ⟨3114636823428342250267235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076424548952228166844823 3114636823428342250267235)
              ·
                refine ⟨4671955235142513375400853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114636823428342250267235 4671955235142513375400853)
                ·
                  refine ⟨218997901647305314471915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4671955235142513375400853 218997901647305314471915)
                  ·
                    rfl

theorem cell20_479809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_479809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479809 prefixEnd_479809 := by exact prefixLift 479809
  have htrace : WordTrace (prefixWord ++ tailWord_479809) baseStart_479809 baseEnd_479809 := by
    simpa [prefixWord, tailWord_479809, baseEnd_479809] using wordTrace_append hprefix tailTrace_479809
  have hstable : (prefixWord ++ tailWord_479809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479809).length < 2 ^ (prefixWord ++ tailWord_479809).sum := by decide
  have hdescent : baseEnd_479809 < baseStart_479809 := by decide
  rcases family_descends (prefixWord ++ tailWord_479809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479836 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_479836 : Nat := 118140960795 + 479836 * 2 ^ 59
def prefixEnd_479836 : Nat := 4983230072969 + 3 ^ 40 * 479836 * 2
def baseEnd_479836 : Nat := 219010225183013220571805

theorem tailTrace_479836 : CollatzResearch.WordTrace tailWord_479836 prefixEnd_479836 219010225183013220571805 := by
  unfold tailWord_479836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750528344821798154789681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11667371126429064206386241 8750528344821798154789681)
  ·
    refine ⟨6562896258616348616092261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8750528344821798154789681 6562896258616348616092261)
    ·
      refine ⟨1230543048490565365517299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6562896258616348616092261 1230543048490565365517299)
      ·
        refine ⟨1845814572735848048275949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230543048490565365517299 1845814572735848048275949)
        ·
          refine ⟨692180464775943018103481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1845814572735848048275949 692180464775943018103481)
          ·
            refine ⟨519135348581957263577611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692180464775943018103481 519135348581957263577611)
            ·
              refine ⟨778703022872935895366417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519135348581957263577611 778703022872935895366417)
              ·
                refine ⟨584027267154701921524813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778703022872935895366417 584027267154701921524813)
                ·
                  refine ⟨219010225183013220571805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584027267154701921524813 219010225183013220571805)
                  ·
                    rfl

theorem cell20_479836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_479836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479836 prefixEnd_479836 := by exact prefixLift 479836
  have htrace : WordTrace (prefixWord ++ tailWord_479836) baseStart_479836 baseEnd_479836 := by
    simpa [prefixWord, tailWord_479836, baseEnd_479836] using wordTrace_append hprefix tailTrace_479836
  have hstable : (prefixWord ++ tailWord_479836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479836).length < 2 ^ (prefixWord ++ tailWord_479836).sum := by decide
  have hdescent : baseEnd_479836 < baseStart_479836 := by decide
  rcases family_descends (prefixWord ++ tailWord_479836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479840 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_479840 : Nat := 118140960795 + 479840 * 2 ^ 59
def prefixEnd_479840 : Nat := 4983230072969 + 3 ^ 40 * 479840 * 2
def baseEnd_479840 : Nat := 219012050892006984438455

theorem tailTrace_479840 : CollatzResearch.WordTrace tailWord_479840 prefixEnd_479840 219012050892006984438455 := by
  unfold tailWord_479840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750601290814552496362487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11667468387752736661816649 8750601290814552496362487)
  ·
    refine ⟨13125901936221828744543731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8750601290814552496362487 13125901936221828744543731)
    ·
      refine ⟨19688852904332743116815597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13125901936221828744543731 19688852904332743116815597)
      ·
        refine ⟨7383319839124778668805849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19688852904332743116815597 7383319839124778668805849)
        ·
          refine ⟨5537489879343584001604387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7383319839124778668805849 5537489879343584001604387)
          ·
            refine ⟨8306234819015376002406581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537489879343584001604387 8306234819015376002406581)
            ·
              refine ⟨778709514282691500225617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8306234819015376002406581 778709514282691500225617)
              ·
                refine ⟨584032135712018625169213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778709514282691500225617 584032135712018625169213)
                ·
                  refine ⟨219012050892006984438455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584032135712018625169213 219012050892006984438455)
                  ·
                    rfl

theorem cell20_479840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_479840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479840 prefixEnd_479840 := by exact prefixLift 479840
  have htrace : WordTrace (prefixWord ++ tailWord_479840) baseStart_479840 baseEnd_479840 := by
    simpa [prefixWord, tailWord_479840, baseEnd_479840] using wordTrace_append hprefix tailTrace_479840
  have hstable : (prefixWord ++ tailWord_479840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479840).length < 2 ^ (prefixWord ++ tailWord_479840).sum := by decide
  have hdescent : baseEnd_479840 < baseStart_479840 := by decide
  rcases family_descends (prefixWord ++ tailWord_479840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479898 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_479898 : Nat := 118140960795 + 479898 * 2 ^ 59
def prefixEnd_479898 : Nat := 4983230072969 + 3 ^ 40 * 479898 * 2
def baseEnd_479898 : Nat := 219038523672416560504885

theorem tailTrace_479898 : CollatzResearch.WordTrace tailWord_479898 prefixEnd_479898 219038523672416560504885 := by
  unfold tailWord_479898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375829503854745224584087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11668878676945987265557565 4375829503854745224584087)
  ·
    refine ⟨6563744255782117836876131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4375829503854745224584087 6563744255782117836876131)
    ·
      refine ⟨9845616383673176755314197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6563744255782117836876131 9845616383673176755314197)
      ·
        refine ⟨461513267984680160405353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9845616383673176755314197 461513267984680160405353)
        ·
          refine ⟨346134950988510120304015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461513267984680160405353 346134950988510120304015)
          ·
            refine ⟨519202426482765180456023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346134950988510120304015 519202426482765180456023)
            ·
              refine ⟨778803639724147770684035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519202426482765180456023 778803639724147770684035)
              ·
                refine ⟨1168205459586221656026053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778803639724147770684035 1168205459586221656026053)
                ·
                  refine ⟨219038523672416560504885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168205459586221656026053 219038523672416560504885)
                  ·
                    rfl

theorem cell20_479898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_479898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479898 prefixEnd_479898 := by exact prefixLift 479898
  have htrace : WordTrace (prefixWord ++ tailWord_479898) baseStart_479898 baseEnd_479898 := by
    simpa [prefixWord, tailWord_479898, baseEnd_479898] using wordTrace_append hprefix tailTrace_479898
  have hstable : (prefixWord ++ tailWord_479898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479898).length < 2 ^ (prefixWord ++ tailWord_479898).sum := by decide
  have hdescent : baseEnd_479898 < baseStart_479898 := by decide
  rcases family_descends (prefixWord ++ tailWord_479898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479913 : List Nat := [1, 2, 1, 1, 1, 1, 2, 11]
def baseStart_479913 : Nat := 118140960795 + 479913 * 2 ^ 59
def prefixEnd_479913 : Nat := 4983230072969 + 3 ^ 40 * 479913 * 2
def baseEnd_479913 : Nat := 73015123360381058334941

theorem tailTrace_479913 : CollatzResearch.WordTrace tailWord_479913 prefixEnd_479913 73015123360381058334941 := by
  unfold tailWord_479913
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503865110364638460132393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11669243406909758973421595 17503865110364638460132393)
  ·
    refine ⟨13127898832773478845099295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17503865110364638460132393 13127898832773478845099295)
    ·
      refine ⟨19691848249160218267648943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13127898832773478845099295 19691848249160218267648943)
      ·
        refine ⟨29537772373740327401473415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19691848249160218267648943 29537772373740327401473415)
        ·
          refine ⟨44306658560610491102210123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29537772373740327401473415 44306658560610491102210123)
          ·
            refine ⟨66459987840915736653315185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44306658560610491102210123 66459987840915736653315185)
            ·
              refine ⟨49844990880686802489986389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66459987840915736653315185 49844990880686802489986389)
              ·
                refine ⟨73015123360381058334941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 49844990880686802489986389 73015123360381058334941)
                ·
                  rfl

theorem cell20_479913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_479913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479913 prefixEnd_479913 := by exact prefixLift 479913
  have htrace : WordTrace (prefixWord ++ tailWord_479913) baseStart_479913 baseEnd_479913 := by
    simpa [prefixWord, tailWord_479913, baseEnd_479913] using wordTrace_append hprefix tailTrace_479913
  have hstable : (prefixWord ++ tailWord_479913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479913).length < 2 ^ (prefixWord ++ tailWord_479913).sum := by decide
  have hdescent : baseEnd_479913 < baseStart_479913 := by decide
  rcases family_descends (prefixWord ++ tailWord_479913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479964 : List Nat := [2, 2, 5, 1, 1, 3, 1, 5]
def baseStart_479964 : Nat := 118140960795 + 479964 * 2 ^ 59
def prefixEnd_479964 : Nat := 4983230072969 + 3 ^ 40 * 479964 * 2
def baseEnd_479964 : Nat := 73022882623604554768205

theorem tailTrace_479964 : CollatzResearch.WordTrace tailWord_479964 prefixEnd_479964 73022882623604554768205 := by
  unfold tailWord_479964
  simp only [CollatzResearch.WordTrace]
  refine ⟨8752862616589937085119473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11670483488786582780159297 8752862616589937085119473)
  ·
    refine ⟨6564646962442452813839605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8752862616589937085119473 6564646962442452813839605)
    ·
      refine ⟨615435652728979951297463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6564646962442452813839605 615435652728979951297463)
      ·
        refine ⟨923153479093469926946195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615435652728979951297463 923153479093469926946195)
        ·
          refine ⟨1384730218640204890419293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923153479093469926946195 1384730218640204890419293)
          ·
            refine ⟨519273831990076833907235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1384730218640204890419293 519273831990076833907235)
            ·
              refine ⟨778910747985115250860853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519273831990076833907235 778910747985115250860853)
              ·
                refine ⟨73022882623604554768205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778910747985115250860853 73022882623604554768205)
                ·
                  rfl

theorem cell20_479964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_479964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_479964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_479964 prefixEnd_479964 := by exact prefixLift 479964
  have htrace : WordTrace (prefixWord ++ tailWord_479964) baseStart_479964 baseEnd_479964 := by
    simpa [prefixWord, tailWord_479964, baseEnd_479964] using wordTrace_append hprefix tailTrace_479964
  have hstable : (prefixWord ++ tailWord_479964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479964).length < 2 ^ (prefixWord ++ tailWord_479964).sum := by decide
  have hdescent : baseEnd_479964 < baseStart_479964 := by decide
  rcases family_descends (prefixWord ++ tailWord_479964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480051 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_480051 : Nat := 118140960795 + 480051 * 2 ^ 59
def prefixEnd_480051 : Nat := 4983230072969 + 3 ^ 40 * 480051 * 2
def baseEnd_480051 : Nat := 219108357041428028404259

theorem tailTrace_480051 : CollatzResearch.WordTrace tailWord_480051 prefixEnd_480051 219108357041428028404259 := by
  unfold tailWord_480051
  simp only [CollatzResearch.WordTrace]
  refine ⟨17508898383864688028656007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11672598922576458685770671 17508898383864688028656007)
  ·
    refine ⟨26263347575797032042984011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17508898383864688028656007 26263347575797032042984011)
    ·
      refine ⟨39395021363695548064476017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26263347575797032042984011 39395021363695548064476017)
      ·
        refine ⟨29546266022771661048357013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39395021363695548064476017 29546266022771661048357013)
        ·
          refine ⟨1384981219817421611641735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29546266022771661048357013 1384981219817421611641735)
          ·
            refine ⟨2077471829726132417462603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384981219817421611641735 2077471829726132417462603)
            ·
              refine ⟨3116207744589198626193905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077471829726132417462603 3116207744589198626193905)
              ·
                refine ⟨2337155808441898969645429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3116207744589198626193905 2337155808441898969645429)
                ·
                  refine ⟨219108357041428028404259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2337155808441898969645429 219108357041428028404259)
                  ·
                    rfl

theorem cell20_480051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_480051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480051 prefixEnd_480051 := by exact prefixLift 480051
  have htrace : WordTrace (prefixWord ++ tailWord_480051) baseStart_480051 baseEnd_480051 := by
    simpa [prefixWord, tailWord_480051, baseEnd_480051] using wordTrace_append hprefix tailTrace_480051
  have hstable : (prefixWord ++ tailWord_480051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480051).length < 2 ^ (prefixWord ++ tailWord_480051).sum := by decide
  have hdescent : baseEnd_480051 < baseStart_480051 := by decide
  rcases family_descends (prefixWord ++ tailWord_480051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480061 : List Nat := [1, 4, 1, 4, 2, 2, 6]
def baseStart_480061 : Nat := 118140960795 + 480061 * 2 ^ 59
def prefixEnd_480061 : Nat := 4983230072969 + 3 ^ 40 * 480061 * 2
def baseEnd_480061 : Nat := 24345880145990270896765

theorem tailTrace_480061 : CollatzResearch.WordTrace tailWord_480061 prefixEnd_480061 24345880145990270896765 := by
  unfold tailWord_480061
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509263113828459736520037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11672842075885639824346691 17509263113828459736520037)
  ·
    refine ⟨3282986833842836200597507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17509263113828459736520037 3282986833842836200597507)
    ·
      refine ⟨4924480250764254300896261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3282986833842836200597507 4924480250764254300896261)
      ·
        refine ⟨923340047018297681418049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4924480250764254300896261 923340047018297681418049)
        ·
          refine ⟨692505035263723261063537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923340047018297681418049 692505035263723261063537)
          ·
            refine ⟨519378776447792445797653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692505035263723261063537 519378776447792445797653)
            ·
              refine ⟨24345880145990270896765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 519378776447792445797653 24345880145990270896765)
              ·
                rfl

theorem cell20_480061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 6].length) (baseStart_480061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480061 prefixEnd_480061 := by exact prefixLift 480061
  have htrace : WordTrace (prefixWord ++ tailWord_480061) baseStart_480061 baseEnd_480061 := by
    simpa [prefixWord, tailWord_480061, baseEnd_480061] using wordTrace_append hprefix tailTrace_480061
  have hstable : (prefixWord ++ tailWord_480061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480061).length < 2 ^ (prefixWord ++ tailWord_480061).sum := by decide
  have hdescent : baseEnd_480061 < baseStart_480061 := by decide
  rcases family_descends (prefixWord ++ tailWord_480061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480082 : List Nat := [3, 2, 2, 1, 1, 2, 4, 5]
def baseStart_480082 : Nat := 118140960795 + 480082 * 2 ^ 59
def prefixEnd_480082 : Nat := 4983230072969 + 3 ^ 40 * 480082 * 2
def baseEnd_480082 : Nat := 73040835428709899456933

theorem tailTrace_480082 : CollatzResearch.WordTrace tailWord_480082 prefixEnd_480082 73040835428709899456933 := by
  unfold tailWord_480082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377507261688095080758625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11673352697834920215356333 4377507261688095080758625)
  ·
    refine ⟨3283130446266071310568969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4377507261688095080758625 3283130446266071310568969)
    ·
      refine ⟨2462347834699553482926727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3283130446266071310568969 2462347834699553482926727)
      ·
        refine ⟨3693521752049330224390091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462347834699553482926727 3693521752049330224390091)
        ·
          refine ⟨5540282628073995336585137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693521752049330224390091 5540282628073995336585137)
          ·
            refine ⟨4155211971055496502438853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5540282628073995336585137 4155211971055496502438853)
            ·
              refine ⟨779102244572905594207285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4155211971055496502438853 779102244572905594207285)
              ·
                refine ⟨73040835428709899456933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 779102244572905594207285 73040835428709899456933)
                ·
                  rfl

theorem cell20_480082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_480082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480082 prefixEnd_480082 := by exact prefixLift 480082
  have htrace : WordTrace (prefixWord ++ tailWord_480082) baseStart_480082 baseEnd_480082 := by
    simpa [prefixWord, tailWord_480082, baseEnd_480082] using wordTrace_append hprefix tailTrace_480082
  have hstable : (prefixWord ++ tailWord_480082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480082).length < 2 ^ (prefixWord ++ tailWord_480082).sum := by decide
  have hdescent : baseEnd_480082 < baseStart_480082 := by decide
  rcases family_descends (prefixWord ++ tailWord_480082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480096 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_480096 : Nat := 118140960795 + 480096 * 2 ^ 59
def prefixEnd_480096 : Nat := 4983230072969 + 3 ^ 40 * 480096 * 2
def baseEnd_480096 : Nat := 219128896267607871904075

theorem tailTrace_480096 : CollatzResearch.WordTrace tailWord_480096 prefixEnd_480096 219128896267607871904075 := by
  unfold tailWord_480096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755269834350830357022071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11673693112467773809362761 8755269834350830357022071)
  ·
    refine ⟨13132904751526245535533107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8755269834350830357022071 13132904751526245535533107)
    ·
      refine ⟨19699357127289368303299661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13132904751526245535533107 19699357127289368303299661)
      ·
        refine ⟨7387258922733513113737373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19699357127289368303299661 7387258922733513113737373)
        ·
          refine ⟨2770222096025067417651515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7387258922733513113737373 2770222096025067417651515)
          ·
            refine ⟨4155333144037601126477273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770222096025067417651515 4155333144037601126477273)
            ·
              refine ⟨3116499858028200844857955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4155333144037601126477273 3116499858028200844857955)
              ·
                refine ⟨4674749787042301267286933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116499858028200844857955 4674749787042301267286933)
                ·
                  refine ⟨219128896267607871904075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4674749787042301267286933 219128896267607871904075)
                  ·
                    rfl

theorem cell20_480096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_480096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480096 prefixEnd_480096 := by exact prefixLift 480096
  have htrace : WordTrace (prefixWord ++ tailWord_480096) baseStart_480096 baseEnd_480096 := by
    simpa [prefixWord, tailWord_480096, baseEnd_480096] using wordTrace_append hprefix tailTrace_480096
  have hstable : (prefixWord ++ tailWord_480096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480096).length < 2 ^ (prefixWord ++ tailWord_480096).sum := by decide
  have hdescent : baseEnd_480096 < baseStart_480096 := by decide
  rcases family_descends (prefixWord ++ tailWord_480096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480126 : List Nat := [4, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_480126 : Nat := 118140960795 + 480126 * 2 ^ 59
def prefixEnd_480126 : Nat := 4983230072969 + 3 ^ 40 * 480126 * 2
def baseEnd_480126 : Nat := 219142589085061100903953

theorem tailTrace_480126 : CollatzResearch.WordTrace tailWord_480126 prefixEnd_480126 219142589085061100903953 := by
  unfold tailWord_480126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188954232324121979704529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11674422572395317225090821 2188954232324121979704529)
  ·
    refine ⟨1641715674243091484778397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2188954232324121979704529 1641715674243091484778397)
    ·
      refine ⟨615643377841159306791899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1641715674243091484778397 615643377841159306791899)
      ·
        refine ⟨923465066761738960187849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615643377841159306791899 923465066761738960187849)
        ·
          refine ⟨692598800071304220140887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923465066761738960187849 692598800071304220140887)
          ·
            refine ⟨1038898200106956330211331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692598800071304220140887 1038898200106956330211331)
            ·
              refine ⟨1558347300160434495316997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038898200106956330211331 1558347300160434495316997)
              ·
                refine ⟨292190118780081467871937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1558347300160434495316997 292190118780081467871937)
                ·
                  refine ⟨219142589085061100903953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292190118780081467871937 219142589085061100903953)
                  ·
                    rfl

theorem cell20_480126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_480126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480126 prefixEnd_480126 := by exact prefixLift 480126
  have htrace : WordTrace (prefixWord ++ tailWord_480126) baseStart_480126 baseEnd_480126 := by
    simpa [prefixWord, tailWord_480126, baseEnd_480126] using wordTrace_append hprefix tailTrace_480126
  have hstable : (prefixWord ++ tailWord_480126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480126).length < 2 ^ (prefixWord ++ tailWord_480126).sum := by decide
  have hdescent : baseEnd_480126 < baseStart_480126 := by decide
  rcases family_descends (prefixWord ++ tailWord_480126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480127 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 3]
def baseStart_480127 : Nat := 118140960795 + 480127 * 2 ^ 59
def prefixEnd_480127 : Nat := 4983230072969 + 3 ^ 40 * 480127 * 2
def baseEnd_480127 : Nat := 219143045512309541870615

theorem tailTrace_480127 : CollatzResearch.WordTrace tailWord_480127 prefixEnd_480127 219143045512309541870615 := by
  unfold tailWord_480127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17511670331589353008422635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11674446887726235338948423 17511670331589353008422635)
  ·
    refine ⟨26267505497384029512633953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17511670331589353008422635 26267505497384029512633953)
    ·
      refine ⟨19700629123038022134475465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26267505497384029512633953 19700629123038022134475465)
      ·
        refine ⟨14775471842278516600856599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19700629123038022134475465 14775471842278516600856599)
        ·
          refine ⟨22163207763417774901284899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14775471842278516600856599 22163207763417774901284899)
          ·
            refine ⟨33244811645126662351927349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22163207763417774901284899 33244811645126662351927349)
            ·
              refine ⟨3116701091730624595493189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33244811645126662351927349 3116701091730624595493189)
              ·
                refine ⟨584381454699492111654973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3116701091730624595493189 584381454699492111654973)
                ·
                  refine ⟨219143045512309541870615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584381454699492111654973 219143045512309541870615)
                  ·
                    rfl

theorem cell20_480127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_480127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480127 prefixEnd_480127 := by exact prefixLift 480127
  have htrace : WordTrace (prefixWord ++ tailWord_480127) baseStart_480127 baseEnd_480127 := by
    simpa [prefixWord, tailWord_480127, baseEnd_480127] using wordTrace_append hprefix tailTrace_480127
  have hstable : (prefixWord ++ tailWord_480127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480127).length < 2 ^ (prefixWord ++ tailWord_480127).sum := by decide
  have hdescent : baseEnd_480127 < baseStart_480127 := by decide
  rcases family_descends (prefixWord ++ tailWord_480127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480205 : List Nat := [1, 6, 3, 1, 2, 1, 2, 4]
def baseStart_480205 : Nat := 118140960795 + 480205 * 2 ^ 59
def prefixEnd_480205 : Nat := 4983230072969 + 3 ^ 40 * 480205 * 2
def baseEnd_480205 : Nat := 73059548945895979090099

theorem tailTrace_480205 : CollatzResearch.WordTrace tailWord_480205 prefixEnd_480205 73059548945895979090099 := by
  unfold tailWord_480205
  simp only [CollatzResearch.WordTrace]
  refine ⟨17514515225306772329762069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11676343483537848219841379 17514515225306772329762069)
  ·
    refine ⟨820992901186254952957597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17514515225306772329762069 820992901186254952957597)
    ·
      refine ⟨307872337944845607359099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 820992901186254952957597 307872337944845607359099)
      ·
        refine ⟨461808506917268411038649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307872337944845607359099 461808506917268411038649)
        ·
          refine ⟨346356380187951308278987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461808506917268411038649 346356380187951308278987)
          ·
            refine ⟨519534570281926962418481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346356380187951308278987 519534570281926962418481)
            ·
              refine ⟨389650927711445221813861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519534570281926962418481 389650927711445221813861)
              ·
                refine ⟨73059548945895979090099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389650927711445221813861 73059548945895979090099)
                ·
                  rfl

theorem cell20_480205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4].length) (baseStart_480205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480205 prefixEnd_480205 := by exact prefixLift 480205
  have htrace : WordTrace (prefixWord ++ tailWord_480205) baseStart_480205 baseEnd_480205 := by
    simpa [prefixWord, tailWord_480205, baseEnd_480205] using wordTrace_append hprefix tailTrace_480205
  have hstable : (prefixWord ++ tailWord_480205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480205).length < 2 ^ (prefixWord ++ tailWord_480205).sum := by decide
  have hdescent : baseEnd_480205 < baseStart_480205 := by decide
  rcases family_descends (prefixWord ++ tailWord_480205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480223 : List Nat := [1, 1, 2, 3, 5, 2, 1, 3, 2]
def baseStart_480223 : Nat := 118140960795 + 480223 * 2 ^ 59
def prefixEnd_480223 : Nat := 4983230072969 + 3 ^ 40 * 480223 * 2
def baseEnd_480223 : Nat := 219186862528159874670223

theorem tailTrace_480223 : CollatzResearch.WordTrace tailWord_480223 prefixEnd_480223 219186862528159874670223 := by
  unfold tailWord_480223
  simp only [CollatzResearch.WordTrace]
  refine ⟨17515171739241561403917323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11676781159494374269278215 17515171739241561403917323)
  ·
    refine ⟨26272757608862342105875985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17515171739241561403917323 26272757608862342105875985)
    ·
      refine ⟨19704568206646756579406989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26272757608862342105875985 19704568206646756579406989)
      ·
        refine ⟨7389213077492533717277621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19704568206646756579406989 7389213077492533717277621)
        ·
          refine ⟨692738726014925035994777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7389213077492533717277621 692738726014925035994777)
          ·
            refine ⟨519554044511193776996083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692738726014925035994777 519554044511193776996083)
            ·
              refine ⟨779331066766790665494125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519554044511193776996083 779331066766790665494125)
              ·
                refine ⟨292249150037546499560297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 779331066766790665494125 292249150037546499560297)
                ·
                  refine ⟨219186862528159874670223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292249150037546499560297 219186862528159874670223)
                  ·
                    rfl

theorem cell20_480223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 2].length) (baseStart_480223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480223 prefixEnd_480223 := by exact prefixLift 480223
  have htrace : WordTrace (prefixWord ++ tailWord_480223) baseStart_480223 baseEnd_480223 := by
    simpa [prefixWord, tailWord_480223, baseEnd_480223] using wordTrace_append hprefix tailTrace_480223
  have hstable : (prefixWord ++ tailWord_480223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480223).length < 2 ^ (prefixWord ++ tailWord_480223).sum := by decide
  have hdescent : baseEnd_480223 < baseStart_480223 := by decide
  rcases family_descends (prefixWord ++ tailWord_480223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480234 : List Nat := [3, 1, 3, 1, 2, 4, 6]
def baseStart_480234 : Nat := 118140960795 + 480234 * 2 ^ 59
def prefixEnd_480234 : Nat := 4983230072969 + 3 ^ 40 * 480234 * 2
def baseEnd_480234 : Nat := 24354653691988080589279

theorem tailTrace_480234 : CollatzResearch.WordTrace tailWord_480234 prefixEnd_480234 24354653691988080589279 := by
  unfold tailWord_480234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378893235550427570641939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11677048628134473521711837 4378893235550427570641939)
  ·
    refine ⟨6568339853325641355962909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4378893235550427570641939 6568339853325641355962909)
    ·
      refine ⟨2463127444997115508486091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6568339853325641355962909 2463127444997115508486091)
      ·
        refine ⟨3694691167495673262729137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463127444997115508486091 3694691167495673262729137)
        ·
          refine ⟨2771018375621754947046853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694691167495673262729137 2771018375621754947046853)
          ·
            refine ⟨519565945429079052571285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2771018375621754947046853 519565945429079052571285)
            ·
              refine ⟨24354653691988080589279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 519565945429079052571285 24354653691988080589279)
              ·
                rfl

theorem cell20_480234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 6].length) (baseStart_480234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480234 prefixEnd_480234 := by exact prefixLift 480234
  have htrace : WordTrace (prefixWord ++ tailWord_480234) baseStart_480234 baseEnd_480234 := by
    simpa [prefixWord, tailWord_480234, baseEnd_480234] using wordTrace_append hprefix tailTrace_480234
  have hstable : (prefixWord ++ tailWord_480234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480234).length < 2 ^ (prefixWord ++ tailWord_480234).sum := by decide
  have hdescent : baseEnd_480234 < baseStart_480234 := by decide
  rcases family_descends (prefixWord ++ tailWord_480234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480241 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_480241 : Nat := 118140960795 + 480241 * 2 ^ 59
def prefixEnd_480241 : Nat := 4983230072969 + 3 ^ 40 * 480241 * 2
def baseEnd_480241 : Nat := 219195078218631812070149

theorem tailTrace_480241 : CollatzResearch.WordTrace tailWord_480241 prefixEnd_480241 219195078218631812070149 := by
  unfold tailWord_480241
  simp only [CollatzResearch.WordTrace]
  refine ⟨17515828253176350478072577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11677218835450900318715051 17515828253176350478072577)
  ·
    refine ⟨13136871189882262858554433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17515828253176350478072577 13136871189882262858554433)
    ·
      refine ⟨9852653392411697143915825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13136871189882262858554433 9852653392411697143915825)
      ·
        refine ⟨7389490044308772857936869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9852653392411697143915825 7389490044308772857936869)
        ·
          refine ⟨1385529383307894910863163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7389490044308772857936869 1385529383307894910863163)
          ·
            refine ⟨2078294074961842366294745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385529383307894910863163 2078294074961842366294745)
            ·
              refine ⟨1558720556221381774721059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2078294074961842366294745 1558720556221381774721059)
              ·
                refine ⟨2338080834332072662081589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558720556221381774721059 2338080834332072662081589)
                ·
                  refine ⟨219195078218631812070149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2338080834332072662081589 219195078218631812070149)
                  ·
                    rfl

theorem cell20_480241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_480241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480241 prefixEnd_480241 := by exact prefixLift 480241
  have htrace : WordTrace (prefixWord ++ tailWord_480241) baseStart_480241 baseEnd_480241 := by
    simpa [prefixWord, tailWord_480241, baseEnd_480241] using wordTrace_append hprefix tailTrace_480241
  have hstable : (prefixWord ++ tailWord_480241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480241).length < 2 ^ (prefixWord ++ tailWord_480241).sum := by decide
  have hdescent : baseEnd_480241 < baseStart_480241 := by decide
  rcases family_descends (prefixWord ++ tailWord_480241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480392 : List Nat := [2, 1, 3, 4, 3, 1, 1, 3, 2]
def baseStart_480392 : Nat := 118140960795 + 480392 * 2 ^ 59
def prefixEnd_480392 : Nat := 4983230072969 + 3 ^ 40 * 480392 * 2
def baseEnd_480392 : Nat := 219263998733146398036199

theorem tailTrace_480392 : CollatzResearch.WordTrace tailWord_480392 prefixEnd_480392 219263998733146398036199 := by
  unfold tailWord_480392
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760667837814651633409715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11680890450419535511212953 8760667837814651633409715)
  ·
    refine ⟨13141001756721977450114573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8760667837814651633409715 13141001756721977450114573)
    ·
      refine ⟨4927875658770741543792965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13141001756721977450114573 4927875658770741543792965)
      ·
        refine ⟨923976686019514039461181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4927875658770741543792965 923976686019514039461181)
        ·
          refine ⟨346491257257317764797943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 923976686019514039461181 346491257257317764797943)
          ·
            refine ⟨519736885885976647196915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346491257257317764797943 519736885885976647196915)
            ·
              refine ⟨779605328828964970795373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519736885885976647196915 779605328828964970795373)
              ·
                refine ⟨292351998310861864048265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 779605328828964970795373 292351998310861864048265)
                ·
                  refine ⟨219263998733146398036199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292351998310861864048265 219263998733146398036199)
                  ·
                    rfl

theorem cell20_480392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_480392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480392 prefixEnd_480392 := by exact prefixLift 480392
  have htrace : WordTrace (prefixWord ++ tailWord_480392) baseStart_480392 baseEnd_480392 := by
    simpa [prefixWord, tailWord_480392, baseEnd_480392] using wordTrace_append hprefix tailTrace_480392
  have hstable : (prefixWord ++ tailWord_480392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480392).length < 2 ^ (prefixWord ++ tailWord_480392).sum := by decide
  have hdescent : baseEnd_480392 < baseStart_480392 := by decide
  rcases family_descends (prefixWord ++ tailWord_480392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480407 : List Nat := [1, 1, 3, 3, 3, 1, 8]
def baseStart_480407 : Nat := 118140960795 + 480407 * 2 ^ 59
def prefixEnd_480407 : Nat := 4983230072969 + 3 ^ 40 * 480407 * 2
def baseEnd_480407 : Nat := 24363427237985890281793

theorem tailTrace_480407 : CollatzResearch.WordTrace tailWord_480407 prefixEnd_480407 24363427237985890281793 := by
  unfold tailWord_480407
  simp only [CollatzResearch.WordTrace]
  refine ⟨17521882770574960828615475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11681255180383307219076983 17521882770574960828615475)
  ·
    refine ⟨26282824155862441242923213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17521882770574960828615475 26282824155862441242923213)
    ·
      refine ⟨9856059058448415466096205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26282824155862441242923213 9856059058448415466096205)
      ·
        refine ⟨3696022146918155799786077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9856059058448415466096205 3696022146918155799786077)
        ·
          refine ⟨1386008305094308424919779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3696022146918155799786077 1386008305094308424919779)
          ·
            refine ⟨2079012457641462637379669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386008305094308424919779 2079012457641462637379669)
            ·
              refine ⟨24363427237985890281793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2079012457641462637379669 24363427237985890281793)
              ·
                rfl

theorem cell20_480407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_480407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480407 prefixEnd_480407 := by exact prefixLift 480407
  have htrace : WordTrace (prefixWord ++ tailWord_480407) baseStart_480407 baseEnd_480407 := by
    simpa [prefixWord, tailWord_480407, baseEnd_480407] using wordTrace_append hprefix tailTrace_480407
  have hstable : (prefixWord ++ tailWord_480407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480407).length < 2 ^ (prefixWord ++ tailWord_480407).sum := by decide
  have hdescent : baseEnd_480407 < baseStart_480407 := by decide
  rcases family_descends (prefixWord ++ tailWord_480407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480445 : List Nat := [1, 4, 1, 2, 1, 1, 4, 6]
def baseStart_480445 : Nat := 118140960795 + 480445 * 2 ^ 59
def prefixEnd_480445 : Nat := 4983230072969 + 3 ^ 40 * 480445 * 2
def baseEnd_480445 : Nat := 73096063125771256423105

theorem tailTrace_480445 : CollatzResearch.WordTrace tailWord_480445 prefixEnd_480445 73096063125771256423105 := by
  unfold tailWord_480445
  simp only [CollatzResearch.WordTrace]
  refine ⟨17523268744437293318498789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11682179162958195545665859 17523268744437293318498789)
  ·
    refine ⟨3285612889581992497218523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17523268744437293318498789 3285612889581992497218523)
    ·
      refine ⟨4928419334372988745827785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285612889581992497218523 4928419334372988745827785)
      ·
        refine ⟨3696314500779741559370839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4928419334372988745827785 3696314500779741559370839)
        ·
          refine ⟨5544471751169612339056259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696314500779741559370839 5544471751169612339056259)
          ·
            refine ⟨8316707626754418508584389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5544471751169612339056259 8316707626754418508584389)
            ·
              refine ⟨1559382680016453470359573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8316707626754418508584389 1559382680016453470359573)
              ·
                refine ⟨73096063125771256423105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1559382680016453470359573 73096063125771256423105)
                ·
                  rfl

theorem cell20_480445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_480445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480445 prefixEnd_480445 := by exact prefixLift 480445
  have htrace : WordTrace (prefixWord ++ tailWord_480445) baseStart_480445 baseEnd_480445 := by
    simpa [prefixWord, tailWord_480445, baseEnd_480445] using wordTrace_append hprefix tailTrace_480445
  have hstable : (prefixWord ++ tailWord_480445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480445).length < 2 ^ (prefixWord ++ tailWord_480445).sum := by decide
  have hdescent : baseEnd_480445 < baseStart_480445 := by decide
  rcases family_descends (prefixWord ++ tailWord_480445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480459 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_480459 : Nat := 118140960795 + 480459 * 2 ^ 59
def prefixEnd_480459 : Nat := 4983230072969 + 3 ^ 40 * 480459 * 2
def baseEnd_480459 : Nat := 219294579358791942802591

theorem tailTrace_480459 : CollatzResearch.WordTrace tailWord_480459 prefixEnd_480459 219294579358791942802591 := by
  unfold tailWord_480459
  simp only [CollatzResearch.WordTrace]
  refine ⟨17523779366386573709508431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11682519577591049139672287 17523779366386573709508431)
  ·
    refine ⟨26285669049579860564262647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17523779366386573709508431 26285669049579860564262647)
    ·
      refine ⟨39428503574369790846393971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26285669049579860564262647 39428503574369790846393971)
      ·
        refine ⟨59142755361554686269590957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39428503574369790846393971 59142755361554686269590957)
        ·
          refine ⟨22178533260583007351096609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59142755361554686269590957 22178533260583007351096609)
          ·
            refine ⟨16633899945437255513322457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22178533260583007351096609 16633899945437255513322457)
            ·
              refine ⟨12475424959077941634991843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16633899945437255513322457 12475424959077941634991843)
              ·
                refine ⟨18713137438616912452487765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12475424959077941634991843 18713137438616912452487765)
                ·
                  refine ⟨219294579358791942802591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18713137438616912452487765 219294579358791942802591)
                  ·
                    rfl

theorem cell20_480459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_480459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480459 prefixEnd_480459 := by exact prefixLift 480459
  have htrace : WordTrace (prefixWord ++ tailWord_480459) baseStart_480459 baseEnd_480459 := by
    simpa [prefixWord, tailWord_480459, baseEnd_480459] using wordTrace_append hprefix tailTrace_480459
  have hstable : (prefixWord ++ tailWord_480459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480459).length < 2 ^ (prefixWord ++ tailWord_480459).sum := by decide
  have hdescent : baseEnd_480459 < baseStart_480459 := by decide
  rcases family_descends (prefixWord ++ tailWord_480459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480462 : List Nat := [4, 1, 1, 1, 6, 7]
def baseStart_480462 : Nat := 118140960795 + 480462 * 2 ^ 59
def prefixEnd_480462 : Nat := 4983230072969 + 3 ^ 40 * 480462 * 2
def baseEnd_480462 : Nat := 8122072171871750581577

theorem tailTrace_480462 : CollatzResearch.WordTrace tailWord_480462 prefixEnd_480462 8122072171871750581577 := by
  unfold tailWord_480462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190486098171963152733455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11682592523583803481245093 2190486098171963152733455)
  ·
    refine ⟨3285729147257944729100183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190486098171963152733455 3285729147257944729100183)
    ·
      refine ⟨4928593720886917093650275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285729147257944729100183 4928593720886917093650275)
      ·
        refine ⟨7392890581330375640475413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928593720886917093650275 7392890581330375640475413)
        ·
          refine ⟨346541745999861358147285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7392890581330375640475413 346541745999861358147285)
          ·
            refine ⟨8122072171871750581577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 346541745999861358147285 8122072171871750581577)
            ·
              rfl

theorem cell20_480462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 7].length) (baseStart_480462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480462 prefixEnd_480462 := by exact prefixLift 480462
  have htrace : WordTrace (prefixWord ++ tailWord_480462) baseStart_480462 baseEnd_480462 := by
    simpa [prefixWord, tailWord_480462, baseEnd_480462] using wordTrace_append hprefix tailTrace_480462
  have hstable : (prefixWord ++ tailWord_480462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480462).length < 2 ^ (prefixWord ++ tailWord_480462).sum := by decide
  have hdescent : baseEnd_480462 < baseStart_480462 := by decide
  rcases family_descends (prefixWord ++ tailWord_480462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480472 : List Nat := [2, 1, 2, 2, 5, 1, 1, 4, 2]
def baseStart_480472 : Nat := 118140960795 + 480472 * 2 ^ 59
def prefixEnd_480472 : Nat := 4983230072969 + 3 ^ 40 * 480472 * 2
def baseEnd_480472 : Nat := 219300512913021675369205

theorem tailTrace_480472 : CollatzResearch.WordTrace tailWord_480472 prefixEnd_480472 219300512913021675369205 := by
  unfold tailWord_480472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762126757669738464865835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11682835676892984619821113 8762126757669738464865835)
  ·
    refine ⟨13143190136504607697298753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8762126757669738464865835 13143190136504607697298753)
    ·
      refine ⟨9857392602378455772974065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13143190136504607697298753 9857392602378455772974065)
      ·
        refine ⟨7393044451783841829730549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857392602378455772974065 7393044451783841829730549)
        ·
          refine ⟨693097917354735171537239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7393044451783841829730549 693097917354735171537239)
          ·
            refine ⟨1039646876032102757305859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693097917354735171537239 1039646876032102757305859)
            ·
              refine ⟨1559470314048154135958789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039646876032102757305859 1559470314048154135958789)
              ·
                refine ⟨292400683884028900492273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1559470314048154135958789 292400683884028900492273)
                ·
                  refine ⟨219300512913021675369205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292400683884028900492273 219300512913021675369205)
                  ·
                    rfl

theorem cell20_480472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_480472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480472 prefixEnd_480472 := by exact prefixLift 480472
  have htrace : WordTrace (prefixWord ++ tailWord_480472) baseStart_480472 baseEnd_480472 := by
    simpa [prefixWord, tailWord_480472, baseEnd_480472] using wordTrace_append hprefix tailTrace_480472
  have hstable : (prefixWord ++ tailWord_480472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480472).length < 2 ^ (prefixWord ++ tailWord_480472).sum := by decide
  have hdescent : baseEnd_480472 < baseStart_480472 := by decide
  rcases family_descends (prefixWord ++ tailWord_480472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480493 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_480493 : Nat := 118140960795 + 480493 * 2 ^ 59
def prefixEnd_480493 : Nat := 4983230072969 + 3 ^ 40 * 480493 * 2
def baseEnd_480493 : Nat := 219310097885238935669119

theorem tailTrace_480493 : CollatzResearch.WordTrace tailWord_480493 prefixEnd_480493 219310097885238935669119 := by
  unfold tailWord_480493
  simp only [CollatzResearch.WordTrace]
  refine ⟨17525019448263397516246133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11683346298842265010830755 17525019448263397516246133)
  ·
    refine ⟨1642970573274693517148075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17525019448263397516246133 1642970573274693517148075)
    ·
      refine ⟨2464455859912040275722113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642970573274693517148075 2464455859912040275722113)
      ·
        refine ⟨1848341894934030206791585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2464455859912040275722113 1848341894934030206791585)
        ·
          refine ⟨1386256421200522655093689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1848341894934030206791585 1386256421200522655093689)
          ·
            refine ⟨1039692315900391991320267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386256421200522655093689 1039692315900391991320267)
            ·
              refine ⟨1559538473850587986980401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039692315900391991320267 1559538473850587986980401)
              ·
                refine ⟨1169653855387940990235301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559538473850587986980401 1169653855387940990235301)
                ·
                  refine ⟨219310097885238935669119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1169653855387940990235301 219310097885238935669119)
                  ·
                    rfl

theorem cell20_480493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_480493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480493 prefixEnd_480493 := by exact prefixLift 480493
  have htrace : WordTrace (prefixWord ++ tailWord_480493) baseStart_480493 baseEnd_480493 := by
    simpa [prefixWord, tailWord_480493, baseEnd_480493] using wordTrace_append hprefix tailTrace_480493
  have hstable : (prefixWord ++ tailWord_480493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480493).length < 2 ^ (prefixWord ++ tailWord_480493).sum := by decide
  have hdescent : baseEnd_480493 < baseStart_480493 := by decide
  rcases family_descends (prefixWord ++ tailWord_480493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480510 : List Nat := [4, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_480510 : Nat := 118140960795 + 480510 * 2 ^ 59
def prefixEnd_480510 : Nat := 4983230072969 + 3 ^ 40 * 480510 * 2
def baseEnd_480510 : Nat := 219317857148462432102383

theorem tailTrace_480510 : CollatzResearch.WordTrace tailWord_480510 prefixEnd_480510 219317857148462432102383 := by
  unfold tailWord_480510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190704936150226177451873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11683759659467872946409989 2190704936150226177451873)
  ·
    refine ⟨1643028702112669633088905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2190704936150226177451873 1643028702112669633088905)
    ·
      refine ⟨1232271526584502224816679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1643028702112669633088905 1232271526584502224816679)
      ·
        refine ⟨1848407289876753337225019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232271526584502224816679 1848407289876753337225019)
        ·
          refine ⟨2772610934815130005837529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848407289876753337225019 2772610934815130005837529)
          ·
            refine ⟨2079458201111347504378147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772610934815130005837529 2079458201111347504378147)
            ·
              refine ⟨3119187301667021256567221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079458201111347504378147 3119187301667021256567221)
              ·
                refine ⟨292423809531283242803177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3119187301667021256567221 292423809531283242803177)
                ·
                  refine ⟨219317857148462432102383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292423809531283242803177 219317857148462432102383)
                  ·
                    rfl

theorem cell20_480510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_480510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480510 prefixEnd_480510 := by exact prefixLift 480510
  have htrace : WordTrace (prefixWord ++ tailWord_480510) baseStart_480510 baseEnd_480510 := by
    simpa [prefixWord, tailWord_480510, baseEnd_480510] using wordTrace_append hprefix tailTrace_480510
  have hstable : (prefixWord ++ tailWord_480510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480510).length < 2 ^ (prefixWord ++ tailWord_480510).sum := by decide
  have hdescent : baseEnd_480510 < baseStart_480510 := by decide
  rcases family_descends (prefixWord ++ tailWord_480510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480524 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_480524 : Nat := 118140960795 + 480524 * 2 ^ 59
def prefixEnd_480524 : Nat := 4983230072969 + 3 ^ 40 * 480524 * 2
def baseEnd_480524 : Nat := 219324247129940605635659

theorem tailTrace_480524 : CollatzResearch.WordTrace tailWord_480524 prefixEnd_480524 219324247129940605635659 := by
  unfold tailWord_480524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763075055575544905312313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11684100074100726540416417 8763075055575544905312313)
  ·
    refine ⟨6572306291681658678984235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8763075055575544905312313 6572306291681658678984235)
    ·
      refine ⟨9858459437522488018476353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572306291681658678984235 9858459437522488018476353)
      ·
        refine ⟨7393844578141866013857265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9858459437522488018476353 7393844578141866013857265)
        ·
          refine ⟨5545383433606399510392949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7393844578141866013857265 5545383433606399510392949)
          ·
            refine ⟨519879696900599954099339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5545383433606399510392949 519879696900599954099339)
            ·
              refine ⟨779819545350899931149009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519879696900599954099339 779819545350899931149009)
              ·
                refine ⟨584864659013174948361757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779819545350899931149009 584864659013174948361757)
                ·
                  refine ⟨219324247129940605635659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584864659013174948361757 219324247129940605635659)
                  ·
                    rfl

theorem cell20_480524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_480524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480524 prefixEnd_480524 := by exact prefixLift 480524
  have htrace : WordTrace (prefixWord ++ tailWord_480524) baseStart_480524 baseEnd_480524 := by
    simpa [prefixWord, tailWord_480524, baseEnd_480524] using wordTrace_append hprefix tailTrace_480524
  have hstable : (prefixWord ++ tailWord_480524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480524).length < 2 ^ (prefixWord ++ tailWord_480524).sum := by decide
  have hdescent : baseEnd_480524 < baseStart_480524 := by decide
  rcases family_descends (prefixWord ++ tailWord_480524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480541 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 3]
def baseStart_480541 : Nat := 118140960795 + 480541 * 2 ^ 59
def prefixEnd_480541 : Nat := 4983230072969 + 3 ^ 40 * 480541 * 2
def baseEnd_480541 : Nat := 219332006393164102068923

theorem tailTrace_480541 : CollatzResearch.WordTrace tailWord_480541 prefixEnd_480541 219332006393164102068923 := by
  unfold tailWord_480541
  simp only [CollatzResearch.WordTrace]
  refine ⟨17526770152089501713993477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11684513434726334475995651 17526770152089501713993477)
  ·
    refine ⟨3286269403516781571373777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17526770152089501713993477 3286269403516781571373777)
    ·
      refine ⟨2464702052637586178530333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3286269403516781571373777 2464702052637586178530333)
      ·
        refine ⟨924263269739094816948875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2464702052637586178530333 924263269739094816948875)
        ·
          refine ⟨1386394904608642225423313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924263269739094816948875 1386394904608642225423313)
          ·
            refine ⟨1039796178456481669067485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386394904608642225423313 1039796178456481669067485)
            ·
              refine ⟨389923566921180625900307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1039796178456481669067485 389923566921180625900307)
              ·
                refine ⟨584885350381770938850461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389923566921180625900307 584885350381770938850461)
                ·
                  refine ⟨219332006393164102068923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584885350381770938850461 219332006393164102068923)
                  ·
                    rfl

theorem cell20_480541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_480541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480541 prefixEnd_480541 := by exact prefixLift 480541
  have htrace : WordTrace (prefixWord ++ tailWord_480541) baseStart_480541 baseEnd_480541 := by
    simpa [prefixWord, tailWord_480541, baseEnd_480541] using wordTrace_append hprefix tailTrace_480541
  have hstable : (prefixWord ++ tailWord_480541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480541).length < 2 ^ (prefixWord ++ tailWord_480541).sum := by decide
  have hdescent : baseEnd_480541 < baseStart_480541 := by decide
  rcases family_descends (prefixWord ++ tailWord_480541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480582 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_480582 : Nat := 118140960795 + 480582 * 2 ^ 59
def prefixEnd_480582 : Nat := 4983230072969 + 3 ^ 40 * 480582 * 2
def baseEnd_480582 : Nat := 219350719910350181702089

theorem tailTrace_480582 : CollatzResearch.WordTrace tailWord_480582 prefixEnd_480582 219350719910350181702089 := by
  unfold tailWord_480582
  simp only [CollatzResearch.WordTrace]
  refine ⟨547758298279405178632375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11685510363293977144157333 547758298279405178632375)
  ·
    refine ⟨821637447419107767948563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 547758298279405178632375 821637447419107767948563)
    ·
      refine ⟨1232456171128661651922845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821637447419107767948563 1232456171128661651922845)
      ·
        refine ⟨462171064173248119471067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1232456171128661651922845 462171064173248119471067)
        ·
          refine ⟨693256596259872179206601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462171064173248119471067 693256596259872179206601)
          ·
            refine ⟨519942447194904134404951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693256596259872179206601 519942447194904134404951)
            ·
              refine ⟨779913670792356201607427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519942447194904134404951 779913670792356201607427)
              ·
                refine ⟨1169870506188534302411141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779913670792356201607427 1169870506188534302411141)
                ·
                  refine ⟨219350719910350181702089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1169870506188534302411141 219350719910350181702089)
                  ·
                    rfl

theorem cell20_480582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_480582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480582 prefixEnd_480582 := by exact prefixLift 480582
  have htrace : WordTrace (prefixWord ++ tailWord_480582) baseStart_480582 baseEnd_480582 := by
    simpa [prefixWord, tailWord_480582, baseEnd_480582] using wordTrace_append hprefix tailTrace_480582
  have hstable : (prefixWord ++ tailWord_480582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480582).length < 2 ^ (prefixWord ++ tailWord_480582).sum := by decide
  have hdescent : baseEnd_480582 < baseStart_480582 := by decide
  rcases family_descends (prefixWord ++ tailWord_480582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480597 : List Nat := [1, 3, 2, 2, 3, 1, 1, 7]
def baseStart_480597 : Nat := 118140960795 + 480597 * 2 ^ 59
def prefixEnd_480597 : Nat := 4983230072969 + 3 ^ 40 * 480597 * 2
def baseEnd_480597 : Nat := 73119188773025598734009

theorem tailTrace_480597 : CollatzResearch.WordTrace tailWord_480597 prefixEnd_480597 73119188773025598734009 := by
  unfold tailWord_480597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17528812639886623278032045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11685875093257748852021363 17528812639886623278032045)
  ·
    refine ⟨6573304739957483729262017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17528812639886623278032045 6573304739957483729262017)
    ·
      refine ⟨4929978554968112796946513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6573304739957483729262017 4929978554968112796946513)
      ·
        refine ⟨3697483916226084597709885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929978554968112796946513 3697483916226084597709885)
        ·
          refine ⟨1386556468584781724141207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3697483916226084597709885 1386556468584781724141207)
          ·
            refine ⟨2079834702877172586211811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386556468584781724141207 2079834702877172586211811)
            ·
              refine ⟨3119752054315758879317717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079834702877172586211811 3119752054315758879317717)
              ·
                refine ⟨73119188773025598734009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3119752054315758879317717 73119188773025598734009)
                ·
                  rfl

theorem cell20_480597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_480597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480597 prefixEnd_480597 := by exact prefixLift 480597
  have htrace : WordTrace (prefixWord ++ tailWord_480597) baseStart_480597 baseEnd_480597 := by
    simpa [prefixWord, tailWord_480597, baseEnd_480597] using wordTrace_append hprefix tailTrace_480597
  have hstable : (prefixWord ++ tailWord_480597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480597).length < 2 ^ (prefixWord ++ tailWord_480597).sum := by decide
  have hdescent : baseEnd_480597 < baseStart_480597 := by decide
  rcases family_descends (prefixWord ++ tailWord_480597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480666 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_480666 : Nat := 118140960795 + 480666 * 2 ^ 59
def prefixEnd_480666 : Nat := 4983230072969 + 3 ^ 40 * 480666 * 2
def baseEnd_480666 : Nat := 219389059799219222901745

theorem tailTrace_480666 : CollatzResearch.WordTrace tailWord_480666 prefixEnd_480666 219389059799219222901745 := by
  unfold tailWord_480666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4382832319159162015573463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11687552851091098708195901 4382832319159162015573463)
  ·
    refine ⟨6574248478738743023360195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4382832319159162015573463 6574248478738743023360195)
    ·
      refine ⟨9861372718108114535040293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6574248478738743023360195 9861372718108114535040293)
      ·
        refine ⟨1849007384645271475320055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9861372718108114535040293 1849007384645271475320055)
        ·
          refine ⟨2773511076967907212980083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849007384645271475320055 2773511076967907212980083)
          ·
            refine ⟨4160266615451860819470125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2773511076967907212980083 4160266615451860819470125)
            ·
              refine ⟨1560099980794447807301297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4160266615451860819470125 1560099980794447807301297)
              ·
                refine ⟨1170074985595835855475973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560099980794447807301297 1170074985595835855475973)
                ·
                  refine ⟨219389059799219222901745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170074985595835855475973 219389059799219222901745)
                  ·
                    rfl

theorem cell20_480666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_480666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480666 prefixEnd_480666 := by exact prefixLift 480666
  have htrace : WordTrace (prefixWord ++ tailWord_480666) baseStart_480666 baseEnd_480666 := by
    simpa [prefixWord, tailWord_480666, baseEnd_480666] using wordTrace_append hprefix tailTrace_480666
  have hstable : (prefixWord ++ tailWord_480666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480666).length < 2 ^ (prefixWord ++ tailWord_480666).sum := by decide
  have hdescent : baseEnd_480666 < baseStart_480666 := by decide
  rcases family_descends (prefixWord ++ tailWord_480666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480697 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 5]
def baseStart_480697 : Nat := 118140960795 + 480697 * 2 ^ 59
def prefixEnd_480697 : Nat := 4983230072969 + 3 ^ 40 * 480697 * 2
def baseEnd_480697 : Nat := 219403209043920892868285

theorem tailTrace_480697 : CollatzResearch.WordTrace tailWord_480697 prefixEnd_480697 219403209043920892868285 := by
  unfold tailWord_480697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17532459939524340356672345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11688306626349560237781563 17532459939524340356672345)
  ·
    refine ⟨13149344954643255267504259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17532459939524340356672345 13149344954643255267504259)
    ·
      refine ⟨19724017431964882901256389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13149344954643255267504259 19724017431964882901256389)
      ·
        refine ⟨3698253268493415543985573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19724017431964882901256389 3698253268493415543985573)
        ·
          refine ⟨693422487842515414497295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3698253268493415543985573 693422487842515414497295)
          ·
            refine ⟨1040133731763773121745943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693422487842515414497295 1040133731763773121745943)
            ·
              refine ⟨1560200597645659682618915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040133731763773121745943 1560200597645659682618915)
              ·
                refine ⟨2340300896468489523928373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560200597645659682618915 2340300896468489523928373)
                ·
                  refine ⟨219403209043920892868285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2340300896468489523928373 219403209043920892868285)
                  ·
                    rfl

theorem cell20_480697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_480697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480697 prefixEnd_480697 := by exact prefixLift 480697
  have htrace : WordTrace (prefixWord ++ tailWord_480697) baseStart_480697 baseEnd_480697 := by
    simpa [prefixWord, tailWord_480697, baseEnd_480697] using wordTrace_append hprefix tailTrace_480697
  have hstable : (prefixWord ++ tailWord_480697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480697).length < 2 ^ (prefixWord ++ tailWord_480697).sum := by decide
  have hdescent : baseEnd_480697 < baseStart_480697 := by decide
  rcases family_descends (prefixWord ++ tailWord_480697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480706 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_480706 : Nat := 118140960795 + 480706 * 2 ^ 59
def prefixEnd_480706 : Nat := 4983230072969 + 3 ^ 40 * 480706 * 2
def baseEnd_480706 : Nat := 219407316889156861568249

theorem tailTrace_480706 : CollatzResearch.WordTrace tailWord_480706 prefixEnd_480706 219407316889156861568249 := by
  unfold tailWord_480706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383197049122933723437493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11688525464327823262499981 4383197049122933723437493)
  ·
    refine ⟨410924723355275036572265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4383197049122933723437493 410924723355275036572265)
    ·
      refine ⟨308193542516456277429199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410924723355275036572265 308193542516456277429199)
      ·
        refine ⟨462290313774684416143799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308193542516456277429199 462290313774684416143799)
        ·
          refine ⟨693435470662026624215699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462290313774684416143799 693435470662026624215699)
          ·
            refine ⟨1040153205993039936323549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693435470662026624215699 1040153205993039936323549)
            ·
              refine ⟨390057452247389976121331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040153205993039936323549 390057452247389976121331)
              ·
                refine ⟨585086178371084964181997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390057452247389976121331 585086178371084964181997)
                ·
                  refine ⟨219407316889156861568249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585086178371084964181997 219407316889156861568249)
                  ·
                    rfl

theorem cell20_480706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_480706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480706 prefixEnd_480706 := by exact prefixLift 480706
  have htrace : WordTrace (prefixWord ++ tailWord_480706) baseStart_480706 baseEnd_480706 := by
    simpa [prefixWord, tailWord_480706, baseEnd_480706] using wordTrace_append hprefix tailTrace_480706
  have hstable : (prefixWord ++ tailWord_480706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480706).length < 2 ^ (prefixWord ++ tailWord_480706).sum := by decide
  have hdescent : baseEnd_480706 < baseStart_480706 := by decide
  rcases family_descends (prefixWord ++ tailWord_480706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480714 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_480714 : Nat := 118140960795 + 480714 * 2 ^ 59
def prefixEnd_480714 : Nat := 4983230072969 + 3 ^ 40 * 480714 * 2
def baseEnd_480714 : Nat := 219410968307144389301549

theorem tailTrace_480714 : CollatzResearch.WordTrace tailWord_480714 prefixEnd_480714 219410968307144389301549 := by
  unfold tailWord_480714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383269995115688065010299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11688719986975168173360797 4383269995115688065010299)
  ·
    refine ⟨6574904992673532097515449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383269995115688065010299 6574904992673532097515449)
    ·
      refine ⟨4931178744505149073136587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6574904992673532097515449 4931178744505149073136587)
      ·
        refine ⟨7396768116757723609704881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931178744505149073136587 7396768116757723609704881)
        ·
          refine ⟨5547576087568292707278661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7396768116757723609704881 5547576087568292707278661)
          ·
            refine ⟨1040170516419054882614749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5547576087568292707278661 1040170516419054882614749)
            ·
              refine ⟨390063943657145580980531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040170516419054882614749 390063943657145580980531)
              ·
                refine ⟨585095915485718371470797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390063943657145580980531 585095915485718371470797)
                ·
                  refine ⟨219410968307144389301549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585095915485718371470797 219410968307144389301549)
                  ·
                    rfl

theorem cell20_480714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_480714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480714 prefixEnd_480714 := by exact prefixLift 480714
  have htrace : WordTrace (prefixWord ++ tailWord_480714) baseStart_480714 baseEnd_480714 := by
    simpa [prefixWord, tailWord_480714, baseEnd_480714] using wordTrace_append hprefix tailTrace_480714
  have hstable : (prefixWord ++ tailWord_480714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480714).length < 2 ^ (prefixWord ++ tailWord_480714).sum := by decide
  have hdescent : baseEnd_480714 < baseStart_480714 := by decide
  rcases family_descends (prefixWord ++ tailWord_480714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480724 : List Nat := [2, 4, 1, 2, 4, 1, 2, 4]
def baseStart_480724 : Nat := 118140960795 + 480724 * 2 ^ 59
def prefixEnd_480724 : Nat := 4983230072969 + 3 ^ 40 * 480724 * 2
def baseEnd_480724 : Nat := 73138510859876266322725

theorem tailTrace_480724 : CollatzResearch.WordTrace tailWord_480724 prefixEnd_480724 73138510859876266322725 := by
  unfold tailWord_480724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8766722355213261983952613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11688963140284349311936817 8766722355213261983952613)
  ·
    refine ⟨1643760441602486621991115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8766722355213261983952613 1643760441602486621991115)
    ·
      refine ⟨2465640662403729932986673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643760441602486621991115 2465640662403729932986673)
      ·
        refine ⟨1849230496802797449740005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2465640662403729932986673 1849230496802797449740005)
        ·
          refine ⟨346730718150524521826251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1849230496802797449740005 346730718150524521826251)
          ·
            refine ⟨520096077225786782739377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346730718150524521826251 520096077225786782739377)
            ·
              refine ⟨390072057919340087054533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520096077225786782739377 390072057919340087054533)
              ·
                refine ⟨73138510859876266322725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390072057919340087054533 73138510859876266322725)
                ·
                  rfl

theorem cell20_480724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_480724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480724 prefixEnd_480724 := by exact prefixLift 480724
  have htrace : WordTrace (prefixWord ++ tailWord_480724) baseStart_480724 baseEnd_480724 := by
    simpa [prefixWord, tailWord_480724, baseEnd_480724] using wordTrace_append hprefix tailTrace_480724
  have hstable : (prefixWord ++ tailWord_480724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480724).length < 2 ^ (prefixWord ++ tailWord_480724).sum := by decide
  have hdescent : baseEnd_480724 < baseStart_480724 := by decide
  rcases family_descends (prefixWord ++ tailWord_480724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480769 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 3]
def baseStart_480769 : Nat := 118140960795 + 480769 * 2 ^ 59
def prefixEnd_480769 : Nat := 4983230072969 + 3 ^ 40 * 480769 * 2
def baseEnd_480769 : Nat := 219436071805808642467991

theorem tailTrace_480769 : CollatzResearch.WordTrace tailWord_480769 prefixEnd_480769 219436071805808642467991 := by
  unfold tailWord_480769
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535085995263496653293361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11690057330175664435528907 17535085995263496653293361)
  ·
    refine ⟨13151314496447622489970021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17535085995263496653293361 13151314496447622489970021)
    ·
      refine ⟨2465871468083929216869379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13151314496447622489970021 2465871468083929216869379)
      ·
        refine ⟨3698807202125893825304069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465871468083929216869379 3698807202125893825304069)
        ·
          refine ⟨693526350398605092244513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3698807202125893825304069 693526350398605092244513)
          ·
            refine ⟨520144762798953819183385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693526350398605092244513 520144762798953819183385)
            ·
              refine ⟨390108572099215364387539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520144762798953819183385 390108572099215364387539)
              ·
                refine ⟨585162858148823046581309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390108572099215364387539 585162858148823046581309)
                ·
                  refine ⟨219436071805808642467991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585162858148823046581309 219436071805808642467991)
                  ·
                    rfl

theorem cell20_480769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_480769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480769 prefixEnd_480769 := by exact prefixLift 480769
  have htrace : WordTrace (prefixWord ++ tailWord_480769) baseStart_480769 baseEnd_480769 := by
    simpa [prefixWord, tailWord_480769, baseEnd_480769] using wordTrace_append hprefix tailTrace_480769
  have hstable : (prefixWord ++ tailWord_480769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480769).length < 2 ^ (prefixWord ++ tailWord_480769).sum := by decide
  have hdescent : baseEnd_480769 < baseStart_480769 := by decide
  rcases family_descends (prefixWord ++ tailWord_480769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480797 : List Nat := [1, 4, 2, 2, 1, 1, 2, 5, 2]
def baseStart_480797 : Nat := 118140960795 + 480797 * 2 ^ 59
def prefixEnd_480797 : Nat := 4983230072969 + 3 ^ 40 * 480797 * 2
def baseEnd_480797 : Nat := 219448851768764989534543

theorem tailTrace_480797 : CollatzResearch.WordTrace tailWord_480797 prefixEnd_480797 219448851768764989534543 := by
  unfold tailWord_480797
  simp only [CollatzResearch.WordTrace]
  refine ⟨17536107239162057435312645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11690738159441371623541763 17536107239162057435312645)
  ·
    refine ⟨3288020107342885769121121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17536107239162057435312645 3288020107342885769121121)
    ·
      refine ⟨2466015080507164326840841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3288020107342885769121121 2466015080507164326840841)
      ·
        refine ⟨1849511310380373245130631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466015080507164326840841 1849511310380373245130631)
        ·
          refine ⟨2774266965570559867695947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849511310380373245130631 2774266965570559867695947)
          ·
            refine ⟨4161400448355839801543921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774266965570559867695947 4161400448355839801543921)
            ·
              refine ⟨3121050336266879851157941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161400448355839801543921 3121050336266879851157941)
              ·
                refine ⟨292598469025019986046057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3121050336266879851157941 292598469025019986046057)
                ·
                  refine ⟨219448851768764989534543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292598469025019986046057 219448851768764989534543)
                  ·
                    rfl

theorem cell20_480797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_480797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480797 prefixEnd_480797 := by exact prefixLift 480797
  have htrace : WordTrace (prefixWord ++ tailWord_480797) baseStart_480797 baseEnd_480797 := by
    simpa [prefixWord, tailWord_480797, baseEnd_480797] using wordTrace_append hprefix tailTrace_480797
  have hstable : (prefixWord ++ tailWord_480797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480797).length < 2 ^ (prefixWord ++ tailWord_480797).sum := by decide
  have hdescent : baseEnd_480797 < baseStart_480797 := by decide
  rcases family_descends (prefixWord ++ tailWord_480797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480814 : List Nat := [4, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_480814 : Nat := 118140960795 + 480814 * 2 ^ 59
def prefixEnd_480814 : Nat := 4983230072969 + 3 ^ 40 * 480814 * 2
def baseEnd_480814 : Nat := 219456611031988485967807

theorem tailTrace_480814 : CollatzResearch.WordTrace tailWord_480814 prefixEnd_480814 219456611031988485967807 := by
  unfold tailWord_480814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192090910012558667335187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11691151520066979559120997 2192090910012558667335187)
  ·
    refine ⟨3288136365018838001002781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2192090910012558667335187 3288136365018838001002781)
    ·
      refine ⟨1233051136882064250376043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3288136365018838001002781 1233051136882064250376043)
      ·
        refine ⟨1849576705323096375564065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233051136882064250376043 1849576705323096375564065)
        ·
          refine ⟨1387182528992322281673049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1849576705323096375564065 1387182528992322281673049)
          ·
            refine ⟨1040386896744241711254787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1387182528992322281673049 1040386896744241711254787)
            ·
              refine ⟨1560580345116362566882181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040386896744241711254787 1560580345116362566882181)
              ·
                refine ⟨292608814709317981290409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1560580345116362566882181 292608814709317981290409)
                ·
                  refine ⟨219456611031988485967807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292608814709317981290409 219456611031988485967807)
                  ·
                    rfl

theorem cell20_480814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_480814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480814 prefixEnd_480814 := by exact prefixLift 480814
  have htrace : WordTrace (prefixWord ++ tailWord_480814) baseStart_480814 baseEnd_480814 := by
    simpa [prefixWord, tailWord_480814, baseEnd_480814] using wordTrace_append hprefix tailTrace_480814
  have hstable : (prefixWord ++ tailWord_480814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480814).length < 2 ^ (prefixWord ++ tailWord_480814).sum := by decide
  have hdescent : baseEnd_480814 < baseStart_480814 := by decide
  rcases family_descends (prefixWord ++ tailWord_480814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480825 : List Nat := [1, 2, 1, 5, 1, 2, 3, 5]
def baseStart_480825 : Nat := 118140960795 + 480825 * 2 ^ 59
def prefixEnd_480825 : Nat := 4983230072969 + 3 ^ 40 * 480825 * 2
def baseEnd_480825 : Nat := 73153877243907112200365

theorem tailTrace_480825 : CollatzResearch.WordTrace tailWord_480825 prefixEnd_480825 73153877243907112200365 := by
  unfold tailWord_480825
  simp only [CollatzResearch.WordTrace]
  refine ⟨17537128483060618217331929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11691418988707078811554619 17537128483060618217331929)
  ·
    refine ⟨13152846362295463662998947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17537128483060618217331929 13152846362295463662998947)
    ·
      refine ⟨19729269543443195494498421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13152846362295463662998947 19729269543443195494498421)
      ·
        refine ⟨1849619019697799577609227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19729269543443195494498421 1849619019697799577609227)
        ·
          refine ⟨2774428529546699366413841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849619019697799577609227 2774428529546699366413841)
          ·
            refine ⟨2080821397160024524810381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774428529546699366413841 2080821397160024524810381)
            ·
              refine ⟨780308023935009196803893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2080821397160024524810381 780308023935009196803893)
              ·
                refine ⟨73153877243907112200365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 780308023935009196803893 73153877243907112200365)
                ·
                  rfl

theorem cell20_480825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_480825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480825 prefixEnd_480825 := by exact prefixLift 480825
  have htrace : WordTrace (prefixWord ++ tailWord_480825) baseStart_480825 baseEnd_480825 := by
    simpa [prefixWord, tailWord_480825, baseEnd_480825] using wordTrace_append hprefix tailTrace_480825
  have hstable : (prefixWord ++ tailWord_480825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480825).length < 2 ^ (prefixWord ++ tailWord_480825).sum := by decide
  have hdescent : baseEnd_480825 < baseStart_480825 := by decide
  rcases family_descends (prefixWord ++ tailWord_480825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480838 : List Nat := [6, 1, 1, 1, 3, 1, 3, 4]
def baseStart_480838 : Nat := 118140960795 + 480838 * 2 ^ 59
def prefixEnd_480838 : Nat := 4983230072969 + 3 ^ 40 * 480838 * 2
def baseEnd_480838 : Nat := 73155855095317023055903

theorem tailTrace_480838 : CollatzResearch.WordTrace tailWord_480838 prefixEnd_480838 73155855095317023055903 := by
  unfold tailWord_480838
  simp only [CollatzResearch.WordTrace]
  refine ⟨548050082250422544923599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11691735088009014291703445 548050082250422544923599)
  ·
    refine ⟨822075123375633817385399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548050082250422544923599 822075123375633817385399)
    ·
      refine ⟨1233112685063450726078099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822075123375633817385399 1233112685063450726078099)
      ·
        refine ⟨1849669027595176089117149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233112685063450726078099 1849669027595176089117149)
        ·
          refine ⟨693625885348191033418931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1849669027595176089117149 693625885348191033418931)
          ·
            refine ⟨1040438828022286550128397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693625885348191033418931 1040438828022286550128397)
            ·
              refine ⟨390164560508357456298149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040438828022286550128397 390164560508357456298149)
              ·
                refine ⟨73155855095317023055903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390164560508357456298149 73155855095317023055903)
                ·
                  rfl

theorem cell20_480838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_480838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480838 prefixEnd_480838 := by exact prefixLift 480838
  have htrace : WordTrace (prefixWord ++ tailWord_480838) baseStart_480838 baseEnd_480838 := by
    simpa [prefixWord, tailWord_480838, baseEnd_480838] using wordTrace_append hprefix tailTrace_480838
  have hstable : (prefixWord ++ tailWord_480838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480838).length < 2 ^ (prefixWord ++ tailWord_480838).sum := by decide
  have hdescent : baseEnd_480838 < baseStart_480838 := by decide
  rcases family_descends (prefixWord ++ tailWord_480838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480928 : List Nat := [2, 1, 1, 4, 3, 2, 3, 2, 2]
def baseStart_480928 : Nat := 118140960795 + 480928 * 2 ^ 59
def prefixEnd_480928 : Nat := 4983230072969 + 3 ^ 40 * 480928 * 2
def baseEnd_480928 : Nat := 219508643738310756167341

theorem tailTrace_480928 : CollatzResearch.WordTrace tailWord_480928 prefixEnd_480928 219508643738310756167341 := by
  unfold tailWord_480928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770442600843733404165719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11693923467791644538887625 8770442600843733404165719)
  ·
    refine ⟨13155663901265600106248579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770442600843733404165719 13155663901265600106248579)
    ·
      refine ⟨19733495851898400159372869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13155663901265600106248579 19733495851898400159372869)
      ·
        refine ⟨3700030472230950029882413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19733495851898400159372869 3700030472230950029882413)
        ·
          refine ⟨1387511427086606261205905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3700030472230950029882413 1387511427086606261205905)
          ·
            refine ⟨1040633570314954695904429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1387511427086606261205905 1040633570314954695904429)
            ·
              refine ⟨390237588868108010964161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040633570314954695904429 390237588868108010964161)
              ·
                refine ⟨292678191651081008223121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390237588868108010964161 292678191651081008223121)
                ·
                  refine ⟨219508643738310756167341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292678191651081008223121 219508643738310756167341)
                  ·
                    rfl

theorem cell20_480928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_480928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480928 prefixEnd_480928 := by exact prefixLift 480928
  have htrace : WordTrace (prefixWord ++ tailWord_480928) baseStart_480928 baseEnd_480928 := by
    simpa [prefixWord, tailWord_480928, baseEnd_480928] using wordTrace_append hprefix tailTrace_480928
  have hstable : (prefixWord ++ tailWord_480928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480928).length < 2 ^ (prefixWord ++ tailWord_480928).sum := by decide
  have hdescent : baseEnd_480928 < baseStart_480928 := by decide
  rcases family_descends (prefixWord ++ tailWord_480928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480932 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_480932 : Nat := 118140960795 + 480932 * 2 ^ 59
def prefixEnd_480932 : Nat := 4983230072969 + 3 ^ 40 * 480932 * 2
def baseEnd_480932 : Nat := 219510469447304520033991

theorem tailTrace_480932 : CollatzResearch.WordTrace tailWord_480932 prefixEnd_480932 219510469447304520033991 := by
  unfold tailWord_480932
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770515546836487745738525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11694020729115316994318033 8770515546836487745738525)
  ·
    refine ⟨3288943330063682904651947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8770515546836487745738525 3288943330063682904651947)
    ·
      refine ⟨4933414995095524356977921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288943330063682904651947 4933414995095524356977921)
      ·
        refine ⟨3700061246321643267733441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4933414995095524356977921 3700061246321643267733441)
        ·
          refine ⟨2775045934741232450800081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700061246321643267733441 2775045934741232450800081)
          ·
            refine ⟨2081284451055924338100061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2775045934741232450800081 2081284451055924338100061)
            ·
              refine ⟨780481669145971626787523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081284451055924338100061 780481669145971626787523)
              ·
                refine ⟨1170722503718957440181285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780481669145971626787523 1170722503718957440181285)
                ·
                  refine ⟨219510469447304520033991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170722503718957440181285 219510469447304520033991)
                  ·
                    rfl

theorem cell20_480932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_480932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480932 prefixEnd_480932 := by exact prefixLift 480932
  have htrace : WordTrace (prefixWord ++ tailWord_480932) baseStart_480932 baseEnd_480932 := by
    simpa [prefixWord, tailWord_480932, baseEnd_480932] using wordTrace_append hprefix tailTrace_480932
  have hstable : (prefixWord ++ tailWord_480932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480932).length < 2 ^ (prefixWord ++ tailWord_480932).sum := by decide
  have hdescent : baseEnd_480932 < baseStart_480932 := by decide
  rcases family_descends (prefixWord ++ tailWord_480932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480953 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_480953 : Nat := 118140960795 + 480953 * 2 ^ 59
def prefixEnd_480953 : Nat := 4983230072969 + 3 ^ 40 * 480953 * 2
def baseEnd_480953 : Nat := 219520054419521780333905

theorem tailTrace_480953 : CollatzResearch.WordTrace tailWord_480953 prefixEnd_480953 219520054419521780333905 := by
  unfold tailWord_480953
  simp only [CollatzResearch.WordTrace]
  refine ⟨17541797026596896077991513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11694531351064597385327675 17541797026596896077991513)
  ·
    refine ⟨13156347769947672058493635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17541797026596896077991513 13156347769947672058493635)
    ·
      refine ⟨19734521654921508087740453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13156347769947672058493635 19734521654921508087740453)
      ·
        refine ⟨3700222810297782766451335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19734521654921508087740453 3700222810297782766451335)
        ·
          refine ⟨5550334215446674149677003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700222810297782766451335 5550334215446674149677003)
          ·
            refine ⟨8325501323170011224515505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550334215446674149677003 8325501323170011224515505)
            ·
              refine ⟨6244125992377508418386629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325501323170011224515505 6244125992377508418386629)
              ·
                refine ⟨1170773623570782828447493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6244125992377508418386629 1170773623570782828447493)
                ·
                  refine ⟨219520054419521780333905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170773623570782828447493 219520054419521780333905)
                  ·
                    rfl

theorem cell20_480953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_480953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480953 prefixEnd_480953 := by exact prefixLift 480953
  have htrace : WordTrace (prefixWord ++ tailWord_480953) baseStart_480953 baseEnd_480953 := by
    simpa [prefixWord, tailWord_480953, baseEnd_480953] using wordTrace_append hprefix tailTrace_480953
  have hstable : (prefixWord ++ tailWord_480953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480953).length < 2 ^ (prefixWord ++ tailWord_480953).sum := by decide
  have hdescent : baseEnd_480953 < baseStart_480953 := by decide
  rcases family_descends (prefixWord ++ tailWord_480953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480960 : List Nat := [2, 1, 1, 2, 4, 1, 1, 8]
def baseStart_480960 : Nat := 118140960795 + 480960 * 2 ^ 59
def prefixEnd_480960 : Nat := 4983230072969 + 3 ^ 40 * 480960 * 2
def baseEnd_480960 : Nat := 73174416470086955700181

theorem tailTrace_480960 : CollatzResearch.WordTrace tailWord_480960 prefixEnd_480960 73174416470086955700181 := by
  unfold tailWord_480960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771026168785768136748167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11694701558381024182330889 8771026168785768136748167)
  ·
    refine ⟨13156539253178652205122251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8771026168785768136748167 13156539253178652205122251)
    ·
      refine ⟨19734808879767978307683377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13156539253178652205122251 19734808879767978307683377)
      ·
        refine ⟨14801106659825983730762533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19734808879767978307683377 14801106659825983730762533)
        ·
          refine ⟨2775207498717371949517975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14801106659825983730762533 2775207498717371949517975)
          ·
            refine ⟨4162811248076057924276963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775207498717371949517975 4162811248076057924276963)
            ·
              refine ⟨6244216872114086886415445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4162811248076057924276963 6244216872114086886415445)
              ·
                refine ⟨73174416470086955700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6244216872114086886415445 73174416470086955700181)
                ·
                  rfl

theorem cell20_480960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_480960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480960 prefixEnd_480960 := by exact prefixLift 480960
  have htrace : WordTrace (prefixWord ++ tailWord_480960) baseStart_480960 baseEnd_480960 := by
    simpa [prefixWord, tailWord_480960, baseEnd_480960] using wordTrace_append hprefix tailTrace_480960
  have hstable : (prefixWord ++ tailWord_480960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480960).length < 2 ^ (prefixWord ++ tailWord_480960).sum := by decide
  have hdescent : baseEnd_480960 < baseStart_480960 := by decide
  rcases family_descends (prefixWord ++ tailWord_480960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480980 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_480980 : Nat := 118140960795 + 480980 * 2 ^ 59
def prefixEnd_480980 : Nat := 4983230072969 + 3 ^ 40 * 480980 * 2
def baseEnd_480980 : Nat := 219532377955229686433795

theorem tailTrace_480980 : CollatzResearch.WordTrace tailWord_480980 prefixEnd_480980 219532377955229686433795 := by
  unfold tailWord_480980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771390898749539844612197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11695187864999386459482929 8771390898749539844612197)
  ·
    refine ⟨1644635793515538720864787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8771390898749539844612197 1644635793515538720864787)
    ·
      refine ⟨2466953690273308081297181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644635793515538720864787 2466953690273308081297181)
      ·
        refine ⟨925107633852490530486443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2466953690273308081297181 925107633852490530486443)
        ·
          refine ⟨1387661450778735795729665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925107633852490530486443 1387661450778735795729665)
          ·
            refine ⟨1040746088084051846797249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1387661450778735795729665 1040746088084051846797249)
            ·
              refine ⟨780559566063038885097937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040746088084051846797249 780559566063038885097937)
              ·
                refine ⟨585419674547279163823453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780559566063038885097937 585419674547279163823453)
                ·
                  refine ⟨219532377955229686433795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585419674547279163823453 219532377955229686433795)
                  ·
                    rfl

theorem cell20_480980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_480980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480980 prefixEnd_480980 := by exact prefixLift 480980
  have htrace : WordTrace (prefixWord ++ tailWord_480980) baseStart_480980 baseEnd_480980 := by
    simpa [prefixWord, tailWord_480980, baseEnd_480980] using wordTrace_append hprefix tailTrace_480980
  have hstable : (prefixWord ++ tailWord_480980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480980).length < 2 ^ (prefixWord ++ tailWord_480980).sum := by decide
  have hdescent : baseEnd_480980 < baseStart_480980 := by decide
  rcases family_descends (prefixWord ++ tailWord_480980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480991 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_480991 : Nat := 118140960795 + 480991 * 2 ^ 59
def prefixEnd_480991 : Nat := 4983230072969 + 3 ^ 40 * 480991 * 2
def baseEnd_480991 : Nat := 219537398654962537067083

theorem tailTrace_480991 : CollatzResearch.WordTrace tailWord_480991 prefixEnd_480991 219537398654962537067083 := by
  unfold tailWord_480991
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543183000459228567874827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11695455333639485711916551 17543183000459228567874827)
  ·
    refine ⟨26314774500688842851812241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17543183000459228567874827 26314774500688842851812241)
    ·
      refine ⟨19736080875516632138859181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26314774500688842851812241 19736080875516632138859181)
      ·
        refine ⟨7401030328318737052072193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19736080875516632138859181 7401030328318737052072193)
        ·
          refine ⟨5550772746239052789054145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7401030328318737052072193 5550772746239052789054145)
          ·
            refine ⟨4163079559679289591790609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5550772746239052789054145 4163079559679289591790609)
            ·
              refine ⟨3122309669759467193842957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163079559679289591790609 3122309669759467193842957)
              ·
                refine ⟨1170866126159800197691109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3122309669759467193842957 1170866126159800197691109)
                ·
                  refine ⟨219537398654962537067083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170866126159800197691109 219537398654962537067083)
                  ·
                    rfl

theorem cell20_480991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_480991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_480991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_480991 prefixEnd_480991 := by exact prefixLift 480991
  have htrace : WordTrace (prefixWord ++ tailWord_480991) baseStart_480991 baseEnd_480991 := by
    simpa [prefixWord, tailWord_480991, baseEnd_480991] using wordTrace_append hprefix tailTrace_480991
  have hstable : (prefixWord ++ tailWord_480991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480991).length < 2 ^ (prefixWord ++ tailWord_480991).sum := by decide
  have hdescent : baseEnd_480991 < baseStart_480991 := by decide
  rcases family_descends (prefixWord ++ tailWord_480991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481042 : List Nat := [3, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_481042 : Nat := 118140960795 + 481042 * 2 ^ 59
def prefixEnd_481042 : Nat := 4983230072969 + 3 ^ 40 * 481042 * 2
def baseEnd_481042 : Nat := 219560676444633026366875

theorem tailTrace_481042 : CollatzResearch.WordTrace tailWord_481042 prefixEnd_481042 219560676444633026366875 := by
  unfold tailWord_481042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386260780818616069495345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11696695415516309518654253 4386260780818616069495345)
  ·
    refine ⟨3289695585613962052121509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4386260780818616069495345 3289695585613962052121509)
    ·
      refine ⟨616817922302617884772783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3289695585613962052121509 616817922302617884772783)
      ·
        refine ⟨925226883453926827159175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616817922302617884772783 925226883453926827159175)
        ·
          refine ⟨1387840325180890240738763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925226883453926827159175 1387840325180890240738763)
          ·
            refine ⟨2081760487771335361108145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387840325180890240738763 2081760487771335361108145)
            ·
              refine ⟨1561320365828501520831109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081760487771335361108145 1561320365828501520831109)
              ·
                refine ⟨292747568592844035155833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1561320365828501520831109 292747568592844035155833)
                ·
                  refine ⟨219560676444633026366875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292747568592844035155833 219560676444633026366875)
                  ·
                    rfl

theorem cell20_481042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_481042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481042 prefixEnd_481042 := by exact prefixLift 481042
  have htrace : WordTrace (prefixWord ++ tailWord_481042) baseStart_481042 baseEnd_481042 := by
    simpa [prefixWord, tailWord_481042, baseEnd_481042] using wordTrace_append hprefix tailTrace_481042
  have hstable : (prefixWord ++ tailWord_481042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481042).length < 2 ^ (prefixWord ++ tailWord_481042).sum := by decide
  have hdescent : baseEnd_481042 < baseStart_481042 := by decide
  rcases family_descends (prefixWord ++ tailWord_481042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481070 : List Nat := [4, 1, 3, 2, 2, 1, 1, 6]
def baseStart_481070 : Nat := 118140960795 + 481070 * 2 ^ 59
def prefixEnd_481070 : Nat := 4983230072969 + 3 ^ 40 * 481070 * 2
def baseEnd_481070 : Nat := 73191152135863124477809

theorem tailTrace_481070 : CollatzResearch.WordTrace tailWord_481070 prefixEnd_481070 73191152135863124477809 := by
  unfold tailWord_481070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193258045896628132500083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11697376244782016706667109 2193258045896628132500083)
  ·
    refine ⟨3289887068844942198750125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193258045896628132500083 3289887068844942198750125)
    ·
      refine ⟨1233707650816853324531297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3289887068844942198750125 1233707650816853324531297)
      ·
        refine ⟨925280738112639993398473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233707650816853324531297 925280738112639993398473)
        ·
          refine ⟨693960553584479995048855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925280738112639993398473 693960553584479995048855)
          ·
            refine ⟨1040940830376719992573283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693960553584479995048855 1040940830376719992573283)
            ·
              refine ⟨1561411245565079988859925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040940830376719992573283 1561411245565079988859925)
              ·
                refine ⟨73191152135863124477809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1561411245565079988859925 73191152135863124477809)
                ·
                  rfl

theorem cell20_481070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_481070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481070 prefixEnd_481070 := by exact prefixLift 481070
  have htrace : WordTrace (prefixWord ++ tailWord_481070) baseStart_481070 baseEnd_481070 := by
    simpa [prefixWord, tailWord_481070, baseEnd_481070] using wordTrace_append hprefix tailTrace_481070
  have hstable : (prefixWord ++ tailWord_481070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481070).length < 2 ^ (prefixWord ++ tailWord_481070).sum := by decide
  have hdescent : baseEnd_481070 < baseStart_481070 := by decide
  rcases family_descends (prefixWord ++ tailWord_481070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481094 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_481094 : Nat := 118140960795 + 481094 * 2 ^ 59
def prefixEnd_481094 : Nat := 4983230072969 + 3 ^ 40 * 481094 * 2
def baseEnd_481094 : Nat := 219584410661551956633329

theorem tailTrace_481094 : CollatzResearch.WordTrace tailWord_481094 prefixEnd_481094 219584410661551956633329 := by
  unfold tailWord_481094
  simp only [CollatzResearch.WordTrace]
  refine ⟨548341866221439911214823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11697959812724051439249557 548341866221439911214823)
  ·
    refine ⟨822512799332159866822235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548341866221439911214823 822512799332159866822235)
    ·
      refine ⟨1233769198998239800233353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822512799332159866822235 1233769198998239800233353)
      ·
        refine ⟨925326899248679850175015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233769198998239800233353 925326899248679850175015)
        ·
          refine ⟨1387990348873019775262523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925326899248679850175015 1387990348873019775262523)
          ·
            refine ⟨2081985523309529662893785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387990348873019775262523 2081985523309529662893785)
            ·
              refine ⟨1561489142482147247170339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081985523309529662893785 1561489142482147247170339)
              ·
                refine ⟨2342233713723220870755509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561489142482147247170339 2342233713723220870755509)
                ·
                  refine ⟨219584410661551956633329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2342233713723220870755509 219584410661551956633329)
                  ·
                    rfl

theorem cell20_481094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_481094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481094 prefixEnd_481094 := by exact prefixLift 481094
  have htrace : WordTrace (prefixWord ++ tailWord_481094) baseStart_481094 baseEnd_481094 := by
    simpa [prefixWord, tailWord_481094, baseEnd_481094] using wordTrace_append hprefix tailTrace_481094
  have hstable : (prefixWord ++ tailWord_481094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481094).length < 2 ^ (prefixWord ++ tailWord_481094).sum := by decide
  have hdescent : baseEnd_481094 < baseStart_481094 := by decide
  rcases family_descends (prefixWord ++ tailWord_481094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481098 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_481098 : Nat := 118140960795 + 481098 * 2 ^ 59
def prefixEnd_481098 : Nat := 4983230072969 + 3 ^ 40 * 481098 * 2
def baseEnd_481098 : Nat := 219586236370545720499979

theorem tailTrace_481098 : CollatzResearch.WordTrace tailWord_481098 prefixEnd_481098 219586236370545720499979 := by
  unfold tailWord_481098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386771402767896460504987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11698057074047723894679965 4386771402767896460504987)
  ·
    refine ⟨6580157104151844690757481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4386771402767896460504987 6580157104151844690757481)
    ·
      refine ⟨4935117828113883518068111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6580157104151844690757481 4935117828113883518068111)
      ·
        refine ⟨7402676742170825277102167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935117828113883518068111 7402676742170825277102167)
        ·
          refine ⟨11104015113256237915653251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402676742170825277102167 11104015113256237915653251)
          ·
            refine ⟨16656022669884356873479877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11104015113256237915653251 16656022669884356873479877)
            ·
              refine ⟨3123004250603316913777477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16656022669884356873479877 3123004250603316913777477)
              ·
                refine ⟨585563296988121921333277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3123004250603316913777477 585563296988121921333277)
                ·
                  refine ⟨219586236370545720499979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585563296988121921333277 219586236370545720499979)
                  ·
                    rfl

theorem cell20_481098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_481098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481098 prefixEnd_481098 := by exact prefixLift 481098
  have htrace : WordTrace (prefixWord ++ tailWord_481098) baseStart_481098 baseEnd_481098 := by
    simpa [prefixWord, tailWord_481098, baseEnd_481098] using wordTrace_append hprefix tailTrace_481098
  have hstable : (prefixWord ++ tailWord_481098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481098).length < 2 ^ (prefixWord ++ tailWord_481098).sum := by decide
  have hdescent : baseEnd_481098 < baseStart_481098 := by decide
  rcases family_descends (prefixWord ++ tailWord_481098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481101 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_481101 : Nat := 118140960795 + 481101 * 2 ^ 59
def prefixEnd_481101 : Nat := 4983230072969 + 3 ^ 40 * 481101 * 2
def baseEnd_481101 : Nat := 219587605652291043399967

theorem tailTrace_481101 : CollatzResearch.WordTrace tailWord_481101 prefixEnd_481101 219587605652291043399967 := by
  unfold tailWord_481101
  simp only [CollatzResearch.WordTrace]
  refine ⟨17547195030060717354379157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11698130020040478236252771 17547195030060717354379157)
  ·
    refine ⟨822524767034096125986523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17547195030060717354379157 822524767034096125986523)
    ·
      refine ⟨1233787150551144188979785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822524767034096125986523 1233787150551144188979785)
      ·
        refine ⟨925340362913358141734839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233787150551144188979785 925340362913358141734839)
        ·
          refine ⟨1388010544370037212602259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925340362913358141734839 1388010544370037212602259)
          ·
            refine ⟨2082015816555055818903389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388010544370037212602259 2082015816555055818903389)
            ·
              refine ⟨780755931208145932088771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2082015816555055818903389 780755931208145932088771)
              ·
                refine ⟨1171133896812218898133157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780755931208145932088771 1171133896812218898133157)
                ·
                  refine ⟨219587605652291043399967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171133896812218898133157 219587605652291043399967)
                  ·
                    rfl

theorem cell20_481101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_481101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481101 prefixEnd_481101 := by exact prefixLift 481101
  have htrace : WordTrace (prefixWord ++ tailWord_481101) baseStart_481101 baseEnd_481101 := by
    simpa [prefixWord, tailWord_481101, baseEnd_481101] using wordTrace_append hprefix tailTrace_481101
  have hstable : (prefixWord ++ tailWord_481101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481101).length < 2 ^ (prefixWord ++ tailWord_481101).sum := by decide
  have hdescent : baseEnd_481101 < baseStart_481101 := by decide
  rcases family_descends (prefixWord ++ tailWord_481101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481111 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 3]
def baseStart_481111 : Nat := 118140960795 + 481111 * 2 ^ 59
def prefixEnd_481111 : Nat := 4983230072969 + 3 ^ 40 * 481111 * 2
def baseEnd_481111 : Nat := 219592169924775453066593

theorem tailTrace_481111 : CollatzResearch.WordTrace tailWord_481111 prefixEnd_481111 219592169924775453066593 := by
  unfold tailWord_481111
  simp only [CollatzResearch.WordTrace]
  refine ⟨17547559760024489062243187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11698373173349659374828791 17547559760024489062243187)
  ·
    refine ⟨26321339640036733593364781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17547559760024489062243187 26321339640036733593364781)
    ·
      refine ⟨9870502365013775097511793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26321339640036733593364781 9870502365013775097511793)
      ·
        refine ⟨7402876773760331323133845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9870502365013775097511793 7402876773760331323133845)
        ·
          refine ⟨347009848770015530771899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7402876773760331323133845 347009848770015530771899)
          ·
            refine ⟨520514773155023296157849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347009848770015530771899 520514773155023296157849)
            ·
              refine ⟨390386079866267472118387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520514773155023296157849 390386079866267472118387)
              ·
                refine ⟨585579119799401208177581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390386079866267472118387 585579119799401208177581)
                ·
                  refine ⟨219592169924775453066593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585579119799401208177581 219592169924775453066593)
                  ·
                    rfl

theorem cell20_481111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 3].length) (baseStart_481111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481111 prefixEnd_481111 := by exact prefixLift 481111
  have htrace : WordTrace (prefixWord ++ tailWord_481111) baseStart_481111 baseEnd_481111 := by
    simpa [prefixWord, tailWord_481111, baseEnd_481111] using wordTrace_append hprefix tailTrace_481111
  have hstable : (prefixWord ++ tailWord_481111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481111).length < 2 ^ (prefixWord ++ tailWord_481111).sum := by decide
  have hdescent : baseEnd_481111 < baseStart_481111 := by decide
  rcases family_descends (prefixWord ++ tailWord_481111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481181 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_481181 : Nat := 118140960795 + 481181 * 2 ^ 59
def prefixEnd_481181 : Nat := 4983230072969 + 3 ^ 40 * 481181 * 2
def baseEnd_481181 : Nat := 219624119832166320732973

theorem tailTrace_481181 : CollatzResearch.WordTrace tailWord_481181 prefixEnd_481181 219624119832166320732973 := by
  unfold tailWord_481181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550112869770891017291397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11700075246513927344860931 17550112869770891017291397)
  ·
    refine ⟨3290646163082042065742137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17550112869770891017291397 3290646163082042065742137)
    ·
      refine ⟨2467984622311531549306603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3290646163082042065742137 2467984622311531549306603)
      ·
        refine ⟨3701976933467297323959905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467984622311531549306603 3701976933467297323959905)
        ·
          refine ⟨2776482700100472992969929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701976933467297323959905 2776482700100472992969929)
          ·
            refine ⟨2082362025075354744727447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776482700100472992969929 2082362025075354744727447)
            ·
              refine ⟨3123543037613032117091171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082362025075354744727447 3123543037613032117091171)
              ·
                refine ⟨4685314556419548175636757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3123543037613032117091171 4685314556419548175636757)
                ·
                  refine ⟨219624119832166320732973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4685314556419548175636757 219624119832166320732973)
                  ·
                    rfl

theorem cell20_481181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_481181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481181 prefixEnd_481181 := by exact prefixLift 481181
  have htrace : WordTrace (prefixWord ++ tailWord_481181) baseStart_481181 baseEnd_481181 := by
    simpa [prefixWord, tailWord_481181, baseEnd_481181] using wordTrace_append hprefix tailTrace_481181
  have hstable : (prefixWord ++ tailWord_481181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481181).length < 2 ^ (prefixWord ++ tailWord_481181).sum := by decide
  have hdescent : baseEnd_481181 < baseStart_481181 := by decide
  rcases family_descends (prefixWord ++ tailWord_481181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481204 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 3]
def baseStart_481204 : Nat := 118140960795 + 481204 * 2 ^ 59
def prefixEnd_481204 : Nat := 4983230072969 + 3 ^ 40 * 481204 * 2
def baseEnd_481204 : Nat := 219634617658880462966213

theorem tailTrace_481204 : CollatzResearch.WordTrace tailWord_481204 prefixEnd_481204 219634617658880462966213 := by
  unfold tailWord_481204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775475874343782972689333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11700634499125043963585777 8775475874343782972689333)
  ·
    refine ⟨822700863219729653689625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8775475874343782972689333 822700863219729653689625)
    ·
      refine ⟨617025647414797240267219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 822700863219729653689625 617025647414797240267219)
      ·
        refine ⟨925538471122195860400829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617025647414797240267219 925538471122195860400829)
        ·
          refine ⟨347076926670823447650311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 925538471122195860400829 347076926670823447650311)
          ·
            refine ⟨520615390006235171475467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347076926670823447650311 520615390006235171475467)
            ·
              refine ⟨780923085009352757213201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520615390006235171475467 780923085009352757213201)
              ·
                refine ⟨585692313757014567909901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780923085009352757213201 585692313757014567909901)
                ·
                  refine ⟨219634617658880462966213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585692313757014567909901 219634617658880462966213)
                  ·
                    rfl

theorem cell20_481204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_481204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481204 prefixEnd_481204 := by exact prefixLift 481204
  have htrace : WordTrace (prefixWord ++ tailWord_481204) baseStart_481204 baseEnd_481204 := by
    simpa [prefixWord, tailWord_481204, baseEnd_481204] using wordTrace_append hprefix tailTrace_481204
  have hstable : (prefixWord ++ tailWord_481204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481204).length < 2 ^ (prefixWord ++ tailWord_481204).sum := by decide
  have hdescent : baseEnd_481204 < baseStart_481204 := by decide
  rcases family_descends (prefixWord ++ tailWord_481204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481270 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_481270 : Nat := 118140960795 + 481270 * 2 ^ 59
def prefixEnd_481270 : Nat := 4983230072969 + 3 ^ 40 * 481270 * 2
def baseEnd_481270 : Nat := 219664741857277566765943

theorem tailTrace_481270 : CollatzResearch.WordTrace tailWord_481270 prefixEnd_481270 219664741857277566765943 := by
  unfold tailWord_481270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097084935403028701080079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11702239310965639478187509 1097084935403028701080079)
  ·
    refine ⟨1645627403104543051620119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1097084935403028701080079 1645627403104543051620119)
    ·
      refine ⟨2468441104656814577430179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645627403104543051620119 2468441104656814577430179)
      ·
        refine ⟨3702661656985221866145269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2468441104656814577430179 3702661656985221866145269)
        ·
          refine ⟨347124530342364549951119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3702661656985221866145269 347124530342364549951119)
          ·
            refine ⟨520686795513546824926679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347124530342364549951119 520686795513546824926679)
            ·
              refine ⟨781030193270320237390019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520686795513546824926679 781030193270320237390019)
              ·
                refine ⟨1171545289905480356085029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781030193270320237390019 1171545289905480356085029)
                ·
                  refine ⟨219664741857277566765943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171545289905480356085029 219664741857277566765943)
                  ·
                    rfl

theorem cell20_481270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_481270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481270 prefixEnd_481270 := by exact prefixLift 481270
  have htrace : WordTrace (prefixWord ++ tailWord_481270) baseStart_481270 baseEnd_481270 := by
    simpa [prefixWord, tailWord_481270, baseEnd_481270] using wordTrace_append hprefix tailTrace_481270
  have hstable : (prefixWord ++ tailWord_481270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481270).length < 2 ^ (prefixWord ++ tailWord_481270).sum := by decide
  have hdescent : baseEnd_481270 < baseStart_481270 := by decide
  rcases family_descends (prefixWord ++ tailWord_481270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481284 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_481284 : Nat := 118140960795 + 481284 * 2 ^ 59
def prefixEnd_481284 : Nat := 4983230072969 + 3 ^ 40 * 481284 * 2
def baseEnd_481284 : Nat := 219671131838755740299219

theorem tailTrace_481284 : CollatzResearch.WordTrace tailWord_481284 prefixEnd_481284 219671131838755740299219 := by
  unfold tailWord_481284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776934794198869804145453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11702579725598493072193937 8776934794198869804145453)
  ·
    refine ⟨3291350547824576176554545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8776934794198869804145453 3291350547824576176554545)
    ·
      refine ⟨2468512910868432132415909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3291350547824576176554545 2468512910868432132415909)
      ·
        refine ⟨462846170787831024827983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2468512910868432132415909 462846170787831024827983)
        ·
          refine ⟨694269256181746537241975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462846170787831024827983 694269256181746537241975)
          ·
            refine ⟨1041403884272619805862963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694269256181746537241975 1041403884272619805862963)
            ·
              refine ⟨1562105826408929708794445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041403884272619805862963 1562105826408929708794445)
              ·
                refine ⟨585789684903348640797917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562105826408929708794445 585789684903348640797917)
                ·
                  refine ⟨219671131838755740299219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585789684903348640797917 219671131838755740299219)
                  ·
                    rfl

theorem cell20_481284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_481284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481284 prefixEnd_481284 := by exact prefixLift 481284
  have htrace : WordTrace (prefixWord ++ tailWord_481284) baseStart_481284 baseEnd_481284 := by
    simpa [prefixWord, tailWord_481284, baseEnd_481284] using wordTrace_append hprefix tailTrace_481284
  have hstable : (prefixWord ++ tailWord_481284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481284).length < 2 ^ (prefixWord ++ tailWord_481284).sum := by decide
  have hdescent : baseEnd_481284 < baseStart_481284 := by decide
  rcases family_descends (prefixWord ++ tailWord_481284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481288 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_481288 : Nat := 118140960795 + 481288 * 2 ^ 59
def prefixEnd_481288 : Nat := 4983230072969 + 3 ^ 40 * 481288 * 2
def baseEnd_481288 : Nat := 219672957547749504165869

theorem tailTrace_481288 : CollatzResearch.WordTrace tailWord_481288 prefixEnd_481288 219672957547749504165869 := by
  unfold tailWord_481288
  simp only [CollatzResearch.WordTrace]
  refine ⟨8777007740191624145718259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11702676986922165527624345 8777007740191624145718259)
  ·
    refine ⟨13165511610287436218577389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8777007740191624145718259 13165511610287436218577389)
    ·
      refine ⟨4937066853857788581966521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13165511610287436218577389 4937066853857788581966521)
      ·
        refine ⟨3702800140393341436474891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4937066853857788581966521 3702800140393341436474891)
        ·
          refine ⟨5554200210590012154712337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702800140393341436474891 5554200210590012154712337)
          ·
            refine ⟨4165650157942509116034253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5554200210590012154712337 4165650157942509116034253)
            ·
              refine ⟨1562118809228440918512845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4165650157942509116034253 1562118809228440918512845)
              ·
                refine ⟨585794553460665344442317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1562118809228440918512845 585794553460665344442317)
                ·
                  refine ⟨219672957547749504165869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585794553460665344442317 219672957547749504165869)
                  ·
                    rfl

theorem cell20_481288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_481288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481288 prefixEnd_481288 := by exact prefixLift 481288
  have htrace : WordTrace (prefixWord ++ tailWord_481288) baseStart_481288 baseEnd_481288 := by
    simpa [prefixWord, tailWord_481288, baseEnd_481288] using wordTrace_append hprefix tailTrace_481288
  have hstable : (prefixWord ++ tailWord_481288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481288).length < 2 ^ (prefixWord ++ tailWord_481288).sum := by decide
  have hdescent : baseEnd_481288 < baseStart_481288 := by decide
  rcases family_descends (prefixWord ++ tailWord_481288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481319 : List Nat := [1, 1, 7, 1, 2, 8]
def baseStart_481319 : Nat := 118140960795 + 481319 * 2 ^ 59
def prefixEnd_481319 : Nat := 4983230072969 + 3 ^ 40 * 481319 * 2
def baseEnd_481319 : Nat := 8136559510831524967867

theorem tailTrace_481319 : CollatzResearch.WordTrace tailWord_481319 prefixEnd_481319 8136559510831524967867 := by
  unfold tailWord_481319
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555146143270940585815011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11703430762180627057210007 17555146143270940585815011)
  ·
    refine ⟨26332719214906410878722517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17555146143270940585815011 26332719214906410878722517)
    ·
      refine ⟨617173106599369004970059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26332719214906410878722517 617173106599369004970059)
      ·
        refine ⟨925759659899053507455089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617173106599369004970059 925759659899053507455089)
        ·
          refine ⟨694319744924290130591317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925759659899053507455089 694319744924290130591317)
          ·
            refine ⟨8136559510831524967867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 694319744924290130591317 8136559510831524967867)
            ·
              rfl

theorem cell20_481319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 8].length) (baseStart_481319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481319 prefixEnd_481319 := by exact prefixLift 481319
  have htrace : WordTrace (prefixWord ++ tailWord_481319) baseStart_481319 baseEnd_481319 := by
    simpa [prefixWord, tailWord_481319, baseEnd_481319] using wordTrace_append hprefix tailTrace_481319
  have hstable : (prefixWord ++ tailWord_481319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481319).length < 2 ^ (prefixWord ++ tailWord_481319).sum := by decide
  have hdescent : baseEnd_481319 < baseStart_481319 := by decide
  rcases family_descends (prefixWord ++ tailWord_481319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481329 : List Nat := [1, 2, 2, 3, 1, 3, 4, 2, 2]
def baseStart_481329 : Nat := 118140960795 + 481329 * 2 ^ 59
def prefixEnd_481329 : Nat := 4983230072969 + 3 ^ 40 * 481329 * 2
def baseEnd_481329 : Nat := 219691671064935583799035

theorem tailTrace_481329 : CollatzResearch.WordTrace tailWord_481329 prefixEnd_481329 219691671064935583799035 := by
  unfold tailWord_481329
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555510873234712293679041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11703673915489808195786027 17555510873234712293679041)
  ·
    refine ⟨13166633154926034220259281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17555510873234712293679041 13166633154926034220259281)
    ·
      refine ⟨9874974866194525665194461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13166633154926034220259281 9874974866194525665194461)
      ·
        refine ⟨3703115574822947124447923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9874974866194525665194461 3703115574822947124447923)
        ·
          refine ⟨5554673362234420686671885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703115574822947124447923 5554673362234420686671885)
          ·
            refine ⟨2083002510837907757501957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5554673362234420686671885 2083002510837907757501957)
            ·
              refine ⟨390562970782107704531617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2083002510837907757501957 390562970782107704531617)
              ·
                refine ⟨292922228086580778398713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390562970782107704531617 292922228086580778398713)
                ·
                  refine ⟨219691671064935583799035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292922228086580778398713 219691671064935583799035)
                  ·
                    rfl

theorem cell20_481329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_481329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481329 prefixEnd_481329 := by exact prefixLift 481329
  have htrace : WordTrace (prefixWord ++ tailWord_481329) baseStart_481329 baseEnd_481329 := by
    simpa [prefixWord, tailWord_481329, baseEnd_481329] using wordTrace_append hprefix tailTrace_481329
  have hstable : (prefixWord ++ tailWord_481329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481329).length < 2 ^ (prefixWord ++ tailWord_481329).sum := by decide
  have hdescent : baseEnd_481329 < baseStart_481329 := by decide
  rcases family_descends (prefixWord ++ tailWord_481329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481336 : List Nat := [2, 1, 2, 1, 7, 1, 1, 5]
def baseStart_481336 : Nat := 118140960795 + 481336 * 2 ^ 59
def prefixEnd_481336 : Nat := 4983230072969 + 3 ^ 40 * 481336 * 2
def baseEnd_481336 : Nat := 73231622018558223521891

theorem tailTrace_481336 : CollatzResearch.WordTrace tailWord_481336 prefixEnd_481336 73231622018558223521891 := by
  unfold tailWord_481336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8777883092104676244591931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11703844122806234992789241 8777883092104676244591931)
  ·
    refine ⟨13166824638157014366887897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8777883092104676244591931 13166824638157014366887897)
    ·
      refine ⟨9875118478617760775165923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13166824638157014366887897 9875118478617760775165923)
      ·
        refine ⟨14812677717926641162748885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9875118478617760775165923 14812677717926641162748885)
        ·
          refine ⟨347172134013905652251927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14812677717926641162748885 347172134013905652251927)
          ·
            refine ⟨520758201020858478377891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347172134013905652251927 520758201020858478377891)
            ·
              refine ⟨781137301531287717566837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520758201020858478377891 781137301531287717566837)
              ·
                refine ⟨73231622018558223521891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 781137301531287717566837 73231622018558223521891)
                ·
                  rfl

theorem cell20_481336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_481336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481336 prefixEnd_481336 := by exact prefixLift 481336
  have htrace : WordTrace (prefixWord ++ tailWord_481336) baseStart_481336 baseEnd_481336 := by
    simpa [prefixWord, tailWord_481336, baseEnd_481336] using wordTrace_append hprefix tailTrace_481336
  have hstable : (prefixWord ++ tailWord_481336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481336).length < 2 ^ (prefixWord ++ tailWord_481336).sum := by decide
  have hdescent : baseEnd_481336 < baseStart_481336 := by decide
  rcases family_descends (prefixWord ++ tailWord_481336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481381 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 3]
def baseStart_481381 : Nat := 118140960795 + 481381 * 2 ^ 59
def prefixEnd_481381 : Nat := 4983230072969 + 3 ^ 40 * 481381 * 2
def baseEnd_481381 : Nat := 219715405281854514065489

theorem tailTrace_481381 : CollatzResearch.WordTrace tailWord_481381 prefixEnd_481381 219715405281854514065489 := by
  unfold tailWord_481381
  simp only [CollatzResearch.WordTrace]
  refine ⟨17557407469046325174571997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11704938312697550116381331 17557407469046325174571997)
  ·
    refine ⟨6584027800892371940464499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17557407469046325174571997 6584027800892371940464499)
    ·
      refine ⟨9876041701338557910696749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584027800892371940464499 9876041701338557910696749)
      ·
        refine ⟨3703515638001959216511281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9876041701338557910696749 3703515638001959216511281)
        ·
          refine ⟨2777636728501469412383461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3703515638001959216511281 2777636728501469412383461)
          ·
            refine ⟨520806886594025514821899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2777636728501469412383461 520806886594025514821899)
            ·
              refine ⟨781210329891038272232849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520806886594025514821899 781210329891038272232849)
              ·
                refine ⟨585907747418278704174637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781210329891038272232849 585907747418278704174637)
                ·
                  refine ⟨219715405281854514065489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585907747418278704174637 219715405281854514065489)
                  ·
                    rfl

theorem cell20_481381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_481381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481381 prefixEnd_481381 := by exact prefixLift 481381
  have htrace : WordTrace (prefixWord ++ tailWord_481381) baseStart_481381 baseEnd_481381 := by
    simpa [prefixWord, tailWord_481381, baseEnd_481381] using wordTrace_append hprefix tailTrace_481381
  have hstable : (prefixWord ++ tailWord_481381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481381).length < 2 ^ (prefixWord ++ tailWord_481381).sum := by decide
  have hdescent : baseEnd_481381 < baseStart_481381 := by decide
  rcases family_descends (prefixWord ++ tailWord_481381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481385 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_481385 : Nat := 118140960795 + 481385 * 2 ^ 59
def prefixEnd_481385 : Nat := 4983230072969 + 3 ^ 40 * 481385 * 2
def baseEnd_481385 : Nat := 219717230990848277932139

theorem tailTrace_481385 : CollatzResearch.WordTrace tailWord_481385 prefixEnd_481385 219717230990848277932139 := by
  unfold tailWord_481385
  simp only [CollatzResearch.WordTrace]
  refine ⟨17557553361031833857717609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11705035574021222571811739 17557553361031833857717609)
  ·
    refine ⟨13168165020773875393288207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17557553361031833857717609 13168165020773875393288207)
    ·
      refine ⟨19752247531160813089932311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13168165020773875393288207 19752247531160813089932311)
      ·
        refine ⟨29628371296741219634898467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19752247531160813089932311 29628371296741219634898467)
        ·
          refine ⟨44442556945111829452347701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29628371296741219634898467 44442556945111829452347701)
          ·
            refine ⟨4166489713604234011157597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44442556945111829452347701 4166489713604234011157597)
            ·
              refine ⟨1562433642601587754184099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4166489713604234011157597 1562433642601587754184099)
              ·
                refine ⟨2343650463902381631276149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562433642601587754184099 2343650463902381631276149)
                ·
                  refine ⟨219717230990848277932139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2343650463902381631276149 219717230990848277932139)
                  ·
                    rfl

theorem cell20_481385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_481385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481385 prefixEnd_481385 := by exact prefixLift 481385
  have htrace : WordTrace (prefixWord ++ tailWord_481385) baseStart_481385 baseEnd_481385 := by
    simpa [prefixWord, tailWord_481385, baseEnd_481385] using wordTrace_append hprefix tailTrace_481385
  have hstable : (prefixWord ++ tailWord_481385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481385).length < 2 ^ (prefixWord ++ tailWord_481385).sum := by decide
  have hdescent : baseEnd_481385 < baseStart_481385 := by decide
  rcases family_descends (prefixWord ++ tailWord_481385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481388 : List Nat := [2, 2, 1, 1, 3, 3, 2, 4, 2]
def baseStart_481388 : Nat := 118140960795 + 481388 * 2 ^ 59
def prefixEnd_481388 : Nat := 4983230072969 + 3 ^ 40 * 481388 * 2
def baseEnd_481388 : Nat := 219718600272593600832127

theorem tailTrace_481388 : CollatzResearch.WordTrace tailWord_481388 prefixEnd_481388 219718600272593600832127 := by
  unfold tailWord_481388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8778831390010482685038409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11705108520013976913384545 8778831390010482685038409)
  ·
    refine ⟨6584123542507862013778807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8778831390010482685038409 6584123542507862013778807)
    ·
      refine ⟨9876185313761793020668211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584123542507862013778807 9876185313761793020668211)
      ·
        refine ⟨14814277970642689531002317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876185313761793020668211 14814277970642689531002317)
        ·
          refine ⟨5555354238991008574125869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14814277970642689531002317 5555354238991008574125869)
          ·
            refine ⟨2083257839621628215297201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5555354238991008574125869 2083257839621628215297201)
            ·
              refine ⟨1562443379716221161472901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083257839621628215297201 1562443379716221161472901)
              ·
                refine ⟨292958133696791467776169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1562443379716221161472901 292958133696791467776169)
                ·
                  refine ⟨219718600272593600832127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292958133696791467776169 219718600272593600832127)
                  ·
                    rfl

theorem cell20_481388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_481388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481388 prefixEnd_481388 := by exact prefixLift 481388
  have htrace : WordTrace (prefixWord ++ tailWord_481388) baseStart_481388 baseEnd_481388 := by
    simpa [prefixWord, tailWord_481388, baseEnd_481388] using wordTrace_append hprefix tailTrace_481388
  have hstable : (prefixWord ++ tailWord_481388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481388).length < 2 ^ (prefixWord ++ tailWord_481388).sum := by decide
  have hdescent : baseEnd_481388 < baseStart_481388 := by decide
  rcases family_descends (prefixWord ++ tailWord_481388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481398 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_481398 : Nat := 118140960795 + 481398 * 2 ^ 59
def prefixEnd_481398 : Nat := 4983230072969 + 3 ^ 40 * 481398 * 2
def baseEnd_481398 : Nat := 219723164545078010498753

theorem tailTrace_481398 : CollatzResearch.WordTrace tailWord_481398 prefixEnd_481398 219723164545078010498753 := by
  unfold tailWord_481398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097376719374046067371303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11705351673323158051960565 1097376719374046067371303)
  ·
    refine ⟨1646065079061069101056955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1097376719374046067371303 1646065079061069101056955)
    ·
      refine ⟨2469097618591603651585433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646065079061069101056955 2469097618591603651585433)
      ·
        refine ⟨1851823213943702738689075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469097618591603651585433 1851823213943702738689075)
        ·
          refine ⟨2777734820915554108033613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851823213943702738689075 2777734820915554108033613)
          ·
            refine ⟨1041650557843332790512605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2777734820915554108033613 1041650557843332790512605)
            ·
              refine ⟨390618959191249796442227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1041650557843332790512605 390618959191249796442227)
              ·
                refine ⟨585928438786874694663341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390618959191249796442227 585928438786874694663341)
                ·
                  refine ⟨219723164545078010498753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585928438786874694663341 219723164545078010498753)
                  ·
                    rfl

theorem cell20_481398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_481398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481398 prefixEnd_481398 := by exact prefixLift 481398
  have htrace : WordTrace (prefixWord ++ tailWord_481398) baseStart_481398 baseEnd_481398 := by
    simpa [prefixWord, tailWord_481398, baseEnd_481398] using wordTrace_append hprefix tailTrace_481398
  have hstable : (prefixWord ++ tailWord_481398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481398).length < 2 ^ (prefixWord ++ tailWord_481398).sum := by decide
  have hdescent : baseEnd_481398 < baseStart_481398 := by decide
  rcases family_descends (prefixWord ++ tailWord_481398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481422 : List Nat := [4, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_481422 : Nat := 118140960795 + 481422 * 2 ^ 59
def prefixEnd_481422 : Nat := 4983230072969 + 3 ^ 40 * 481422 * 2
def baseEnd_481422 : Nat := 219734118799040593698655

theorem tailTrace_481422 : CollatzResearch.WordTrace tailWord_481422 prefixEnd_481422 219734118799040593698655 := by
  unfold tailWord_481422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194862857737223647101815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11705935241265192784543013 2194862857737223647101815)
  ·
    refine ⟨3292294286605835470652723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2194862857737223647101815 3292294286605835470652723)
    ·
      refine ⟨4938441429908753205979085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292294286605835470652723 4938441429908753205979085)
      ·
        refine ⟨1851915536215782452242157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4938441429908753205979085 1851915536215782452242157)
        ·
          refine ⟨694468326080918419590809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1851915536215782452242157 694468326080918419590809)
          ·
            refine ⟨520851244560688814693107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694468326080918419590809 520851244560688814693107)
            ·
              refine ⟨781276866841033222039661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520851244560688814693107 781276866841033222039661)
              ·
                refine ⟨292978825065387458264873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781276866841033222039661 292978825065387458264873)
                ·
                  refine ⟨219734118799040593698655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292978825065387458264873 219734118799040593698655)
                  ·
                    rfl

theorem cell20_481422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_481422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481422 prefixEnd_481422 := by exact prefixLift 481422
  have htrace : WordTrace (prefixWord ++ tailWord_481422) baseStart_481422 baseEnd_481422 := by
    simpa [prefixWord, tailWord_481422, baseEnd_481422] using wordTrace_append hprefix tailTrace_481422
  have hstable : (prefixWord ++ tailWord_481422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481422).length < 2 ^ (prefixWord ++ tailWord_481422).sum := by decide
  have hdescent : baseEnd_481422 < baseStart_481422 := by decide
  rcases family_descends (prefixWord ++ tailWord_481422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481450 : List Nat := [3, 1, 5, 1, 2, 1, 2, 5]
def baseStart_481450 : Nat := 118140960795 + 481450 * 2 ^ 59
def prefixEnd_481450 : Nat := 4983230072969 + 3 ^ 40 * 481450 * 2
def baseEnd_481450 : Nat := 73248966253998980255069

theorem tailTrace_481450 : CollatzResearch.WordTrace tailWord_481450 prefixEnd_481450 73248966253998980255069 := by
  unfold tailWord_481450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389981026449087489708451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11706616070530899972555869 4389981026449087489708451)
  ·
    refine ⟨6584971539673631234562677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4389981026449087489708451 6584971539673631234562677)
    ·
      refine ⟨617341081844402928240251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6584971539673631234562677 617341081844402928240251)
      ·
        refine ⟨926011622766604392360377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617341081844402928240251 926011622766604392360377)
        ·
          refine ⟨694508717074953294270283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926011622766604392360377 694508717074953294270283)
          ·
            refine ⟨1041763075612429941405425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694508717074953294270283 1041763075612429941405425)
            ·
              refine ⟨781322306709322456054069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041763075612429941405425 781322306709322456054069)
              ·
                refine ⟨73248966253998980255069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 781322306709322456054069 73248966253998980255069)
                ·
                  rfl

theorem cell20_481450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_481450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_481450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_481450 prefixEnd_481450 := by exact prefixLift 481450
  have htrace : WordTrace (prefixWord ++ tailWord_481450) baseStart_481450 baseEnd_481450 := by
    simpa [prefixWord, tailWord_481450, baseEnd_481450] using wordTrace_append hprefix tailTrace_481450
  have hstable : (prefixWord ++ tailWord_481450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481450).length < 2 ^ (prefixWord ++ tailWord_481450).sum := by decide
  have hdescent : baseEnd_481450 < baseStart_481450 := by decide
  rcases family_descends (prefixWord ++ tailWord_481450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
