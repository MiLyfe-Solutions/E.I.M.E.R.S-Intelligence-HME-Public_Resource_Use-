import V185TrunkScan23Chunk0184

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1095181 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1095181 : Nat := 118140960795 + 1095181 * 2 ^ 59
def prefixEnd_1095181 : Nat := 4983230072969 + 3 ^ 40 * 1095181 * 2
def baseEnd_1095181 : Nat := 562354256671784833000861

theorem tailTrace_1095181 : CollatzResearch.WordTrace tailWord_1095181 prefixEnd_1095181 562354256671784833000861 := by
  unfold tailWord_1095181
  simp only [CollatzResearch.WordTrace]
  refine ⟨39944532645353753868733397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26629688430235835912488931 39944532645353753868733397)
  ·
    refine ⟨936199983875478606298439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39944532645353753868733397 936199983875478606298439)
    ·
      refine ⟨1404299975813217909447659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 936199983875478606298439 1404299975813217909447659)
      ·
        refine ⟨2106449963719826864171489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404299975813217909447659 2106449963719826864171489)
        ·
          refine ⟨1579837472789870148128617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2106449963719826864171489 1579837472789870148128617)
          ·
            refine ⟨1184878104592402611096463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579837472789870148128617 1184878104592402611096463)
            ·
              refine ⟨1777317156888603916644695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184878104592402611096463 1777317156888603916644695)
              ·
                refine ⟨2665975735332905874967043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777317156888603916644695 2665975735332905874967043)
                ·
                  refine ⟨3998963602999358812450565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665975735332905874967043 3998963602999358812450565)
                  ·
                    refine ⟨749805675562379777334481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3998963602999358812450565 749805675562379777334481)
                    ·
                      refine ⟨562354256671784833000861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749805675562379777334481 562354256671784833000861)
                      ·
                        rfl

theorem cell23_1095181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1095181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095181 prefixEnd_1095181 := by exact prefixLift 1095181
  have htrace : WordTrace (prefixWord ++ tailWord_1095181) baseStart_1095181 baseEnd_1095181 := by
    simpa [prefixWord, tailWord_1095181, baseEnd_1095181] using wordTrace_append hprefix tailTrace_1095181
  have hstable : (prefixWord ++ tailWord_1095181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095181).length < 2 ^ (prefixWord ++ tailWord_1095181).sum := by decide
  have hdescent : baseEnd_1095181 < baseStart_1095181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095196 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1095196 : Nat := 118140960795 + 1095196 * 2 ^ 59
def prefixEnd_1095196 : Nat := 4983230072969 + 3 ^ 40 * 1095196 * 2
def baseEnd_1095196 : Nat := 187453986293867424771097

theorem tailTrace_1095196 : CollatzResearch.WordTrace tailWord_1095196 prefixEnd_1095196 187453986293867424771097 := by
  unfold tailWord_1095196
  simp only [CollatzResearch.WordTrace]
  refine ⟨19972539870149705715264721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26630053160199607620352961 19972539870149705715264721)
  ·
    refine ⟨14979404902612279286448541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19972539870149705715264721 14979404902612279286448541)
    ·
      refine ⟨5617276838479604732418203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14979404902612279286448541 5617276838479604732418203)
      ·
        refine ⟨8425915257719407098627305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5617276838479604732418203 8425915257719407098627305)
        ·
          refine ⟨6319436443289555323970479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8425915257719407098627305 6319436443289555323970479)
          ·
            refine ⟨9479154664934332985955719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6319436443289555323970479 9479154664934332985955719)
            ·
              refine ⟨14218731997401499478933579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9479154664934332985955719 14218731997401499478933579)
              ·
                refine ⟨21328097996102249218400369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14218731997401499478933579 21328097996102249218400369)
                ·
                  refine ⟨15996073497076686913800277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21328097996102249218400369 15996073497076686913800277)
                  ·
                    refine ⟨187453986293867424771097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15996073497076686913800277 187453986293867424771097)
                    ·
                      rfl

theorem cell23_1095196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1095196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095196 prefixEnd_1095196 := by exact prefixLift 1095196
  have htrace : WordTrace (prefixWord ++ tailWord_1095196) baseStart_1095196 baseEnd_1095196 := by
    simpa [prefixWord, tailWord_1095196, baseEnd_1095196] using wordTrace_append hprefix tailTrace_1095196
  have hstable : (prefixWord ++ tailWord_1095196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095196).length < 2 ^ (prefixWord ++ tailWord_1095196).sum := by decide
  have hdescent : baseEnd_1095196 < baseStart_1095196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095223 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_1095223 : Nat := 118140960795 + 1095223 * 2 ^ 59
def prefixEnd_1095223 : Nat := 4983230072969 + 3 ^ 40 * 1095223 * 2
def baseEnd_1095223 : Nat := 562375822859273668675667

theorem tailTrace_1095223 : CollatzResearch.WordTrace tailWord_1095223 prefixEnd_1095223 562375822859273668675667 := by
  unfold tailWord_1095223
  simp only [CollatzResearch.WordTrace]
  refine ⟨39946064511201595041762323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26630709674134396694508215 39946064511201595041762323)
  ·
    refine ⟨59919096766802392562643485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39946064511201595041762323 59919096766802392562643485)
    ·
      refine ⟨22469661287550897210991307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59919096766802392562643485 22469661287550897210991307)
      ·
        refine ⟨33704491931326345816486961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22469661287550897210991307 33704491931326345816486961)
        ·
          refine ⟨25278368948494759362365221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33704491931326345816486961 25278368948494759362365221)
          ·
            refine ⟨4739694177842767380443479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25278368948494759362365221 4739694177842767380443479)
            ·
              refine ⟨7109541266764151070665219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739694177842767380443479 7109541266764151070665219)
              ·
                refine ⟨10664311900146226605997829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7109541266764151070665219 10664311900146226605997829)
                ·
                  refine ⟨1999558481277417488624593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10664311900146226605997829 1999558481277417488624593)
                  ·
                    refine ⟨1499668860958063116468445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1999558481277417488624593 1499668860958063116468445)
                    ·
                      refine ⟨562375822859273668675667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1499668860958063116468445 562375822859273668675667)
                      ·
                        rfl

theorem cell23_1095223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_1095223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095223 prefixEnd_1095223 := by exact prefixLift 1095223
  have htrace : WordTrace (prefixWord ++ tailWord_1095223) baseStart_1095223 baseEnd_1095223 := by
    simpa [prefixWord, tailWord_1095223, baseEnd_1095223] using wordTrace_append hprefix tailTrace_1095223
  have hstable : (prefixWord ++ tailWord_1095223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095223).length < 2 ^ (prefixWord ++ tailWord_1095223).sum := by decide
  have hdescent : baseEnd_1095223 < baseStart_1095223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095226 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 8]
def baseStart_1095226 : Nat := 118140960795 + 1095226 * 2 ^ 59
def prefixEnd_1095226 : Nat := 4983230072969 + 3 ^ 40 * 1095226 * 2
def baseEnd_1095226 : Nat := 62486373700137461882017

theorem tailTrace_1095226 : CollatzResearch.WordTrace tailWord_1095226 prefixEnd_1095226 62486373700137461882017 := by
  unfold tailWord_1095226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986543482547681638530383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26630782620127151036081021 9986543482547681638530383)
  ·
    refine ⟨14979815223821522457795575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9986543482547681638530383 14979815223821522457795575)
    ·
      refine ⟨22469722835732283686693363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14979815223821522457795575 22469722835732283686693363)
      ·
        refine ⟨33704584253598425530040045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22469722835732283686693363 33704584253598425530040045)
        ·
          refine ⟨12639219095099409573765017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33704584253598425530040045 12639219095099409573765017)
          ·
            refine ⟨9479414321324557180323763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12639219095099409573765017 9479414321324557180323763)
            ·
              refine ⟨14219121481986835770485645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9479414321324557180323763 14219121481986835770485645)
              ·
                refine ⟨5332170555745063413932117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14219121481986835770485645 5332170555745063413932117)
                ·
                  refine ⟨62486373700137461882017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5332170555745063413932117 62486373700137461882017)
                  ·
                    rfl

theorem cell23_1095226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_1095226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095226 prefixEnd_1095226 := by exact prefixLift 1095226
  have htrace : WordTrace (prefixWord ++ tailWord_1095226) baseStart_1095226 baseEnd_1095226 := by
    simpa [prefixWord, tailWord_1095226, baseEnd_1095226] using wordTrace_append hprefix tailTrace_1095226
  have hstable : (prefixWord ++ tailWord_1095226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095226).length < 2 ^ (prefixWord ++ tailWord_1095226).sum := by decide
  have hdescent : baseEnd_1095226 < baseStart_1095226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095273 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 1, 5]
def baseStart_1095273 : Nat := 118140960795 + 1095273 * 2 ^ 59
def prefixEnd_1095273 : Nat := 4983230072969 + 3 ^ 40 * 1095273 * 2
def baseEnd_1095273 : Nat := 187467165630666157683479

theorem tailTrace_1095273 : CollatzResearch.WordTrace tailWord_1095273 prefixEnd_1095273 187467165630666157683479 := by
  unfold tailWord_1095273
  simp only [CollatzResearch.WordTrace]
  refine ⟨39947888161020453581082473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26631925440680302387388315 39947888161020453581082473)
  ·
    refine ⟨29960916120765340185811855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39947888161020453581082473 29960916120765340185811855)
    ·
      refine ⟨44941374181148010278717783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29960916120765340185811855 44941374181148010278717783)
      ·
        refine ⟨67412061271722015418076675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44941374181148010278717783 67412061271722015418076675)
        ·
          refine ⟨101118091907583023127115013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67412061271722015418076675 101118091907583023127115013)
          ·
            refine ⟨18959642232671816836334065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101118091907583023127115013 18959642232671816836334065)
            ·
              refine ⟨14219731674503862627250549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18959642232671816836334065 14219731674503862627250549)
              ·
                refine ⟨1333099844484737121304739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14219731674503862627250549 1333099844484737121304739)
                ·
                  refine ⟨1999649766727105681957109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1333099844484737121304739 1999649766727105681957109)
                  ·
                    refine ⟨187467165630666157683479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1999649766727105681957109 187467165630666157683479)
                    ·
                      rfl

theorem cell23_1095273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_1095273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095273 prefixEnd_1095273 := by exact prefixLift 1095273
  have htrace : WordTrace (prefixWord ++ tailWord_1095273) baseStart_1095273 baseEnd_1095273 := by
    simpa [prefixWord, tailWord_1095273, baseEnd_1095273] using wordTrace_append hprefix tailTrace_1095273
  have hstable : (prefixWord ++ tailWord_1095273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095273).length < 2 ^ (prefixWord ++ tailWord_1095273).sum := by decide
  have hdescent : baseEnd_1095273 < baseStart_1095273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095303 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 1, 6]
def baseStart_1095303 : Nat := 118140960795 + 1095303 * 2 ^ 59
def prefixEnd_1095303 : Nat := 4983230072969 + 3 ^ 40 * 1095303 * 2
def baseEnd_1095303 : Nat := 187472300437211118558433

theorem tailTrace_1095303 : CollatzResearch.WordTrace tailWord_1095303 prefixEnd_1095303 187472300437211118558433 := by
  unfold tailWord_1095303
  simp only [CollatzResearch.WordTrace]
  refine ⟨39948982350911768704674563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26632654900607845803116375 39948982350911768704674563)
  ·
    refine ⟨59923473526367653057011845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39948982350911768704674563 59923473526367653057011845)
    ·
      refine ⟨11235651286193934948189721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59923473526367653057011845 11235651286193934948189721)
      ·
        refine ⟨8426738464645451211142291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11235651286193934948189721 8426738464645451211142291)
        ·
          refine ⟨12640107696968176816713437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8426738464645451211142291 12640107696968176816713437)
          ·
            refine ⟨4740040386363066306267539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12640107696968176816713437 4740040386363066306267539)
            ·
              refine ⟨7110060579544599459401309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4740040386363066306267539 7110060579544599459401309)
              ·
                refine ⟨2666272717329224797275491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7110060579544599459401309 2666272717329224797275491)
                ·
                  refine ⟨3999409075993837195913237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666272717329224797275491 3999409075993837195913237)
                  ·
                    refine ⟨187472300437211118558433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3999409075993837195913237 187472300437211118558433)
                    ·
                      rfl

theorem cell23_1095303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_1095303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095303 prefixEnd_1095303 := by exact prefixLift 1095303
  have htrace : WordTrace (prefixWord ++ tailWord_1095303) baseStart_1095303 baseEnd_1095303 := by
    simpa [prefixWord, tailWord_1095303, baseEnd_1095303] using wordTrace_append hprefix tailTrace_1095303
  have hstable : (prefixWord ++ tailWord_1095303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095303).length < 2 ^ (prefixWord ++ tailWord_1095303).sum := by decide
  have hdescent : baseEnd_1095303 < baseStart_1095303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095304 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1095304 : Nat := 118140960795 + 1095304 * 2 ^ 59
def prefixEnd_1095304 : Nat := 4983230072969 + 3 ^ 40 * 1095304 * 2
def baseEnd_1095304 : Nat := 562417414792287851762795

theorem tailTrace_1095304 : CollatzResearch.WordTrace tailWord_1095304 prefixEnd_1095304 562417414792287851762795 := by
  unfold tailWord_1095304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19974509411954072937730483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26632679215938763916973977 19974509411954072937730483)
  ·
    refine ⟨29961764117931109406595725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19974509411954072937730483 29961764117931109406595725)
    ·
      refine ⟨11235661544224166027473397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29961764117931109406595725 11235661544224166027473397)
      ·
        refine ⟨1053343269771015565075631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11235661544224166027473397 1053343269771015565075631)
        ·
          refine ⟨1580014904656523347613447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053343269771015565075631 1580014904656523347613447)
          ·
            refine ⟨2370022356984785021420171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580014904656523347613447 2370022356984785021420171)
            ·
              refine ⟨3555033535477177532130257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370022356984785021420171 3555033535477177532130257)
              ·
                refine ⟨2666275151607883149097693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3555033535477177532130257 2666275151607883149097693)
                ·
                  refine ⟨999853181852956180911635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2666275151607883149097693 999853181852956180911635)
                  ·
                    refine ⟨1499779772779434271367453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 999853181852956180911635 1499779772779434271367453)
                    ·
                      refine ⟨562417414792287851762795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1499779772779434271367453 562417414792287851762795)
                      ·
                        rfl

theorem cell23_1095304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1095304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095304 prefixEnd_1095304 := by exact prefixLift 1095304
  have htrace : WordTrace (prefixWord ++ tailWord_1095304) baseStart_1095304 baseEnd_1095304 := by
    simpa [prefixWord, tailWord_1095304, baseEnd_1095304] using wordTrace_append hprefix tailTrace_1095304
  have hstable : (prefixWord ++ tailWord_1095304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095304).length < 2 ^ (prefixWord ++ tailWord_1095304).sum := by decide
  have hdescent : baseEnd_1095304 < baseStart_1095304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095310 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1095310 : Nat := 118140960795 + 1095310 * 2 ^ 59
def prefixEnd_1095310 : Nat := 4983230072969 + 3 ^ 40 * 1095310 * 2
def baseEnd_1095310 : Nat := 562420495676214828287767

theorem tailTrace_1095310 : CollatzResearch.WordTrace tailWord_1095310 prefixEnd_1095310 562420495676214828287767 := by
  unfold tailWord_1095310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993654707735801112522423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26632825107924272600119589 4993654707735801112522423)
  ·
    refine ⟨7490482061603701668783635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4993654707735801112522423 7490482061603701668783635)
    ·
      refine ⟨11235723092405552503175453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7490482061603701668783635 11235723092405552503175453)
      ·
        refine ⟨4213396159652082188690795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11235723092405552503175453 4213396159652082188690795)
        ·
          refine ⟨6320094239478123283036193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4213396159652082188690795 6320094239478123283036193)
          ·
            refine ⟨4740070679608592462277145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6320094239478123283036193 4740070679608592462277145)
            ·
              refine ⟨3555053009706444346707859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4740070679608592462277145 3555053009706444346707859)
              ·
                refine ⟨5332579514559666520061789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3555053009706444346707859 5332579514559666520061789)
                ·
                  refine ⟨1999717317959874945023171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5332579514559666520061789 1999717317959874945023171)
                  ·
                    refine ⟨2999575976939812417534757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1999717317959874945023171 2999575976939812417534757)
                    ·
                      refine ⟨562420495676214828287767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2999575976939812417534757 562420495676214828287767)
                      ·
                        rfl

theorem cell23_1095310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1095310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095310 prefixEnd_1095310 := by exact prefixLift 1095310
  have htrace : WordTrace (prefixWord ++ tailWord_1095310) baseStart_1095310 baseEnd_1095310 := by
    simpa [prefixWord, tailWord_1095310, baseEnd_1095310] using wordTrace_append hprefix tailTrace_1095310
  have hstable : (prefixWord ++ tailWord_1095310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095310).length < 2 ^ (prefixWord ++ tailWord_1095310).sum := by decide
  have hdescent : baseEnd_1095310 < baseStart_1095310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095324 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_1095324 : Nat := 118140960795 + 1095324 * 2 ^ 59
def prefixEnd_1095324 : Nat := 4983230072969 + 3 ^ 40 * 1095324 * 2
def baseEnd_1095324 : Nat := 187475894801792591170901

theorem tailTrace_1095324 : CollatzResearch.WordTrace tailWord_1095324 prefixEnd_1095324 187475894801792591170901 := by
  unfold tailWord_1095324
  simp only [CollatzResearch.WordTrace]
  refine ⟨19974874141917844645594513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26633165522557126194126017 19974874141917844645594513)
  ·
    refine ⟨14981155606438383484195885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19974874141917844645594513 14981155606438383484195885)
    ·
      refine ⟨5617933352414393806573457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14981155606438383484195885 5617933352414393806573457)
      ·
        refine ⟨4213450014310795354930093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5617933352414393806573457 4213450014310795354930093)
        ·
          refine ⟨1580043755366548258098785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4213450014310795354930093 1580043755366548258098785)
          ·
            refine ⟨1185032816524911193574089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1580043755366548258098785 1185032816524911193574089)
            ·
              refine ⟨888774612393683395180567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185032816524911193574089 888774612393683395180567)
              ·
                refine ⟨1333161918590525092770851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888774612393683395180567 1333161918590525092770851)
                ·
                  refine ⟨1999742877885787639156277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1333161918590525092770851 1999742877885787639156277)
                  ·
                    refine ⟨187475894801792591170901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1999742877885787639156277 187475894801792591170901)
                    ·
                      rfl

theorem cell23_1095324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_1095324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095324 prefixEnd_1095324 := by exact prefixLift 1095324
  have htrace : WordTrace (prefixWord ++ tailWord_1095324) baseStart_1095324 baseEnd_1095324 := by
    simpa [prefixWord, tailWord_1095324, baseEnd_1095324] using wordTrace_append hprefix tailTrace_1095324
  have hstable : (prefixWord ++ tailWord_1095324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095324).length < 2 ^ (prefixWord ++ tailWord_1095324).sum := by decide
  have hdescent : baseEnd_1095324 < baseStart_1095324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095344 : List Nat := [2, 1, 1, 1, 2, 1, 6, 4, 1, 2, 2]
def baseStart_1095344 : Nat := 118140960795 + 1095344 * 2 ^ 59
def prefixEnd_1095344 : Nat := 4983230072969 + 3 ^ 40 * 1095344 * 2
def baseEnd_1095344 : Nat := 562437954018467695262611

theorem tailTrace_1095344 : CollatzResearch.WordTrace tailWord_1095344 prefixEnd_1095344 562437954018467695262611 := by
  unfold tailWord_1095344
  simp only [CollatzResearch.WordTrace]
  refine ⟨19975238871881616353458543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26633651829175488471278057 19975238871881616353458543)
  ·
    refine ⟨29962858307822424530187815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19975238871881616353458543 29962858307822424530187815)
    ·
      refine ⟨44944287461733636795281723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29962858307822424530187815 44944287461733636795281723)
      ·
        refine ⟨67416431192600455192922585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44944287461733636795281723 67416431192600455192922585)
        ·
          refine ⟨50562323394450341394691939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67416431192600455192922585 50562323394450341394691939)
          ·
            refine ⟨75843485091675512092037909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50562323394450341394691939 75843485091675512092037909)
            ·
              refine ⟨3555163363672289629314277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75843485091675512092037909 3555163363672289629314277)
              ·
                refine ⟨666593130688554305496427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3555163363672289629314277 666593130688554305496427)
                ·
                  refine ⟨999889696032831458244641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666593130688554305496427 999889696032831458244641)
                  ·
                    refine ⟨749917272024623593683481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 999889696032831458244641 749917272024623593683481)
                    ·
                      refine ⟨562437954018467695262611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749917272024623593683481 562437954018467695262611)
                      ·
                        rfl

theorem cell23_1095344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 2, 2].length) (baseStart_1095344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095344 prefixEnd_1095344 := by exact prefixLift 1095344
  have htrace : WordTrace (prefixWord ++ tailWord_1095344) baseStart_1095344 baseEnd_1095344 := by
    simpa [prefixWord, tailWord_1095344, baseEnd_1095344] using wordTrace_append hprefix tailTrace_1095344
  have hstable : (prefixWord ++ tailWord_1095344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095344).length < 2 ^ (prefixWord ++ tailWord_1095344).sum := by decide
  have hdescent : baseEnd_1095344 < baseStart_1095344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095378 : List Nat := [3, 2, 2, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_1095378 : Nat := 118140960795 + 1095378 * 2 ^ 59
def prefixEnd_1095378 : Nat := 4983230072969 + 3 ^ 40 * 1095378 * 2
def baseEnd_1095378 : Nat := 562455412360720562237455

theorem tailTrace_1095378 : CollatzResearch.WordTrace tailWord_1095378 prefixEnd_1095378 562455412360720562237455 := by
  unfold tailWord_1095378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9987929456410014128413697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26634478550426704342436525 9987929456410014128413697)
  ·
    refine ⟨7490947092307510596310273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9987929456410014128413697 7490947092307510596310273)
    ·
      refine ⟨5618210319230632947232705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7490947092307510596310273 5618210319230632947232705)
      ·
        refine ⟨4213657739422974710424529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5618210319230632947232705 4213657739422974710424529)
        ·
          refine ⟨3160243304567231032818397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4213657739422974710424529 3160243304567231032818397)
          ·
            refine ⟨1185091239212711637306899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3160243304567231032818397 1185091239212711637306899)
            ·
              refine ⟨1777636858819067455960349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185091239212711637306899 1777636858819067455960349)
              ·
                refine ⟨666613822057150295985131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1777636858819067455960349 666613822057150295985131)
                ·
                  refine ⟨999920733085725443977697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666613822057150295985131 999920733085725443977697)
                  ·
                    refine ⟨749940549814294082983273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 999920733085725443977697 749940549814294082983273)
                    ·
                      refine ⟨562455412360720562237455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 749940549814294082983273 562455412360720562237455)
                      ·
                        rfl

theorem cell23_1095378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_1095378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095378 prefixEnd_1095378 := by exact prefixLift 1095378
  have htrace : WordTrace (prefixWord ++ tailWord_1095378) baseStart_1095378 baseEnd_1095378 := by
    simpa [prefixWord, tailWord_1095378, baseEnd_1095378] using wordTrace_append hprefix tailTrace_1095378
  have hstable : (prefixWord ++ tailWord_1095378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095378).length < 2 ^ (prefixWord ++ tailWord_1095378).sum := by decide
  have hdescent : baseEnd_1095378 < baseStart_1095378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095423 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 7]
def baseStart_1095423 : Nat := 118140960795 + 1095423 * 2 ^ 59
def prefixEnd_1095423 : Nat := 4983230072969 + 3 ^ 40 * 1095423 * 2
def baseEnd_1095423 : Nat := 62497613221130320686083

theorem tailTrace_1095423 : CollatzResearch.WordTrace tailWord_1095423 prefixEnd_1095423 62497613221130320686083 := by
  unfold tailWord_1095423
  simp only [CollatzResearch.WordTrace]
  refine ⟨39953359110477029199042923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26635572740318019466028615 39953359110477029199042923)
  ·
    refine ⟨59930038665715543798564385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39953359110477029199042923 59930038665715543798564385)
    ·
      refine ⟨44947528999286657848923289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59930038665715543798564385 44947528999286657848923289)
      ·
        refine ⟨33710646749464993386692467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44947528999286657848923289 33710646749464993386692467)
        ·
          refine ⟨50565970124197490080038701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33710646749464993386692467 50565970124197490080038701)
          ·
            refine ⟨18962238796574058780014513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50565970124197490080038701 18962238796574058780014513)
            ·
              refine ⟨14221679097430544085010885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18962238796574058780014513 14221679097430544085010885)
              ·
                refine ⟨2666564830768227015939541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14221679097430544085010885 2666564830768227015939541)
                ·
                  refine ⟨62497613221130320686083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2666564830768227015939541 62497613221130320686083)
                  ·
                    rfl

theorem cell23_1095423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 7].length) (baseStart_1095423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095423 prefixEnd_1095423 := by exact prefixLift 1095423
  have htrace : WordTrace (prefixWord ++ tailWord_1095423) baseStart_1095423 baseEnd_1095423 := by
    simpa [prefixWord, tailWord_1095423, baseEnd_1095423] using wordTrace_append hprefix tailTrace_1095423
  have hstable : (prefixWord ++ tailWord_1095423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095423).length < 2 ^ (prefixWord ++ tailWord_1095423).sum := by decide
  have hdescent : baseEnd_1095423 < baseStart_1095423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095457 : List Nat := [1, 2, 3, 2, 1, 4, 1, 4, 5]
def baseStart_1095457 : Nat := 118140960795 + 1095457 * 2 ^ 59
def prefixEnd_1095457 : Nat := 4983230072969 + 3 ^ 40 * 1095457 * 2
def baseEnd_1095457 : Nat := 62499553036936194794399

theorem tailTrace_1095457 : CollatzResearch.WordTrace tailWord_1095457 prefixEnd_1095457 62499553036936194794399 := by
  unfold tailWord_1095457
  simp only [CollatzResearch.WordTrace]
  refine ⟨39954599192353853005780625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26636399461569235337187083 39954599192353853005780625)
  ·
    refine ⟨29965949394265389754335469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39954599192353853005780625 29965949394265389754335469)
    ·
      refine ⟨11237231022849521157875801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29965949394265389754335469 11237231022849521157875801)
      ·
        refine ⟨8427923267137140868406851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11237231022849521157875801 8427923267137140868406851)
        ·
          refine ⟨12641884900705711302610277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8427923267137140868406851 12641884900705711302610277)
          ·
            refine ⟨2370353418882320869239427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12641884900705711302610277 2370353418882320869239427)
            ·
              refine ⟨3555530128323481303859141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370353418882320869239427 3555530128323481303859141)
              ·
                refine ⟨666661899060652744473589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3555530128323481303859141 666661899060652744473589)
                ·
                  refine ⟨62499553036936194794399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 666661899060652744473589 62499553036936194794399)
                  ·
                    rfl

theorem cell23_1095457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 5].length) (baseStart_1095457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095457 prefixEnd_1095457 := by exact prefixLift 1095457
  have htrace : WordTrace (prefixWord ++ tailWord_1095457) baseStart_1095457 baseEnd_1095457 := by
    simpa [prefixWord, tailWord_1095457, baseEnd_1095457] using wordTrace_append hprefix tailTrace_1095457
  have hstable : (prefixWord ++ tailWord_1095457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095457).length < 2 ^ (prefixWord ++ tailWord_1095457).sum := by decide
  have hdescent : baseEnd_1095457 < baseStart_1095457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095534 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1095534 : Nat := 118140960795 + 1095534 * 2 ^ 59
def prefixEnd_1095534 : Nat := 4983230072969 + 3 ^ 40 * 1095534 * 2
def baseEnd_1095534 : Nat := 187511838447607317295579

theorem tailTrace_1095534 : CollatzResearch.WordTrace tailWord_1095534 prefixEnd_1095534 187511838447607317295579 := by
  unfold tailWord_1095534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4994675951634361894541707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26638271742049930104222437 4994675951634361894541707)
  ·
    refine ⟨7492013927451542841812561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4994675951634361894541707 7492013927451542841812561)
    ·
      refine ⟨5619010445588657131359421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7492013927451542841812561 5619010445588657131359421)
      ·
        refine ⟨2107128917095746424259783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5619010445588657131359421 2107128917095746424259783)
        ·
          refine ⟨3160693375643619636389675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107128917095746424259783 3160693375643619636389675)
          ·
            refine ⟨4741040063465429454584513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160693375643619636389675 4741040063465429454584513)
            ·
              refine ⟨3555780047599072090938385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4741040063465429454584513 3555780047599072090938385)
              ·
                refine ⟨2666835035699304068203789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3555780047599072090938385 2666835035699304068203789)
                ·
                  refine ⟨1000063138387239025576421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2666835035699304068203789 1000063138387239025576421)
                  ·
                    refine ⟨187511838447607317295579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1000063138387239025576421 187511838447607317295579)
                    ·
                      rfl

theorem cell23_1095534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1095534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095534 prefixEnd_1095534 := by exact prefixLift 1095534
  have htrace : WordTrace (prefixWord ++ tailWord_1095534) baseStart_1095534 baseEnd_1095534 := by
    simpa [prefixWord, tailWord_1095534, baseEnd_1095534] using wordTrace_append hprefix tailTrace_1095534
  have hstable : (prefixWord ++ tailWord_1095534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095534).length < 2 ^ (prefixWord ++ tailWord_1095534).sum := by decide
  have hdescent : baseEnd_1095534 < baseStart_1095534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095601 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1095601 : Nat := 118140960795 + 1095601 * 2 ^ 59
def prefixEnd_1095601 : Nat := 4983230072969 + 3 ^ 40 * 1095601 * 2
def baseEnd_1095601 : Nat := 562569918546673189748929

theorem tailTrace_1095601 : CollatzResearch.WordTrace tailWord_1095601 prefixEnd_1095601 562569918546673189748929 := by
  unfold tailWord_1095601
  simp only [CollatzResearch.WordTrace]
  refine ⟨39959851303832165599022657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26639900869221443732681771 39959851303832165599022657)
  ·
    refine ⟨29969888477874124199266993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39959851303832165599022657 29969888477874124199266993)
    ·
      refine ⟨22477416358405593149450245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29969888477874124199266993 22477416358405593149450245)
      ·
        refine ⟨4214515567201048715521921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22477416358405593149450245 4214515567201048715521921)
        ·
          refine ⟨3160886675400786536641441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4214515567201048715521921 3160886675400786536641441)
          ·
            refine ⟨2370665006550589902481081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3160886675400786536641441 2370665006550589902481081)
            ·
              refine ⟨1777998754912942426860811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370665006550589902481081 1777998754912942426860811)
              ·
                refine ⟨2666998132369413640291217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777998754912942426860811 2666998132369413640291217)
                ·
                  refine ⟨2000248599277060230218413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2666998132369413640291217 2000248599277060230218413)
                  ·
                    refine ⟨750093224728897586331905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2000248599277060230218413 750093224728897586331905)
                    ·
                      refine ⟨562569918546673189748929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 750093224728897586331905 562569918546673189748929)
                      ·
                        rfl

theorem cell23_1095601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1095601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095601 prefixEnd_1095601 := by exact prefixLift 1095601
  have htrace : WordTrace (prefixWord ++ tailWord_1095601) baseStart_1095601 baseEnd_1095601 := by
    simpa [prefixWord, tailWord_1095601, baseEnd_1095601] using wordTrace_append hprefix tailTrace_1095601
  have hstable : (prefixWord ++ tailWord_1095601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095601).length < 2 ^ (prefixWord ++ tailWord_1095601).sum := by decide
  have hdescent : baseEnd_1095601 < baseStart_1095601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095610 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1095610 : Nat := 118140960795 + 1095610 * 2 ^ 59
def prefixEnd_1095610 : Nat := 4983230072969 + 3 ^ 40 * 1095610 * 2
def baseEnd_1095610 : Nat := 562574539872563654536387

theorem tailTrace_1095610 : CollatzResearch.WordTrace tailWord_1095610 prefixEnd_1095610 562574539872563654536387 := by
  unfold tailWord_1095610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9990044890199890034025071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26640119707199706757400189 9990044890199890034025071)
  ·
    refine ⟨14985067335299835051037607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9990044890199890034025071 14985067335299835051037607)
    ·
      refine ⟨22477601002949752576556411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14985067335299835051037607 22477601002949752576556411)
      ·
        refine ⟨33716401504424628864834617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22477601002949752576556411 33716401504424628864834617)
        ·
          refine ⟨25287301128318471648625963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33716401504424628864834617 25287301128318471648625963)
          ·
            refine ⟨37930951692477707472938945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25287301128318471648625963 37930951692477707472938945)
            ·
              refine ⟨28448213769358280604704209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37930951692477707472938945 28448213769358280604704209)
              ·
                refine ⟨21336160327018710453528157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28448213769358280604704209 21336160327018710453528157)
                ·
                  refine ⟨8001060122632016420073059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21336160327018710453528157 8001060122632016420073059)
                  ·
                    refine ⟨12001590183948024630109589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8001060122632016420073059 12001590183948024630109589)
                    ·
                      refine ⟨562574539872563654536387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12001590183948024630109589 562574539872563654536387)
                      ·
                        rfl

theorem cell23_1095610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1095610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095610 prefixEnd_1095610 := by exact prefixLift 1095610
  have htrace : WordTrace (prefixWord ++ tailWord_1095610) baseStart_1095610 baseEnd_1095610 := by
    simpa [prefixWord, tailWord_1095610, baseEnd_1095610] using wordTrace_append hprefix tailTrace_1095610
  have hstable : (prefixWord ++ tailWord_1095610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095610).length < 2 ^ (prefixWord ++ tailWord_1095610).sum := by decide
  have hdescent : baseEnd_1095610 < baseStart_1095610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095620 : List Nat := [2, 3, 3, 15]
def baseStart_1095620 : Nat := 118140960795 + 1095620 * 2 ^ 59
def prefixEnd_1095620 : Nat := 4983230072969 + 3 ^ 40 * 1095620 * 2
def baseEnd_1095620 : Nat := 257238077128078927943

theorem tailTrace_1095620 : CollatzResearch.WordTrace tailWord_1095620 prefixEnd_1095620 257238077128078927943 := by
  unfold tailWord_1095620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19980272145381665921982157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26640362860508887895976209 19980272145381665921982157)
  ·
    refine ⟨7492602054518124720743309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19980272145381665921982157 7492602054518124720743309)
    ·
      refine ⟨2809725770444296770278741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7492602054518124720743309 2809725770444296770278741)
      ·
        refine ⟨257238077128078927943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 2809725770444296770278741 257238077128078927943)
        ·
          rfl

theorem cell23_1095620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 15].length) (baseStart_1095620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095620 prefixEnd_1095620 := by exact prefixLift 1095620
  have htrace : WordTrace (prefixWord ++ tailWord_1095620) baseStart_1095620 baseEnd_1095620 := by
    simpa [prefixWord, tailWord_1095620, baseEnd_1095620] using wordTrace_append hprefix tailTrace_1095620
  have hstable : (prefixWord ++ tailWord_1095620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095620).length < 2 ^ (prefixWord ++ tailWord_1095620).sum := by decide
  have hdescent : baseEnd_1095620 < baseStart_1095620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095624 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 2, 4]
def baseStart_1095624 : Nat := 118140960795 + 1095624 * 2 ^ 59
def prefixEnd_1095624 : Nat := 4983230072969 + 3 ^ 40 * 1095624 * 2
def baseEnd_1095624 : Nat := 187527242867242199920441

theorem tailTrace_1095624 : CollatzResearch.WordTrace tailWord_1095624 prefixEnd_1095624 187527242867242199920441 := by
  unfold tailWord_1095624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19980345091374420263554963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26640460121832560351406617 19980345091374420263554963)
  ·
    refine ⟨29970517637061630395332445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19980345091374420263554963 29970517637061630395332445)
    ·
      refine ⟨11238944113898111398249667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29970517637061630395332445 11238944113898111398249667)
      ·
        refine ⟨16858416170847167097374501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11238944113898111398249667 16858416170847167097374501)
        ·
          refine ⟨3160953032033843830757719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16858416170847167097374501 3160953032033843830757719)
          ·
            refine ⟨4741429548050765746136579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160953032033843830757719 4741429548050765746136579)
            ·
              refine ⟨7112144322076148619204869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741429548050765746136579 7112144322076148619204869)
              ·
                refine ⟨1333527060389277866100913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7112144322076148619204869 1333527060389277866100913)
                ·
                  refine ⟨1000145295291958399575685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1333527060389277866100913 1000145295291958399575685)
                  ·
                    refine ⟨187527242867242199920441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1000145295291958399575685 187527242867242199920441)
                    ·
                      rfl

theorem cell23_1095624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_1095624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095624 prefixEnd_1095624 := by exact prefixLift 1095624
  have htrace : WordTrace (prefixWord ++ tailWord_1095624) baseStart_1095624 baseEnd_1095624 := by
    simpa [prefixWord, tailWord_1095624, baseEnd_1095624] using wordTrace_append hprefix tailTrace_1095624
  have hstable : (prefixWord ++ tailWord_1095624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095624).length < 2 ^ (prefixWord ++ tailWord_1095624).sum := by decide
  have hdescent : baseEnd_1095624 < baseStart_1095624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095637 : List Nat := [1, 3, 2, 3, 2, 1, 3, 8]
def baseStart_1095637 : Nat := 118140960795 + 1095637 * 2 ^ 59
def prefixEnd_1095637 : Nat := 4983230072969 + 3 ^ 40 * 1095637 * 2
def baseEnd_1095637 : Nat := 20836607550008705514769

theorem tailTrace_1095637 : CollatzResearch.WordTrace tailWord_1095637 prefixEnd_1095637 20836607550008705514769 := by
  unfold tailWord_1095637
  simp only [CollatzResearch.WordTrace]
  refine ⟨39961164331701743747333165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26640776221134495831555443 39961164331701743747333165)
  ·
    refine ⟨14985436624388153905249937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39961164331701743747333165 14985436624388153905249937)
    ·
      refine ⟨11239077468291115428937453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14985436624388153905249937 11239077468291115428937453)
      ·
        refine ⟨4214654050609168285851545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11239077468291115428937453 4214654050609168285851545)
        ·
          refine ⟨3160990537956876214388659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4214654050609168285851545 3160990537956876214388659)
          ·
            refine ⟨4741485806935314321582989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160990537956876214388659 4741485806935314321582989)
            ·
              refine ⟨1778057177600742870593621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4741485806935314321582989 1778057177600742870593621)
              ·
                refine ⟨20836607550008705514769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1778057177600742870593621 20836607550008705514769)
                ·
                  rfl

theorem cell23_1095637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 8].length) (baseStart_1095637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095637 prefixEnd_1095637 := by exact prefixLift 1095637
  have htrace : WordTrace (prefixWord ++ tailWord_1095637) baseStart_1095637 baseEnd_1095637 := by
    simpa [prefixWord, tailWord_1095637, baseEnd_1095637] using wordTrace_append hprefix tailTrace_1095637
  have hstable : (prefixWord ++ tailWord_1095637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095637).length < 2 ^ (prefixWord ++ tailWord_1095637).sum := by decide
  have hdescent : baseEnd_1095637 < baseStart_1095637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095665 : List Nat := [1, 2, 2, 2, 5, 1, 2, 3, 1, 2, 2]
def baseStart_1095665 : Nat := 118140960795 + 1095665 * 2 ^ 59
def prefixEnd_1095665 : Nat := 4983230072969 + 3 ^ 40 * 1095665 * 2
def baseEnd_1095665 : Nat := 562602781308560939348635

theorem tailTrace_1095665 : CollatzResearch.WordTrace tailWord_1095665 prefixEnd_1095665 562602781308560939348635 := by
  unfold tailWord_1095665
  simp only [CollatzResearch.WordTrace]
  refine ⟨39962185575600304529352449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26641457050400203019568299 39962185575600304529352449)
  ·
    refine ⟨29971639181700228397014337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39962185575600304529352449 29971639181700228397014337)
    ·
      refine ⟨22478729386275171297760753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29971639181700228397014337 22478729386275171297760753)
      ·
        refine ⟨16859047039706378473320565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22478729386275171297760753 16859047039706378473320565)
        ·
          refine ⟨1580535659972472981873803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16859047039706378473320565 1580535659972472981873803)
          ·
            refine ⟨2370803489958709472810705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580535659972472981873803 2370803489958709472810705)
            ·
              refine ⟨1778102617469032104608029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370803489958709472810705 1778102617469032104608029)
              ·
                refine ⟨666788481550887039228011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1778102617469032104608029 666788481550887039228011)
                ·
                  refine ⟨1000182722326330558842017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666788481550887039228011 1000182722326330558842017)
                  ·
                    refine ⟨750137041744747919131513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1000182722326330558842017 750137041744747919131513)
                    ·
                      refine ⟨562602781308560939348635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 750137041744747919131513 562602781308560939348635)
                      ·
                        rfl

theorem cell23_1095665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_1095665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095665 prefixEnd_1095665 := by exact prefixLift 1095665
  have htrace : WordTrace (prefixWord ++ tailWord_1095665) baseStart_1095665 baseEnd_1095665 := by
    simpa [prefixWord, tailWord_1095665, baseEnd_1095665] using wordTrace_append hprefix tailTrace_1095665
  have hstable : (prefixWord ++ tailWord_1095665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095665).length < 2 ^ (prefixWord ++ tailWord_1095665).sum := by decide
  have hdescent : baseEnd_1095665 < baseStart_1095665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095708 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_1095708 : Nat := 118140960795 + 1095708 * 2 ^ 59
def prefixEnd_1095708 : Nat := 4983230072969 + 3 ^ 40 * 1095708 * 2
def baseEnd_1095708 : Nat := 562624860976704271110937

theorem tailTrace_1095708 : CollatzResearch.WordTrace tailWord_1095708 prefixEnd_1095708 562624860976704271110937 := by
  unfold tailWord_1095708
  simp only [CollatzResearch.WordTrace]
  refine ⟨19981876957222261436583889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26642502609629681915445185 19981876957222261436583889)
  ·
    refine ⟨14986407717916696077437917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19981876957222261436583889 14986407717916696077437917)
    ·
      refine ⟨5619902894218761029039219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14986407717916696077437917 5619902894218761029039219)
      ·
        refine ⟨8429854341328141543558829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5619902894218761029039219 8429854341328141543558829)
        ·
          refine ⟨3161195377998053078834561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8429854341328141543558829 3161195377998053078834561)
          ·
            refine ⟨2370896533498539809125921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3161195377998053078834561 2370896533498539809125921)
            ·
              refine ⟨1778172400123904856844441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370896533498539809125921 1778172400123904856844441)
              ·
                refine ⟨1333629300092928642633331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778172400123904856844441 1333629300092928642633331)
                ·
                  refine ⟨2000443950139392963949997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1333629300092928642633331 2000443950139392963949997)
                  ·
                    refine ⟨750166481302272361481249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2000443950139392963949997 750166481302272361481249)
                    ·
                      refine ⟨562624860976704271110937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 750166481302272361481249 562624860976704271110937)
                      ·
                        rfl

theorem cell23_1095708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_1095708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095708 prefixEnd_1095708 := by exact prefixLift 1095708
  have htrace : WordTrace (prefixWord ++ tailWord_1095708) baseStart_1095708 baseEnd_1095708 := by
    simpa [prefixWord, tailWord_1095708, baseEnd_1095708] using wordTrace_append hprefix tailTrace_1095708
  have hstable : (prefixWord ++ tailWord_1095708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095708).length < 2 ^ (prefixWord ++ tailWord_1095708).sum := by decide
  have hdescent : baseEnd_1095708 < baseStart_1095708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095744 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 7]
def baseStart_1095744 : Nat := 118140960795 + 1095744 * 2 ^ 59
def prefixEnd_1095744 : Nat := 4983230072969 + 3 ^ 40 * 1095744 * 2
def baseEnd_1095744 : Nat := 62515927364474014473419

theorem tailTrace_1095744 : CollatzResearch.WordTrace tailWord_1095744 prefixEnd_1095744 62515927364474014473419 := by
  unfold tailWord_1095744
  simp only [CollatzResearch.WordTrace]
  refine ⟨19982533471157050510739143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26643377961542734014318857 19982533471157050510739143)
  ·
    refine ⟨29973800206735575766108715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19982533471157050510739143 29973800206735575766108715)
    ·
      refine ⟨44960700310103363649163073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29973800206735575766108715 44960700310103363649163073)
      ·
        refine ⟨33720525232577522736872305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44960700310103363649163073 33720525232577522736872305)
        ·
          refine ⟨25290393924433142052654229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33720525232577522736872305 25290393924433142052654229)
          ·
            refine ⟨1185487215207803533718167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25290393924433142052654229 1185487215207803533718167)
            ·
              refine ⟨1778230822811705300577251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185487215207803533718167 1778230822811705300577251)
              ·
                refine ⟨2667346234217557950865877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778230822811705300577251 2667346234217557950865877)
                ·
                  refine ⟨62515927364474014473419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2667346234217557950865877 62515927364474014473419)
                  ·
                    rfl

theorem cell23_1095744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 7].length) (baseStart_1095744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095744 prefixEnd_1095744 := by exact prefixLift 1095744
  have htrace : WordTrace (prefixWord ++ tailWord_1095744) baseStart_1095744 baseEnd_1095744 := by
    simpa [prefixWord, tailWord_1095744, baseEnd_1095744] using wordTrace_append hprefix tailTrace_1095744
  have hstable : (prefixWord ++ tailWord_1095744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095744).length < 2 ^ (prefixWord ++ tailWord_1095744).sum := by decide
  have hdescent : baseEnd_1095744 < baseStart_1095744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095811 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 2, 4, 2]
def baseStart_1095811 : Nat := 118140960795 + 1095811 * 2 ^ 59
def prefixEnd_1095811 : Nat := 4983230072969 + 3 ^ 40 * 1095811 * 2
def baseEnd_1095811 : Nat := 562677749484117368122963

theorem tailTrace_1095811 : CollatzResearch.WordTrace tailWord_1095811 prefixEnd_1095811 562677749484117368122963 := by
  unfold tailWord_1095811
  simp only [CollatzResearch.WordTrace]
  refine ⟨39967510633071371464167287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26645007088714247642778191 39967510633071371464167287)
  ·
    refine ⟨59951265949607057196250931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39967510633071371464167287 59951265949607057196250931)
    ·
      refine ⟨89926898924410585794376397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59951265949607057196250931 89926898924410585794376397)
      ·
        refine ⟨33722587096653969672891149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89926898924410585794376397 33722587096653969672891149)
        ·
          refine ⟨12645970161245238627334181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33722587096653969672891149 12645970161245238627334181)
          ·
            refine ⟨2371119405233482242625159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12645970161245238627334181 2371119405233482242625159)
            ·
              refine ⟨3556679107850223363937739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371119405233482242625159 3556679107850223363937739)
              ·
                refine ⟨5335018661775335045906609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556679107850223363937739 5335018661775335045906609)
                ·
                  refine ⟨4001263996331501284429957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5335018661775335045906609 4001263996331501284429957)
                  ·
                    refine ⟨750236999312156490830617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001263996331501284429957 750236999312156490830617)
                    ·
                      refine ⟨562677749484117368122963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 750236999312156490830617 562677749484117368122963)
                      ·
                        rfl

theorem cell23_1095811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_1095811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095811 prefixEnd_1095811 := by exact prefixLift 1095811
  have htrace : WordTrace (prefixWord ++ tailWord_1095811) baseStart_1095811 baseEnd_1095811 := by
    simpa [prefixWord, tailWord_1095811, baseEnd_1095811] using wordTrace_append hprefix tailTrace_1095811
  have hstable : (prefixWord ++ tailWord_1095811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095811).length < 2 ^ (prefixWord ++ tailWord_1095811).sum := by decide
  have hdescent : baseEnd_1095811 < baseStart_1095811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095828 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1095828 : Nat := 118140960795 + 1095828 * 2 ^ 59
def prefixEnd_1095828 : Nat := 4983230072969 + 3 ^ 40 * 1095828 * 2
def baseEnd_1095828 : Nat := 562686478655243801610385

theorem tailTrace_1095828 : CollatzResearch.WordTrace tailWord_1095828 prefixEnd_1095828 562686478655243801610385 := by
  unfold tailWord_1095828
  simp only [CollatzResearch.WordTrace]
  refine ⟨19984065337004891683768069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26645420449339855578357425 19984065337004891683768069)
  ·
    refine ⟨3747012250688417190706513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19984065337004891683768069 3747012250688417190706513)
    ·
      refine ⟨2810259188016312893029885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3747012250688417190706513 2810259188016312893029885)
      ·
        refine ⟨1053847195506117334886207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2810259188016312893029885 1053847195506117334886207)
        ·
          refine ⟨1580770793259176002329311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053847195506117334886207 1580770793259176002329311)
          ·
            refine ⟨2371156189888764003493967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580770793259176002329311 2371156189888764003493967)
            ·
              refine ⟨3556734284833146005240951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371156189888764003493967 3556734284833146005240951)
              ·
                refine ⟨5335101427249719007861427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556734284833146005240951 5335101427249719007861427)
                ·
                  refine ⟨8002652140874578511792141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335101427249719007861427 8002652140874578511792141)
                  ·
                    refine ⟨3000994552827966941922053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8002652140874578511792141 3000994552827966941922053)
                    ·
                      refine ⟨562686478655243801610385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3000994552827966941922053 562686478655243801610385)
                      ·
                        rfl

theorem cell23_1095828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1095828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095828 prefixEnd_1095828 := by exact prefixLift 1095828
  have htrace : WordTrace (prefixWord ++ tailWord_1095828) baseStart_1095828 baseEnd_1095828 := by
    simpa [prefixWord, tailWord_1095828, baseEnd_1095828] using wordTrace_append hprefix tailTrace_1095828
  have hstable : (prefixWord ++ tailWord_1095828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095828).length < 2 ^ (prefixWord ++ tailWord_1095828).sum := by decide
  have hdescent : baseEnd_1095828 < baseStart_1095828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095831 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1095831 : Nat := 118140960795 + 1095831 * 2 ^ 59
def prefixEnd_1095831 : Nat := 4983230072969 + 3 ^ 40 * 1095831 * 2
def baseEnd_1095831 : Nat := 562688019097207289872871

theorem tailTrace_1095831 : CollatzResearch.WordTrace tailWord_1095831 prefixEnd_1095831 562688019097207289872871 := by
  unfold tailWord_1095831
  simp only [CollatzResearch.WordTrace]
  refine ⟨39968240092998914879895347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26645493395332609919930231 39968240092998914879895347)
  ·
    refine ⟨59952360139498372319843021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39968240092998914879895347 59952360139498372319843021)
    ·
      refine ⟨22482135052311889619941133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59952360139498372319843021 22482135052311889619941133)
      ·
        refine ⟨8430800644616958607477925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22482135052311889619941133 8430800644616958607477925)
        ·
          refine ⟨1580775120865679738902111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8430800644616958607477925 1580775120865679738902111)
          ·
            refine ⟨2371162681298519608353167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580775120865679738902111 2371162681298519608353167)
            ·
              refine ⟨3556744021947779412529751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371162681298519608353167 3556744021947779412529751)
              ·
                refine ⟨5335116032921669118794627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556744021947779412529751 5335116032921669118794627)
                ·
                  refine ⟨8002674049382503678191941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335116032921669118794627 8002674049382503678191941)
                  ·
                    refine ⟨1500501384259219439660989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8002674049382503678191941 1500501384259219439660989)
                    ·
                      refine ⟨562688019097207289872871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1500501384259219439660989 562688019097207289872871)
                      ·
                        rfl

theorem cell23_1095831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1095831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095831 prefixEnd_1095831 := by exact prefixLift 1095831
  have htrace : WordTrace (prefixWord ++ tailWord_1095831) baseStart_1095831 baseEnd_1095831 := by
    simpa [prefixWord, tailWord_1095831, baseEnd_1095831] using wordTrace_append hprefix tailTrace_1095831
  have hstable : (prefixWord ++ tailWord_1095831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095831).length < 2 ^ (prefixWord ++ tailWord_1095831).sum := by decide
  have hdescent : baseEnd_1095831 < baseStart_1095831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095868 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 6]
def baseStart_1095868 : Nat := 118140960795 + 1095868 * 2 ^ 59
def prefixEnd_1095868 : Nat := 4983230072969 + 3 ^ 40 * 1095868 * 2
def baseEnd_1095868 : Nat := 62523001986824849456689

theorem tailTrace_1095868 : CollatzResearch.WordTrace tailWord_1095868 prefixEnd_1095868 62523001986824849456689 := by
  unfold tailWord_1095868
  simp only [CollatzResearch.WordTrace]
  refine ⟨19984794796932435099496129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26646393062576580132661505 19984794796932435099496129)
  ·
    refine ⟨14988596097699326324622097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19984794796932435099496129 14988596097699326324622097)
    ·
      refine ⟨11241447073274494743466573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14988596097699326324622097 11241447073274494743466573)
      ·
        refine ⟨4215542652477935528799965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11241447073274494743466573 4215542652477935528799965)
        ·
          refine ⟨1580828494679225823299987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4215542652477935528799965 1580828494679225823299987)
          ·
            refine ⟨2371242742018838734949981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580828494679225823299987 2371242742018838734949981)
            ·
              refine ⟨889216028257064525606243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2371242742018838734949981 889216028257064525606243)
              ·
                refine ⟨1333824042385596788409365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889216028257064525606243 1333824042385596788409365)
                ·
                  refine ⟨62523001986824849456689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1333824042385596788409365 62523001986824849456689)
                  ·
                    rfl

theorem cell23_1095868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_1095868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095868 prefixEnd_1095868 := by exact prefixLift 1095868
  have htrace : WordTrace (prefixWord ++ tailWord_1095868) baseStart_1095868 baseEnd_1095868 := by
    simpa [prefixWord, tailWord_1095868, baseEnd_1095868] using wordTrace_append hprefix tailTrace_1095868
  have hstable : (prefixWord ++ tailWord_1095868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095868).length < 2 ^ (prefixWord ++ tailWord_1095868).sum := by decide
  have hdescent : baseEnd_1095868 < baseStart_1095868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095906 : List Nat := [3, 3, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1095906 : Nat := 118140960795 + 1095906 * 2 ^ 59
def prefixEnd_1095906 : Nat := 4983230072969 + 3 ^ 40 * 1095906 * 2
def baseEnd_1095906 : Nat := 187575510048764832145009

theorem tailTrace_1095906 : CollatzResearch.WordTrace tailWord_1095906 prefixEnd_1095906 187575510048764832145009 := by
  unfold tailWord_1095906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992743891931800672218893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26647317045151468459250381 9992743891931800672218893)
  ·
    refine ⟨3747278959474425252082085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9992743891931800672218893 3747278959474425252082085)
    ·
      refine ⟨702614804901454734765391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3747278959474425252082085 702614804901454734765391)
      ·
        refine ⟨1053922207352182102148087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702614804901454734765391 1053922207352182102148087)
        ·
          refine ⟨1580883311028273153222131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053922207352182102148087 1580883311028273153222131)
          ·
            refine ⟨2371324966542409729833197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580883311028273153222131 2371324966542409729833197)
            ·
              refine ⟨889246862453403648687449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2371324966542409729833197 889246862453403648687449)
              ·
                refine ⟨666935146840052736515587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889246862453403648687449 666935146840052736515587)
                ·
                  refine ⟨1000402720260079104773381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666935146840052736515587 1000402720260079104773381)
                  ·
                    refine ⟨187575510048764832145009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1000402720260079104773381 187575510048764832145009)
                    ·
                      rfl

theorem cell23_1095906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1095906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095906 prefixEnd_1095906 := by exact prefixLift 1095906
  have htrace : WordTrace (prefixWord ++ tailWord_1095906) baseStart_1095906 baseEnd_1095906 := by
    simpa [prefixWord, tailWord_1095906, baseEnd_1095906] using wordTrace_append hprefix tailTrace_1095906
  have hstable : (prefixWord ++ tailWord_1095906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095906).length < 2 ^ (prefixWord ++ tailWord_1095906).sum := by decide
  have hdescent : baseEnd_1095906 < baseStart_1095906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095912 : List Nat := [2, 1, 4, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_1095912 : Nat := 118140960795 + 1095912 * 2 ^ 59
def prefixEnd_1095912 : Nat := 4983230072969 + 3 ^ 40 * 1095912 * 2
def baseEnd_1095912 : Nat := 562729611030221472959999

theorem tailTrace_1095912 : CollatzResearch.WordTrace tailWord_1095912 prefixEnd_1095912 562729611030221472959999 := by
  unfold tailWord_1095912
  simp only [CollatzResearch.WordTrace]
  refine ⟨19985597202852732856796995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26647462937136977142395993 19985597202852732856796995)
  ·
    refine ⟨29978395804279099285195493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19985597202852732856796995 29978395804279099285195493)
    ·
      refine ⟨5620949213302331115974155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29978395804279099285195493 5620949213302331115974155)
      ·
        refine ⟨8431423819953496673961233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5620949213302331115974155 8431423819953496673961233)
        ·
          refine ⟨6323567864965122505470925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8431423819953496673961233 6323567864965122505470925)
          ·
            refine ⟨2371337949361920939551597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6323567864965122505470925 2371337949361920939551597)
            ·
              refine ⟨889251731010720352331849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2371337949361920939551597 889251731010720352331849)
              ·
                refine ⟨666938798258040264248887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889251731010720352331849 666938798258040264248887)
                ·
                  refine ⟨1000408197387060396373331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666938798258040264248887 1000408197387060396373331)
                  ·
                    refine ⟨1500612296080590594559997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1000408197387060396373331 1500612296080590594559997)
                    ·
                      refine ⟨562729611030221472959999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1500612296080590594559997 562729611030221472959999)
                      ·
                        rfl

theorem cell23_1095912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_1095912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095912 prefixEnd_1095912 := by exact prefixLift 1095912
  have htrace : WordTrace (prefixWord ++ tailWord_1095912) baseStart_1095912 baseEnd_1095912 := by
    simpa [prefixWord, tailWord_1095912, baseEnd_1095912] using wordTrace_append hprefix tailTrace_1095912
  have hstable : (prefixWord ++ tailWord_1095912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095912).length < 2 ^ (prefixWord ++ tailWord_1095912).sum := by decide
  have hdescent : baseEnd_1095912 < baseStart_1095912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095914 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1095914 : Nat := 118140960795 + 1095914 * 2 ^ 59
def prefixEnd_1095914 : Nat := 4983230072969 + 3 ^ 40 * 1095914 * 2
def baseEnd_1095914 : Nat := 562730637991530465134989

theorem tailTrace_1095914 : CollatzResearch.WordTrace tailWord_1095914 prefixEnd_1095914 562730637991530465134989 := by
  unfold tailWord_1095914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992816837924555013791699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26647511567798813370111197 9992816837924555013791699)
  ·
    refine ⟨14989225256886832520687549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9992816837924555013791699 14989225256886832520687549)
    ·
      refine ⟨5620959471332562195257831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14989225256886832520687549 5620959471332562195257831)
      ·
        refine ⟨8431439206998843292886747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5620959471332562195257831 8431439206998843292886747)
        ·
          refine ⟨12647158810498264939330121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8431439206998843292886747 12647158810498264939330121)
          ·
            refine ⟨9485369107873698704497591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12647158810498264939330121 9485369107873698704497591)
            ·
              refine ⟨14228053661810548056746387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9485369107873698704497591 14228053661810548056746387)
              ·
                refine ⟨21342080492715822085119581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14228053661810548056746387 21342080492715822085119581)
                ·
                  refine ⟨8003280184768433281919843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21342080492715822085119581 8003280184768433281919843)
                  ·
                    refine ⟨12004920277152649922879765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8003280184768433281919843 12004920277152649922879765)
                    ·
                      refine ⟨562730637991530465134989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12004920277152649922879765 562730637991530465134989)
                      ·
                        rfl

theorem cell23_1095914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1095914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095914 prefixEnd_1095914 := by exact prefixLift 1095914
  have htrace : WordTrace (prefixWord ++ tailWord_1095914) baseStart_1095914 baseEnd_1095914 := by
    simpa [prefixWord, tailWord_1095914, baseEnd_1095914] using wordTrace_append hprefix tailTrace_1095914
  have hstable : (prefixWord ++ tailWord_1095914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095914).length < 2 ^ (prefixWord ++ tailWord_1095914).sum := by decide
  have hdescent : baseEnd_1095914 < baseStart_1095914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1095951 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 3]
def baseStart_1095951 : Nat := 118140960795 + 1095951 * 2 ^ 59
def prefixEnd_1095951 : Nat := 4983230072969 + 3 ^ 40 * 1095951 * 2
def baseEnd_1095951 : Nat := 562749636775746820372319

theorem tailTrace_1095951 : CollatzResearch.WordTrace tailWord_1095951 prefixEnd_1095951 562749636775746820372319 := by
  unfold tailWord_1095951
  simp only [CollatzResearch.WordTrace]
  refine ⟨39972616852564175374263707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26648411235042783582842471 39972616852564175374263707)
  ·
    refine ⟨59958925278846263061395561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39972616852564175374263707 59958925278846263061395561)
    ·
      refine ⟨44969193959134697296046671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59958925278846263061395561 44969193959134697296046671)
      ·
        refine ⟨67453790938702045944070007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44969193959134697296046671 67453790938702045944070007)
        ·
          refine ⟨101180686408053068916105011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67453790938702045944070007 101180686408053068916105011)
          ·
            refine ⟨151771029612079603374157517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101180686408053068916105011 151771029612079603374157517)
            ·
              refine ⟨56914136104529851265309069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151771029612079603374157517 56914136104529851265309069)
              ·
                refine ⟨21342801039198694224490901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56914136104529851265309069 21342801039198694224490901)
                ·
                  refine ⟨1000443798712438791773011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21342801039198694224490901 1000443798712438791773011)
                  ·
                    refine ⟨1500665698068658187659517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1000443798712438791773011 1500665698068658187659517)
                    ·
                      refine ⟨562749636775746820372319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1500665698068658187659517 562749636775746820372319)
                      ·
                        rfl

theorem cell23_1095951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 3].length) (baseStart_1095951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1095951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1095951 prefixEnd_1095951 := by exact prefixLift 1095951
  have htrace : WordTrace (prefixWord ++ tailWord_1095951) baseStart_1095951 baseEnd_1095951 := by
    simpa [prefixWord, tailWord_1095951, baseEnd_1095951] using wordTrace_append hprefix tailTrace_1095951
  have hstable : (prefixWord ++ tailWord_1095951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1095951).length < 2 ^ (prefixWord ++ tailWord_1095951).sum := by decide
  have hdescent : baseEnd_1095951 < baseStart_1095951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1095951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096008 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_1096008 : Nat := 118140960795 + 1096008 * 2 ^ 59
def prefixEnd_1096008 : Nat := 4983230072969 + 3 ^ 40 * 1096008 * 2
def baseEnd_1096008 : Nat := 562778905173053097359557

theorem tailTrace_1096008 : CollatzResearch.WordTrace tailWord_1096008 prefixEnd_1096008 562778905173053097359557 := by
  unfold tailWord_1096008
  simp only [CollatzResearch.WordTrace]
  refine ⟨19987347906678837054544339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26649797208905116072725785 19987347906678837054544339)
  ·
    refine ⟨29981021860018255581816509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19987347906678837054544339 29981021860018255581816509)
    ·
      refine ⟨11242883197506845843181191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29981021860018255581816509 11242883197506845843181191)
      ·
        refine ⟨16864324796260268764771787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11242883197506845843181191 16864324796260268764771787)
        ·
          refine ⟨25296487194390403147157681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16864324796260268764771787 25296487194390403147157681)
          ·
            refine ⟨18972365395792802360368261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25296487194390403147157681 18972365395792802360368261)
            ·
              refine ⟨3557318511711150442569049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18972365395792802360368261 3557318511711150442569049)
              ·
                refine ⟨2667988883783362831926787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3557318511711150442569049 2667988883783362831926787)
                ·
                  refine ⟨4001983325675044247890181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667988883783362831926787 4001983325675044247890181)
                  ·
                    refine ⟨750371873564070796479409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001983325675044247890181 750371873564070796479409)
                    ·
                      refine ⟨562778905173053097359557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 750371873564070796479409 562778905173053097359557)
                      ·
                        rfl

theorem cell23_1096008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_1096008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096008 prefixEnd_1096008 := by exact prefixLift 1096008
  have htrace : WordTrace (prefixWord ++ tailWord_1096008) baseStart_1096008 baseEnd_1096008 := by
    simpa [prefixWord, tailWord_1096008, baseEnd_1096008] using wordTrace_append hprefix tailTrace_1096008
  have hstable : (prefixWord ++ tailWord_1096008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096008).length < 2 ^ (prefixWord ++ tailWord_1096008).sum := by decide
  have hdescent : baseEnd_1096008 < baseStart_1096008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096024 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1096024 : Nat := 118140960795 + 1096024 * 2 ^ 59
def prefixEnd_1096024 : Nat := 4983230072969 + 3 ^ 40 * 1096024 * 2
def baseEnd_1096024 : Nat := 562787120863525034759483

theorem tailTrace_1096024 : CollatzResearch.WordTrace tailWord_1096024 prefixEnd_1096024 562787120863525034759483 := by
  unfold tailWord_1096024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19987639690649854420835563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26650186254199805894447417 19987639690649854420835563)
  ·
    refine ⟨29981459535974781631253345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19987639690649854420835563 29981459535974781631253345)
    ·
      refine ⟨22486094651981086223440009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29981459535974781631253345 22486094651981086223440009)
      ·
        refine ⟨16864570988985814667580007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22486094651981086223440009 16864570988985814667580007)
        ·
          refine ⟨25296856483478722001370011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16864570988985814667580007 25296856483478722001370011)
          ·
            refine ⟨37945284725218083002055017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25296856483478722001370011 37945284725218083002055017)
            ·
              refine ⟨28458963543913562251541263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37945284725218083002055017 28458963543913562251541263)
              ·
                refine ⟨42688445315870343377311895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28458963543913562251541263 42688445315870343377311895)
                ·
                  refine ⟨64032667973805515065967843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42688445315870343377311895 64032667973805515065967843)
                  ·
                    refine ⟨96049001960708272598951765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64032667973805515065967843 96049001960708272598951765)
                    ·
                      refine ⟨562787120863525034759483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 96049001960708272598951765 562787120863525034759483)
                      ·
                        rfl

theorem cell23_1096024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1096024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096024 prefixEnd_1096024 := by exact prefixLift 1096024
  have htrace : WordTrace (prefixWord ++ tailWord_1096024) baseStart_1096024 baseEnd_1096024 := by
    simpa [prefixWord, tailWord_1096024, baseEnd_1096024] using wordTrace_append hprefix tailTrace_1096024
  have hstable : (prefixWord ++ tailWord_1096024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096024).length < 2 ^ (prefixWord ++ tailWord_1096024).sum := by decide
  have hdescent : baseEnd_1096024 < baseStart_1096024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096041 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 3]
def baseStart_1096041 : Nat := 118140960795 + 1096041 * 2 ^ 59
def prefixEnd_1096041 : Nat := 4983230072969 + 3 ^ 40 * 1096041 * 2
def baseEnd_1096041 : Nat := 562795850034651468246905

theorem tailTrace_1096041 : CollatzResearch.WordTrace tailWord_1096041 prefixEnd_1096041 562795850034651468246905 := by
  unfold tailWord_1096041
  simp only [CollatzResearch.WordTrace]
  refine ⟨39975899422238120745039977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26650599614825413830026651 39975899422238120745039977)
  ·
    refine ⟨29981924566678590558779983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39975899422238120745039977 29981924566678590558779983)
    ·
      refine ⟨44972886850017885838169975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29981924566678590558779983 44972886850017885838169975)
      ·
        refine ⟨67459330275026828757254963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44972886850017885838169975 67459330275026828757254963)
        ·
          refine ⟨101188995412540243135882445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67459330275026828757254963 101188995412540243135882445)
          ·
            refine ⟨37945873279702591175955917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101188995412540243135882445 37945873279702591175955917)
            ·
              refine ⟨14229702479888471690983469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37945873279702591175955917 14229702479888471690983469)
              ·
                refine ⟨5336138429958176884118801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14229702479888471690983469 5336138429958176884118801)
                ·
                  refine ⟨4002103822468632663089101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5336138429958176884118801 4002103822468632663089101)
                  ·
                    refine ⟨1500788933425737248658413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4002103822468632663089101 1500788933425737248658413)
                    ·
                      refine ⟨562795850034651468246905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1500788933425737248658413 562795850034651468246905)
                      ·
                        rfl

theorem cell23_1096041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_1096041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096041 prefixEnd_1096041 := by exact prefixLift 1096041
  have htrace : WordTrace (prefixWord ++ tailWord_1096041) baseStart_1096041 baseEnd_1096041 := by
    simpa [prefixWord, tailWord_1096041, baseEnd_1096041] using wordTrace_append hprefix tailTrace_1096041
  have hstable : (prefixWord ++ tailWord_1096041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096041).length < 2 ^ (prefixWord ++ tailWord_1096041).sum := by decide
  have hdescent : baseEnd_1096041 < baseStart_1096041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096042 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1096042 : Nat := 118140960795 + 1096042 * 2 ^ 59
def prefixEnd_1096042 : Nat := 4983230072969 + 3 ^ 40 * 1096042 * 2
def baseEnd_1096042 : Nat := 562796363515305964334401

theorem tailTrace_1096042 : CollatzResearch.WordTrace tailWord_1096042 prefixEnd_1096042 562796363515305964334401 := by
  unfold tailWord_1096042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9993983973808624478956595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26650623930156331943884253 9993983973808624478956595)
  ·
    refine ⟨14990975960712936718434893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9993983973808624478956595 14990975960712936718434893)
    ·
      refine ⟨5621615985267351269413085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14990975960712936718434893 5621615985267351269413085)
      ·
        refine ⟨2108105994475256726029907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5621615985267351269413085 2108105994475256726029907)
        ·
          refine ⟨3162158991712885089044861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108105994475256726029907 3162158991712885089044861)
          ·
            refine ⟨1185809621892331908391823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3162158991712885089044861 1185809621892331908391823)
            ·
              refine ⟨1778714432838497862587735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185809621892331908391823 1778714432838497862587735)
              ·
                refine ⟨2668071649257746793881603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778714432838497862587735 2668071649257746793881603)
                ·
                  refine ⟨4002107473886620190822405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668071649257746793881603 4002107473886620190822405)
                  ·
                    refine ⟨750395151353741285779201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002107473886620190822405 750395151353741285779201)
                    ·
                      refine ⟨562796363515305964334401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 750395151353741285779201 562796363515305964334401)
                      ·
                        rfl

theorem cell23_1096042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1096042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096042 prefixEnd_1096042 := by exact prefixLift 1096042
  have htrace : WordTrace (prefixWord ++ tailWord_1096042) baseStart_1096042 baseEnd_1096042 := by
    simpa [prefixWord, tailWord_1096042, baseEnd_1096042] using wordTrace_append hprefix tailTrace_1096042
  have hstable : (prefixWord ++ tailWord_1096042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096042).length < 2 ^ (prefixWord ++ tailWord_1096042).sum := by decide
  have hdescent : baseEnd_1096042 < baseStart_1096042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096061 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1096061 : Nat := 118140960795 + 1096061 * 2 ^ 59
def prefixEnd_1096061 : Nat := 4983230072969 + 3 ^ 40 * 1096061 * 2
def baseEnd_1096061 : Nat := 187602039882580463332271

theorem tailTrace_1096061 : CollatzResearch.WordTrace tailWord_1096061 prefixEnd_1096061 187602039882580463332271 := by
  unfold tailWord_1096061
  simp only [CollatzResearch.WordTrace]
  refine ⟨39976628882165664160768037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26651085921443776107178691 39976628882165664160768037)
  ·
    refine ⟨7495617915406062030144007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39976628882165664160768037 7495617915406062030144007)
    ·
      refine ⟨11243426873109093045216011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7495617915406062030144007 11243426873109093045216011)
      ·
        refine ⟨16865140309663639567824017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11243426873109093045216011 16865140309663639567824017)
        ·
          refine ⟨12648855232247729675868013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16865140309663639567824017 12648855232247729675868013)
          ·
            refine ⟨4743320712092898628450505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12648855232247729675868013 4743320712092898628450505)
            ·
              refine ⟨3557490534069673971337879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4743320712092898628450505 3557490534069673971337879)
              ·
                refine ⟨5336235801104510957006819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557490534069673971337879 5336235801104510957006819)
                ·
                  refine ⟨8004353701656766435510229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5336235801104510957006819 8004353701656766435510229)
                  ·
                    refine ⟨187602039882580463332271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8004353701656766435510229 187602039882580463332271)
                    ·
                      rfl

theorem cell23_1096061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1096061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096061 prefixEnd_1096061 := by exact prefixLift 1096061
  have htrace : WordTrace (prefixWord ++ tailWord_1096061) baseStart_1096061 baseEnd_1096061 := by
    simpa [prefixWord, tailWord_1096061, baseEnd_1096061] using wordTrace_append hprefix tailTrace_1096061
  have hstable : (prefixWord ++ tailWord_1096061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096061).length < 2 ^ (prefixWord ++ tailWord_1096061).sum := by decide
  have hdescent : baseEnd_1096061 < baseStart_1096061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096065 : List Nat := [1, 2, 4, 3, 1, 1, 3, 3, 5]
def baseStart_1096065 : Nat := 118140960795 + 1096065 * 2 ^ 59
def prefixEnd_1096065 : Nat := 4983230072969 + 3 ^ 40 * 1096065 * 2
def baseEnd_1096065 : Nat := 62534241507817708260755

theorem tailTrace_1096065 : CollatzResearch.WordTrace tailWord_1096065 prefixEnd_1096065 62534241507817708260755 := by
  unfold tailWord_1096065
  simp only [CollatzResearch.WordTrace]
  refine ⟨39976774774151172843913649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26651183182767448562609099 39976774774151172843913649)
  ·
    refine ⟨29982581080613379632935237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39976774774151172843913649 29982581080613379632935237)
    ·
      refine ⟨5621733952615008681175357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29982581080613379632935237 5621733952615008681175357)
      ·
        refine ⟨2108150232230628255440759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5621733952615008681175357 2108150232230628255440759)
        ·
          refine ⟨3162225348345942383161139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108150232230628255440759 3162225348345942383161139)
          ·
            refine ⟨4743338022518913574741709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162225348345942383161139 4743338022518913574741709)
            ·
              refine ⟨1778751758444592590528141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4743338022518913574741709 1778751758444592590528141)
              ·
                refine ⟨667031909416722221448053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1778751758444592590528141 667031909416722221448053)
                ·
                  refine ⟨62534241507817708260755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 667031909416722221448053 62534241507817708260755)
                  ·
                    rfl

theorem cell23_1096065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 5].length) (baseStart_1096065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096065 prefixEnd_1096065 := by exact prefixLift 1096065
  have htrace : WordTrace (prefixWord ++ tailWord_1096065) baseStart_1096065 baseEnd_1096065 := by
    simpa [prefixWord, tailWord_1096065, baseEnd_1096065] using wordTrace_append hprefix tailTrace_1096065
  have hstable : (prefixWord ++ tailWord_1096065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096065).length < 2 ^ (prefixWord ++ tailWord_1096065).sum := by decide
  have hdescent : baseEnd_1096065 < baseStart_1096065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096071 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1096071 : Nat := 118140960795 + 1096071 * 2 ^ 59
def prefixEnd_1096071 : Nat := 4983230072969 + 3 ^ 40 * 1096071 * 2
def baseEnd_1096071 : Nat := 562811254454286350871767

theorem tailTrace_1096071 : CollatzResearch.WordTrace tailWord_1096071 prefixEnd_1096071 562811254454286350871767 := by
  unfold tailWord_1096071
  simp only [CollatzResearch.WordTrace]
  refine ⟨39976993612129435868632067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26651329074752957245754711 39976993612129435868632067)
  ·
    refine ⟨59965490418194153802948101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39976993612129435868632067 59965490418194153802948101)
    ·
      refine ⟨11243529453411403838052769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59965490418194153802948101 11243529453411403838052769)
      ·
        refine ⟨8432647090058552878539577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11243529453411403838052769 8432647090058552878539577)
        ·
          refine ⟨6324485317543914658904683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8432647090058552878539577 6324485317543914658904683)
          ·
            refine ⟨9486727976315871988357025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6324485317543914658904683 9486727976315871988357025)
            ·
              refine ⟨7115045982236903991267769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9486727976315871988357025 7115045982236903991267769)
              ·
                refine ⟨5336284486677677993450827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7115045982236903991267769 5336284486677677993450827)
                ·
                  refine ⟨8004426730016516990176241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5336284486677677993450827 8004426730016516990176241)
                  ·
                    refine ⟨6003320047512387742632181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8004426730016516990176241 6003320047512387742632181)
                    ·
                      refine ⟨562811254454286350871767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6003320047512387742632181 562811254454286350871767)
                      ·
                        rfl

theorem cell23_1096071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1096071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096071 prefixEnd_1096071 := by exact prefixLift 1096071
  have htrace : WordTrace (prefixWord ++ tailWord_1096071) baseStart_1096071 baseEnd_1096071 := by
    simpa [prefixWord, tailWord_1096071, baseEnd_1096071] using wordTrace_append hprefix tailTrace_1096071
  have hstable : (prefixWord ++ tailWord_1096071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096071).length < 2 ^ (prefixWord ++ tailWord_1096071).sum := by decide
  have hdescent : baseEnd_1096071 < baseStart_1096071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096078 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1096078 : Nat := 118140960795 + 1096078 * 2 ^ 59
def prefixEnd_1096078 : Nat := 4983230072969 + 3 ^ 40 * 1096078 * 2
def baseEnd_1096078 : Nat := 187604949606289274494745

theorem tailTrace_1096078 : CollatzResearch.WordTrace tailWord_1096078 prefixEnd_1096078 187604949606289274494745 := by
  unfold tailWord_1096078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4997156115388009508017111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26651499282069384042757925 4997156115388009508017111)
  ·
    refine ⟨7495734173082014262025667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4997156115388009508017111 7495734173082014262025667)
    ·
      refine ⟨11243601259623021393038501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7495734173082014262025667 11243601259623021393038501)
      ·
        refine ⟨2108175236179316511194719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11243601259623021393038501 2108175236179316511194719)
        ·
          refine ⟨3162262854268974766792079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108175236179316511194719 3162262854268974766792079)
          ·
            refine ⟨4743394281403462150188119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162262854268974766792079 4743394281403462150188119)
            ·
              refine ⟨7115091422105193225282179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4743394281403462150188119 7115091422105193225282179)
              ·
                refine ⟨10672637133157789837923269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7115091422105193225282179 10672637133157789837923269)
                ·
                  refine ⟨2001119462467085594610613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10672637133157789837923269 2001119462467085594610613)
                  ·
                    refine ⟨187604949606289274494745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2001119462467085594610613 187604949606289274494745)
                    ·
                      rfl

theorem cell23_1096078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1096078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096078 prefixEnd_1096078 := by exact prefixLift 1096078
  have htrace : WordTrace (prefixWord ++ tailWord_1096078) baseStart_1096078 baseEnd_1096078 := by
    simpa [prefixWord, tailWord_1096078, baseEnd_1096078] using wordTrace_append hprefix tailTrace_1096078
  have hstable : (prefixWord ++ tailWord_1096078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096078).length < 2 ^ (prefixWord ++ tailWord_1096078).sum := by decide
  have hdescent : baseEnd_1096078 < baseStart_1096078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096088 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1096088 : Nat := 118140960795 + 1096088 * 2 ^ 59
def prefixEnd_1096088 : Nat := 4983230072969 + 3 ^ 40 * 1096088 * 2
def baseEnd_1096088 : Nat := 562819983625412784359189

theorem tailTrace_1096088 : CollatzResearch.WordTrace tailWord_1096088 prefixEnd_1096088 562819983625412784359189 := by
  unfold tailWord_1096088
  simp only [CollatzResearch.WordTrace]
  refine ⟨19988806826533923886000459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26651742435378565181333945 19988806826533923886000459)
  ·
    refine ⟨29983210239800885829000689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19988806826533923886000459 29983210239800885829000689)
    ·
      refine ⟨22487407679850664371750517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29983210239800885829000689 22487407679850664371750517)
      ·
        refine ⟨2108194469985999784851611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22487407679850664371750517 2108194469985999784851611)
        ·
          refine ⟨3162291704978999677277417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108194469985999784851611 3162291704978999677277417)
          ·
            refine ⟨2371718778734249757958063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3162291704978999677277417 2371718778734249757958063)
            ·
              refine ⟨3557578168101374636937095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371718778734249757958063 3557578168101374636937095)
              ·
                refine ⟨5336367252152061955405643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557578168101374636937095 5336367252152061955405643)
                ·
                  refine ⟨8004550878228092933108465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5336367252152061955405643 8004550878228092933108465)
                  ·
                    refine ⟨6003413158671069699831349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8004550878228092933108465 6003413158671069699831349)
                    ·
                      refine ⟨562819983625412784359189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6003413158671069699831349 562819983625412784359189)
                      ·
                        rfl

theorem cell23_1096088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1096088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096088 prefixEnd_1096088 := by exact prefixLift 1096088
  have htrace : WordTrace (prefixWord ++ tailWord_1096088) baseStart_1096088 baseEnd_1096088 := by
    simpa [prefixWord, tailWord_1096088, baseEnd_1096088] using wordTrace_append hprefix tailTrace_1096088
  have hstable : (prefixWord ++ tailWord_1096088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096088).length < 2 ^ (prefixWord ++ tailWord_1096088).sum := by decide
  have hdescent : baseEnd_1096088 < baseStart_1096088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096098 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1096098 : Nat := 118140960795 + 1096098 * 2 ^ 59
def prefixEnd_1096098 : Nat := 4983230072969 + 3 ^ 40 * 1096098 * 2
def baseEnd_1096098 : Nat := 562825118431957745234143

theorem tailTrace_1096098 : CollatzResearch.WordTrace tailWord_1096098 prefixEnd_1096098 562825118431957745234143 := by
  unfold tailWord_1096098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9994494595757904869966237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26651985588687746319909965 9994494595757904869966237)
  ·
    refine ⟨3747935473409214326237339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9994494595757904869966237 3747935473409214326237339)
    ·
      refine ⟨5621903210113821489356009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3747935473409214326237339 5621903210113821489356009)
      ·
        refine ⟨4216427407585366117017007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5621903210113821489356009 4216427407585366117017007)
        ·
          refine ⟨6324641111378049175525511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4216427407585366117017007 6324641111378049175525511)
          ·
            refine ⟨9486961667067073763288267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6324641111378049175525511 9486961667067073763288267)
            ·
              refine ⟨14230442500600610644932401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9486961667067073763288267 14230442500600610644932401)
              ·
                refine ⟨10672831875450457983699301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14230442500600610644932401 10672831875450457983699301)
                ·
                  refine ⟨2001155976646960871943619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10672831875450457983699301 2001155976646960871943619)
                  ·
                    refine ⟨3001733964970441307915429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2001155976646960871943619 3001733964970441307915429)
                    ·
                      refine ⟨562825118431957745234143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3001733964970441307915429 562825118431957745234143)
                      ·
                        rfl

theorem cell23_1096098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1096098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096098 prefixEnd_1096098 := by exact prefixLift 1096098
  have htrace : WordTrace (prefixWord ++ tailWord_1096098) baseStart_1096098 baseEnd_1096098 := by
    simpa [prefixWord, tailWord_1096098, baseEnd_1096098] using wordTrace_append hprefix tailTrace_1096098
  have hstable : (prefixWord ++ tailWord_1096098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096098).length < 2 ^ (prefixWord ++ tailWord_1096098).sum := by decide
  have hdescent : baseEnd_1096098 < baseStart_1096098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096138 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 6]
def baseStart_1096138 : Nat := 118140960795 + 1096138 * 2 ^ 59
def prefixEnd_1096138 : Nat := 4983230072969 + 3 ^ 40 * 1096138 * 2
def baseEnd_1096138 : Nat := 62538406406459732081551

theorem tailTrace_1096138 : CollatzResearch.WordTrace tailWord_1096138 prefixEnd_1096138 62538406406459732081551 := by
  unfold tailWord_1096138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9994859325721676577830267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26652958201924470874214045 9994859325721676577830267)
  ·
    refine ⟨14992288988582514866745401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9994859325721676577830267 14992288988582514866745401)
    ·
      refine ⟨11244216741436886150059051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14992288988582514866745401 11244216741436886150059051)
      ·
        refine ⟨16866325112155329225088577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11244216741436886150059051 16866325112155329225088577)
        ·
          refine ⟨12649743834116496918816433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16866325112155329225088577 12649743834116496918816433)
          ·
            refine ⟨9487307875587372689112325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12649743834116496918816433 9487307875587372689112325)
            ·
              refine ⟨1778870226672632379208561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9487307875587372689112325 1778870226672632379208561)
              ·
                refine ⟨1334152670004474284406421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1778870226672632379208561 1334152670004474284406421)
                ·
                  refine ⟨62538406406459732081551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1334152670004474284406421 62538406406459732081551)
                  ·
                    rfl

theorem cell23_1096138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_1096138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096138 prefixEnd_1096138 := by exact prefixLift 1096138
  have htrace : WordTrace (prefixWord ++ tailWord_1096138) baseStart_1096138 baseEnd_1096138 := by
    simpa [prefixWord, tailWord_1096138, baseEnd_1096138] using wordTrace_append hprefix tailTrace_1096138
  have hstable : (prefixWord ++ tailWord_1096138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096138).length < 2 ^ (prefixWord ++ tailWord_1096138).sum := by decide
  have hdescent : baseEnd_1096138 < baseStart_1096138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096161 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1096161 : Nat := 118140960795 + 1096161 * 2 ^ 59
def prefixEnd_1096161 : Nat := 4983230072969 + 3 ^ 40 * 1096161 * 2
def baseEnd_1096161 : Nat := 562857467713190998746353

theorem tailTrace_1096161 : CollatzResearch.WordTrace tailWord_1096161 prefixEnd_1096161 562857467713190998746353 := by
  unfold tailWord_1096161
  simp only [CollatzResearch.WordTrace]
  refine ⟨39980276181803381239408337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26653517454535587492938891 39980276181803381239408337)
  ·
    refine ⟨29985207136352535929556253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39980276181803381239408337 29985207136352535929556253)
    ·
      refine ⟨11244452676132200973583595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29985207136352535929556253 11244452676132200973583595)
      ·
        refine ⟨16866679014198301460375393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11244452676132200973583595 16866679014198301460375393)
        ·
          refine ⟨12650009260648726095281545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16866679014198301460375393 12650009260648726095281545)
          ·
            refine ⟨9487506945486544571461159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12650009260648726095281545 9487506945486544571461159)
            ·
              refine ⟨14231260418229816857191739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9487506945486544571461159 14231260418229816857191739)
              ·
                refine ⟨21346890627344725285787609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14231260418229816857191739 21346890627344725285787609)
                ·
                  refine ⟨16010167970508543964340707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21346890627344725285787609 16010167970508543964340707)
                  ·
                    refine ⟨24015251955762815946511061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16010167970508543964340707 24015251955762815946511061)
                    ·
                      refine ⟨562857467713190998746353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24015251955762815946511061 562857467713190998746353)
                      ·
                        rfl

theorem cell23_1096161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1096161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096161 prefixEnd_1096161 := by exact prefixLift 1096161
  have htrace : WordTrace (prefixWord ++ tailWord_1096161) baseStart_1096161 baseEnd_1096161 := by
    simpa [prefixWord, tailWord_1096161, baseEnd_1096161] using wordTrace_append hprefix tailTrace_1096161
  have hstable : (prefixWord ++ tailWord_1096161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096161).length < 2 ^ (prefixWord ++ tailWord_1096161).sum := by decide
  have hdescent : baseEnd_1096161 < baseStart_1096161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096168 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1096168 : Nat := 118140960795 + 1096168 * 2 ^ 59
def prefixEnd_1096168 : Nat := 4983230072969 + 3 ^ 40 * 1096168 * 2
def baseEnd_1096168 : Nat := 187620354025924157119607

theorem tailTrace_1096168 : CollatzResearch.WordTrace tailWord_1096168 prefixEnd_1096168 187620354025924157119607 := by
  unfold tailWord_1096168
  simp only [CollatzResearch.WordTrace]
  refine ⟨19990265746389010717456579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26653687661852014289942105 19990265746389010717456579)
  ·
    refine ⟨29985398619583516076184869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19990265746389010717456579 29985398619583516076184869)
    ·
      refine ⟨5622262241171909264284663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29985398619583516076184869 5622262241171909264284663)
      ·
        refine ⟨8433393361757863896426995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5622262241171909264284663 8433393361757863896426995)
        ·
          refine ⟨12650090042636795844640493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8433393361757863896426995 12650090042636795844640493)
          ·
            refine ⟨4743783765988798441740185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12650090042636795844640493 4743783765988798441740185)
            ·
              refine ⟨3557837824491598831305139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4743783765988798441740185 3557837824491598831305139)
              ·
                refine ⟨5336756736737398246957709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557837824491598831305139 5336756736737398246957709)
                ·
                  refine ⟨2001283776276524342609141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5336756736737398246957709 2001283776276524342609141)
                  ·
                    refine ⟨187620354025924157119607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2001283776276524342609141 187620354025924157119607)
                    ·
                      rfl

theorem cell23_1096168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1096168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096168 prefixEnd_1096168 := by exact prefixLift 1096168
  have htrace : WordTrace (prefixWord ++ tailWord_1096168) baseStart_1096168 baseEnd_1096168 := by
    simpa [prefixWord, tailWord_1096168, baseEnd_1096168] using wordTrace_append hprefix tailTrace_1096168
  have hstable : (prefixWord ++ tailWord_1096168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096168).length < 2 ^ (prefixWord ++ tailWord_1096168).sum := by decide
  have hdescent : baseEnd_1096168 < baseStart_1096168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096185 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 1, 5]
def baseStart_1096185 : Nat := 118140960795 + 1096185 * 2 ^ 59
def prefixEnd_1096185 : Nat := 4983230072969 + 3 ^ 40 * 1096185 * 2
def baseEnd_1096185 : Nat := 187623263749632968282081

theorem tailTrace_1096185 : CollatzResearch.WordTrace tailWord_1096185 prefixEnd_1096185 187623263749632968282081 := by
  unfold tailWord_1096185
  simp only [CollatzResearch.WordTrace]
  refine ⟨39981151533716433338282009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26654101022477622225521339 39981151533716433338282009)
  ·
    refine ⟨29985863650287325003711507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39981151533716433338282009 29985863650287325003711507)
    ·
      refine ⟨44978795475430987505567261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29985863650287325003711507 44978795475430987505567261)
      ·
        refine ⟨16867048303286620314587723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44978795475430987505567261 16867048303286620314587723)
        ·
          refine ⟨25300572454929930471881585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16867048303286620314587723 25300572454929930471881585)
          ·
            refine ⟨18975429341197447853911189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25300572454929930471881585 18975429341197447853911189)
            ·
              refine ⟨889473250368630368152087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18975429341197447853911189 889473250368630368152087)
              ·
                refine ⟨1334209875552945552228131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889473250368630368152087 1334209875552945552228131)
                ·
                  refine ⟨2001314813329418328342197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334209875552945552228131 2001314813329418328342197)
                  ·
                    refine ⟨187623263749632968282081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2001314813329418328342197 187623263749632968282081)
                    ·
                      rfl

theorem cell23_1096185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 5].length) (baseStart_1096185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096185 prefixEnd_1096185 := by exact prefixLift 1096185
  have htrace : WordTrace (prefixWord ++ tailWord_1096185) baseStart_1096185 baseEnd_1096185 := by
    simpa [prefixWord, tailWord_1096185, baseEnd_1096185] using wordTrace_append hprefix tailTrace_1096185
  have hstable : (prefixWord ++ tailWord_1096185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096185).length < 2 ^ (prefixWord ++ tailWord_1096185).sum := by decide
  have hdescent : baseEnd_1096185 < baseStart_1096185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096211 : List Nat := [1, 1, 1, 2, 1, 5, 2, 10]
def baseStart_1096211 : Nat := 118140960795 + 1096211 * 2 ^ 59
def prefixEnd_1096211 : Nat := 4983230072969 + 3 ^ 40 * 1096211 * 2
def baseEnd_1096211 : Nat := 20847523768367251967449

theorem tailTrace_1096211 : CollatzResearch.WordTrace tailWord_1096211 prefixEnd_1096211 20847523768367251967449 := by
  unfold tailWord_1096211
  simp only [CollatzResearch.WordTrace]
  refine ⟨39982099831622239778728487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26654733221081493185818991 39982099831622239778728487)
  ·
    refine ⟨59973149747433359668092731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39982099831622239778728487 59973149747433359668092731)
    ·
      refine ⟨89959724621150039502139097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59973149747433359668092731 89959724621150039502139097)
      ·
        refine ⟨67469793465862529626604323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89959724621150039502139097 67469793465862529626604323)
        ·
          refine ⟨101204690198793794439906485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67469793465862529626604323 101204690198793794439906485)
          ·
            refine ⟨9487939706136918228741233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101204690198793794439906485 9487939706136918228741233)
            ·
              refine ⟨7115954779602688671555925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9487939706136918228741233 7115954779602688671555925)
              ·
                refine ⟨20847523768367251967449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7115954779602688671555925 20847523768367251967449)
                ·
                  rfl

theorem cell23_1096211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 10].length) (baseStart_1096211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096211 prefixEnd_1096211 := by exact prefixLift 1096211
  have htrace : WordTrace (prefixWord ++ tailWord_1096211) baseStart_1096211 baseEnd_1096211 := by
    simpa [prefixWord, tailWord_1096211, baseEnd_1096211] using wordTrace_append hprefix tailTrace_1096211
  have hstable : (prefixWord ++ tailWord_1096211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096211).length < 2 ^ (prefixWord ++ tailWord_1096211).sum := by decide
  have hdescent : baseEnd_1096211 < baseStart_1096211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096255 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 3]
def baseStart_1096255 : Nat := 118140960795 + 1096255 * 2 ^ 59
def prefixEnd_1096255 : Nat := 4983230072969 + 3 ^ 40 * 1096255 * 2
def baseEnd_1096255 : Nat := 562905734894713630970921

theorem tailTrace_1096255 : CollatzResearch.WordTrace tailWord_1096255 prefixEnd_1096255 562905734894713630970921 := by
  unfold tailWord_1096255
  simp only [CollatzResearch.WordTrace]
  refine ⟨39983704643462835293330219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26655803095641890195553479 39983704643462835293330219)
  ·
    refine ⟨59975556965194252939995329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39983704643462835293330219 59975556965194252939995329)
    ·
      refine ⟨44981667723895689704996497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59975556965194252939995329 44981667723895689704996497)
      ·
        refine ⟨33736250792921767278747373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44981667723895689704996497 33736250792921767278747373)
        ·
          refine ⟨12651094047345662729530265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33736250792921767278747373 12651094047345662729530265)
          ·
            refine ⟨9488320535509247047147699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12651094047345662729530265 9488320535509247047147699)
            ·
              refine ⟨14232480803263870570721549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9488320535509247047147699 14232480803263870570721549)
              ·
                refine ⟨5337180301223951464020581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14232480803263870570721549 5337180301223951464020581)
                ·
                  refine ⟨1000721306479490899503859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5337180301223951464020581 1000721306479490899503859)
                  ·
                    refine ⟨1501081959719236349255789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1000721306479490899503859 1501081959719236349255789)
                    ·
                      refine ⟨562905734894713630970921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1501081959719236349255789 562905734894713630970921)
                      ·
                        rfl

theorem cell23_1096255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_1096255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096255 prefixEnd_1096255 := by exact prefixLift 1096255
  have htrace : WordTrace (prefixWord ++ tailWord_1096255) baseStart_1096255 baseEnd_1096255 := by
    simpa [prefixWord, tailWord_1096255, baseEnd_1096255] using wordTrace_append hprefix tailTrace_1096255
  have hstable : (prefixWord ++ tailWord_1096255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096255).length < 2 ^ (prefixWord ++ tailWord_1096255).sum := by decide
  have hdescent : baseEnd_1096255 < baseStart_1096255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096262 : List Nat := [6, 1, 1, 1, 2, 2, 2, 8]
def baseStart_1096262 : Nat := 118140960795 + 1096262 * 2 ^ 59
def prefixEnd_1096262 : Nat := 4983230072969 + 3 ^ 40 * 1096262 * 2
def baseEnd_1096262 : Nat := 20848493676270189021607

theorem tailTrace_1096262 : CollatzResearch.WordTrace tailWord_1096262 prefixEnd_1096262 20848493676270189021607 := by
  unfold tailWord_1096262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249498748576171109026095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26655973302958316992556693 1249498748576171109026095)
  ·
    refine ⟨1874248122864256663539143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1249498748576171109026095 1874248122864256663539143)
    ·
      refine ⟨2811372184296384995308715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874248122864256663539143 2811372184296384995308715)
      ·
        refine ⟨4217058276444577492963073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811372184296384995308715 4217058276444577492963073)
        ·
          refine ⟨3162793707333433119722305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4217058276444577492963073 3162793707333433119722305)
          ·
            refine ⟨2372095280500074839791729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3162793707333433119722305 2372095280500074839791729)
            ·
              refine ⟨1779071460375056129843797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2372095280500074839791729 1779071460375056129843797)
              ·
                refine ⟨20848493676270189021607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1779071460375056129843797 20848493676270189021607)
                ·
                  rfl

theorem cell23_1096262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_1096262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096262 prefixEnd_1096262 := by exact prefixLift 1096262
  have htrace : WordTrace (prefixWord ++ tailWord_1096262) baseStart_1096262 baseEnd_1096262 := by
    simpa [prefixWord, tailWord_1096262, baseEnd_1096262] using wordTrace_append hprefix tailTrace_1096262
  have hstable : (prefixWord ++ tailWord_1096262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096262).length < 2 ^ (prefixWord ++ tailWord_1096262).sum := by decide
  have hdescent : baseEnd_1096262 < baseStart_1096262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096286 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1096286 : Nat := 118140960795 + 1096286 * 2 ^ 59
def prefixEnd_1096286 : Nat := 4983230072969 + 3 ^ 40 * 1096286 * 2
def baseEnd_1096286 : Nat := 562921652795003009683279

theorem tailTrace_1096286 : CollatzResearch.WordTrace tailWord_1096286 prefixEnd_1096286 562921652795003009683279 := by
  unfold tailWord_1096286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998104413293815948463589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26656556870900351725139141 4998104413293815948463589)
  ·
    refine ⟨937144577492590490336923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4998104413293815948463589 937144577492590490336923)
    ·
      refine ⟨1405716866238885735505385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 937144577492590490336923 1405716866238885735505385)
      ·
        refine ⟨1054287649679164301629039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1405716866238885735505385 1054287649679164301629039)
        ·
          refine ⟨1581431474518746452443559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054287649679164301629039 1581431474518746452443559)
          ·
            refine ⟨2372147211778119678665339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581431474518746452443559 2372147211778119678665339)
            ·
              refine ⟨3558220817667179517998009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372147211778119678665339 3558220817667179517998009)
              ·
                refine ⟨2668665613250384638498507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558220817667179517998009 2668665613250384638498507)
                ·
                  refine ⟨4002998419875576957747761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668665613250384638498507 4002998419875576957747761)
                  ·
                    refine ⟨3002248814906682718310821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002998419875576957747761 3002248814906682718310821)
                    ·
                      refine ⟨562921652795003009683279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3002248814906682718310821 562921652795003009683279)
                      ·
                        rfl

theorem cell23_1096286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1096286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096286 prefixEnd_1096286 := by exact prefixLift 1096286
  have htrace : WordTrace (prefixWord ++ tailWord_1096286) baseStart_1096286 baseEnd_1096286 := by
    simpa [prefixWord, tailWord_1096286, baseEnd_1096286] using wordTrace_append hprefix tailTrace_1096286
  have hstable : (prefixWord ++ tailWord_1096286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096286).length < 2 ^ (prefixWord ++ tailWord_1096286).sum := by decide
  have hdescent : baseEnd_1096286 < baseStart_1096286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096325 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_1096325 : Nat := 118140960795 + 1096325 * 2 ^ 59
def prefixEnd_1096325 : Nat := 4983230072969 + 3 ^ 40 * 1096325 * 2
def baseEnd_1096325 : Nat := 562941678540528357095599

theorem tailTrace_1096325 : CollatzResearch.WordTrace tailWord_1096325 prefixEnd_1096325 562941678540528357095599 := by
  unfold tailWord_1096325
  simp only [CollatzResearch.WordTrace]
  refine ⟨39986257753209237248378429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26657505168806158165585619 39986257753209237248378429)
  ·
    refine ⟨14994846657453463968141911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39986257753209237248378429 14994846657453463968141911)
    ·
      refine ⟨22492269986180195952212867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14994846657453463968141911 22492269986180195952212867)
      ·
        refine ⟨33738404979270293928319301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22492269986180195952212867 33738404979270293928319301)
        ·
          refine ⟨6325950933613180111559869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33738404979270293928319301 6325950933613180111559869)
          ·
            refine ⟨2372231600104942541834951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6325950933613180111559869 2372231600104942541834951)
            ·
              refine ⟨3558347400157413812752427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372231600104942541834951 3558347400157413812752427)
              ·
                refine ⟨5337521100236120719128641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558347400157413812752427 5337521100236120719128641)
                ·
                  refine ⟨4003140825177090539346481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5337521100236120719128641 4003140825177090539346481)
                  ·
                    refine ⟨3002355618882817904509861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4003140825177090539346481 3002355618882817904509861)
                    ·
                      refine ⟨562941678540528357095599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3002355618882817904509861 562941678540528357095599)
                      ·
                        rfl

theorem cell23_1096325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_1096325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096325 prefixEnd_1096325 := by exact prefixLift 1096325
  have htrace : WordTrace (prefixWord ++ tailWord_1096325) baseStart_1096325 baseEnd_1096325 := by
    simpa [prefixWord, tailWord_1096325, baseEnd_1096325] using wordTrace_append hprefix tailTrace_1096325
  have hstable : (prefixWord ++ tailWord_1096325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096325).length < 2 ^ (prefixWord ++ tailWord_1096325).sum := by decide
  have hdescent : baseEnd_1096325 < baseStart_1096325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096355 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 7, 2]
def baseStart_1096355 : Nat := 118140960795 + 1096355 * 2 ^ 59
def prefixEnd_1096355 : Nat := 4983230072969 + 3 ^ 40 * 1096355 * 2
def baseEnd_1096355 : Nat := 562957082960163239720461

theorem tailTrace_1096355 : CollatzResearch.WordTrace tailWord_1096355 prefixEnd_1096355 562957082960163239720461 := by
  unfold tailWord_1096355
  simp only [CollatzResearch.WordTrace]
  refine ⟨39987351943100552371970519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26658234628733701581313679 39987351943100552371970519)
  ·
    refine ⟨59981027914650828557955779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39987351943100552371970519 59981027914650828557955779)
    ·
      refine ⟨89971541871976242836933669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59981027914650828557955779 89971541871976242836933669)
      ·
        refine ⟨16869664100995545531925063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89971541871976242836933669 16869664100995545531925063)
        ·
          refine ⟨25304496151493318297887595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16869664100995545531925063 25304496151493318297887595)
          ·
            refine ⟨37956744227239977446831393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25304496151493318297887595 37956744227239977446831393)
            ·
              refine ⟨28467558170429983085123545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37956744227239977446831393 28467558170429983085123545)
              ·
                refine ⟨21350668627822487313842659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28467558170429983085123545 21350668627822487313842659)
                ·
                  refine ⟨32026002941733730970763989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21350668627822487313842659 32026002941733730970763989)
                  ·
                    refine ⟨750609443946884319627281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32026002941733730970763989 750609443946884319627281)
                    ·
                      refine ⟨562957082960163239720461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 750609443946884319627281 562957082960163239720461)
                      ·
                        rfl

theorem cell23_1096355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_1096355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096355 prefixEnd_1096355 := by exact prefixLift 1096355
  have htrace : WordTrace (prefixWord ++ tailWord_1096355) baseStart_1096355 baseEnd_1096355 := by
    simpa [prefixWord, tailWord_1096355, baseEnd_1096355] using wordTrace_append hprefix tailTrace_1096355
  have hstable : (prefixWord ++ tailWord_1096355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096355).length < 2 ^ (prefixWord ++ tailWord_1096355).sum := by decide
  have hdescent : baseEnd_1096355 < baseStart_1096355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096442 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 6]
def baseStart_1096442 : Nat := 118140960795 + 1096442 * 2 ^ 59
def prefixEnd_1096442 : Nat := 4983230072969 + 3 ^ 40 * 1096442 * 2
def baseEnd_1096442 : Nat := 62555750641900488814729

theorem tailTrace_1096442 : CollatzResearch.WordTrace tailWord_1096442 prefixEnd_1096442 62555750641900488814729 := by
  unfold tailWord_1096442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9997631273446341557596895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26660350062523577486925053 9997631273446341557596895)
  ·
    refine ⟨14996446910169512336395343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9997631273446341557596895 14996446910169512336395343)
    ·
      refine ⟨22494670365254268504593015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14996446910169512336395343 22494670365254268504593015)
      ·
        refine ⟨33742005547881402756889523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22494670365254268504593015 33742005547881402756889523)
        ·
          refine ⟨50613008321822104135334285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33742005547881402756889523 50613008321822104135334285)
          ·
            refine ⟨18979878120683289050750357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50613008321822104135334285 18979878120683289050750357)
            ·
              refine ⟨889681786907029174253923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18979878120683289050750357 889681786907029174253923)
              ·
                refine ⟨1334522680360543761380885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889681786907029174253923 1334522680360543761380885)
                ·
                  refine ⟨62555750641900488814729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1334522680360543761380885 62555750641900488814729)
                  ·
                    rfl

theorem cell23_1096442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_1096442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096442 prefixEnd_1096442 := by exact prefixLift 1096442
  have htrace : WordTrace (prefixWord ++ tailWord_1096442) baseStart_1096442 baseEnd_1096442 := by
    simpa [prefixWord, tailWord_1096442, baseEnd_1096442] using wordTrace_append hprefix tailTrace_1096442
  have hstable : (prefixWord ++ tailWord_1096442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096442).length < 2 ^ (prefixWord ++ tailWord_1096442).sum := by decide
  have hdescent : baseEnd_1096442 < baseStart_1096442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096475 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 4]
def baseStart_1096475 : Nat := 118140960795 + 1096475 * 2 ^ 59
def prefixEnd_1096475 : Nat := 4983230072969 + 3 ^ 40 * 1096475 * 2
def baseEnd_1096475 : Nat := 563018700638702770219909

theorem tailTrace_1096475 : CollatzResearch.WordTrace tailWord_1096475 prefixEnd_1096475 563018700638702770219909 := by
  unfold tailWord_1096475
  simp only [CollatzResearch.WordTrace]
  refine ⟨39991728702665812866338879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26661152468443875244225919 39991728702665812866338879)
  ·
    refine ⟨59987593053998719299508319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39991728702665812866338879 59987593053998719299508319)
    ·
      refine ⟨89981389580998078949262479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59987593053998719299508319 89981389580998078949262479)
      ·
        refine ⟨134972084371497118423893719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89981389580998078949262479 134972084371497118423893719)
        ·
          refine ⟨202458126557245677635840579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134972084371497118423893719 202458126557245677635840579)
          ·
            refine ⟨303687189835868516453760869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202458126557245677635840579 303687189835868516453760869)
            ·
              refine ⟨56941348094225346835080163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 303687189835868516453760869 56941348094225346835080163)
              ·
                refine ⟨85412022141338020252620245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56941348094225346835080163 85412022141338020252620245)
                ·
                  refine ⟨2001844268937609849670787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 85412022141338020252620245 2001844268937609849670787)
                  ·
                    refine ⟨3002766403406414774506181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2001844268937609849670787 3002766403406414774506181)
                    ·
                      refine ⟨563018700638702770219909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3002766403406414774506181 563018700638702770219909)
                      ·
                        rfl

theorem cell23_1096475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 4].length) (baseStart_1096475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096475 prefixEnd_1096475 := by exact prefixLift 1096475
  have htrace : WordTrace (prefixWord ++ tailWord_1096475) baseStart_1096475 baseEnd_1096475 := by
    simpa [prefixWord, tailWord_1096475, baseEnd_1096475] using wordTrace_append hprefix tailTrace_1096475
  have hstable : (prefixWord ++ tailWord_1096475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096475).length < 2 ^ (prefixWord ++ tailWord_1096475).sum := by decide
  have hdescent : baseEnd_1096475 < baseStart_1096475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096479 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 2, 3, 2]
def baseStart_1096479 : Nat := 118140960795 + 1096479 * 2 ^ 59
def prefixEnd_1096479 : Nat := 4983230072969 + 3 ^ 40 * 1096479 * 2
def baseEnd_1096479 : Nat := 563020754561320754569891

theorem tailTrace_1096479 : CollatzResearch.WordTrace tailWord_1096479 prefixEnd_1096479 563020754561320754569891 := by
  unfold tailWord_1096479
  simp only [CollatzResearch.WordTrace]
  refine ⟨39991874594651321549484491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26661249729767547699656327 39991874594651321549484491)
  ·
    refine ⟨59987811891976982324226737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39991874594651321549484491 59987811891976982324226737)
    ·
      refine ⟨44990858918982736743170053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59987811891976982324226737 44990858918982736743170053)
      ·
        refine ⟨8435786047309263139344385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44990858918982736743170053 8435786047309263139344385)
        ·
          refine ⟨6326839535481947354508289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8435786047309263139344385 6326839535481947354508289)
          ·
            refine ⟨4745129651611460515881217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6326839535481947354508289 4745129651611460515881217)
            ·
              refine ⟨3558847238708595386910913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4745129651611460515881217 3558847238708595386910913)
              ·
                refine ⟨2669135429031446540183185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558847238708595386910913 2669135429031446540183185)
                ·
                  refine ⟨2001851571773584905137389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669135429031446540183185 2001851571773584905137389)
                  ·
                    refine ⟨750694339415094339426521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001851571773584905137389 750694339415094339426521)
                    ·
                      refine ⟨563020754561320754569891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 750694339415094339426521 563020754561320754569891)
                      ·
                        rfl

theorem cell23_1096479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_1096479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096479 prefixEnd_1096479 := by exact prefixLift 1096479
  have htrace : WordTrace (prefixWord ++ tailWord_1096479) baseStart_1096479 baseEnd_1096479 := by
    simpa [prefixWord, tailWord_1096479, baseEnd_1096479] using wordTrace_append hprefix tailTrace_1096479
  have hstable : (prefixWord ++ tailWord_1096479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096479).length < 2 ^ (prefixWord ++ tailWord_1096479).sum := by decide
  have hdescent : baseEnd_1096479 < baseStart_1096479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096485 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_1096485 : Nat := 118140960795 + 1096485 * 2 ^ 59
def prefixEnd_1096485 : Nat := 4983230072969 + 3 ^ 40 * 1096485 * 2
def baseEnd_1096485 : Nat := 187674611815082577031621

theorem tailTrace_1096485 : CollatzResearch.WordTrace tailWord_1096485 prefixEnd_1096485 187674611815082577031621 := by
  unfold tailWord_1096485
  simp only [CollatzResearch.WordTrace]
  refine ⟨39992093432629584574202909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26661395621753056382801939 39992093432629584574202909)
  ·
    refine ⟨14997035037236094215326091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39992093432629584574202909 14997035037236094215326091)
    ·
      refine ⟨22495552555854141322989137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14997035037236094215326091 22495552555854141322989137)
      ·
        refine ⟨16871664416890605992241853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22495552555854141322989137 16871664416890605992241853)
        ·
          refine ⟨6326874156333977247090695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16871664416890605992241853 6326874156333977247090695)
          ·
            refine ⟨9490311234500965870636043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6326874156333977247090695 9490311234500965870636043)
            ·
              refine ⟨14235466851751448805954065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9490311234500965870636043 14235466851751448805954065)
              ·
                refine ⟨10676600138813586604465549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14235466851751448805954065 10676600138813586604465549)
                ·
                  refine ⟨4003725052055094976674581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10676600138813586604465549 4003725052055094976674581)
                  ·
                    refine ⟨187674611815082577031621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4003725052055094976674581 187674611815082577031621)
                    ·
                      rfl

theorem cell23_1096485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_1096485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096485 prefixEnd_1096485 := by exact prefixLift 1096485
  have htrace : WordTrace (prefixWord ++ tailWord_1096485) baseStart_1096485 baseEnd_1096485 := by
    simpa [prefixWord, tailWord_1096485, baseEnd_1096485] using wordTrace_append hprefix tailTrace_1096485
  have hstable : (prefixWord ++ tailWord_1096485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096485).length < 2 ^ (prefixWord ++ tailWord_1096485).sum := by decide
  have hdescent : baseEnd_1096485 < baseStart_1096485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096495 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 3]
def baseStart_1096495 : Nat := 118140960795 + 1096495 * 2 ^ 59
def prefixEnd_1096495 : Nat := 4983230072969 + 3 ^ 40 * 1096495 * 2
def baseEnd_1096495 : Nat := 563028970251792691969817

theorem tailTrace_1096495 : CollatzResearch.WordTrace tailWord_1096495 prefixEnd_1096495 563028970251792691969817 := by
  unfold tailWord_1096495
  simp only [CollatzResearch.WordTrace]
  refine ⟨39992458162593356282066939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26661638775062237521377959 39992458162593356282066939)
  ·
    refine ⟨59988687243890034423100409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39992458162593356282066939 59988687243890034423100409)
    ·
      refine ⟨44991515432917525817325307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59988687243890034423100409 44991515432917525817325307)
      ·
        refine ⟨67487273149376288725987961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44991515432917525817325307 67487273149376288725987961)
        ·
          refine ⟨50615454862032216544490971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67487273149376288725987961 50615454862032216544490971)
          ·
            refine ⟨75923182293048324816736457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50615454862032216544490971 75923182293048324816736457)
            ·
              refine ⟨56942386719786243612552343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75923182293048324816736457 56942386719786243612552343)
              ·
                refine ⟨85413580079679365418828515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56942386719786243612552343 85413580079679365418828515)
                ·
                  refine ⟨128120370119519048128242773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85413580079679365418828515 128120370119519048128242773)
                  ·
                    refine ⟨1501410587338113845252845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 128120370119519048128242773 1501410587338113845252845)
                    ·
                      refine ⟨563028970251792691969817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1501410587338113845252845 563028970251792691969817)
                      ·
                        rfl

theorem cell23_1096495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_1096495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096495 prefixEnd_1096495 := by exact prefixLift 1096495
  have htrace : WordTrace (prefixWord ++ tailWord_1096495) baseStart_1096495 baseEnd_1096495 := by
    simpa [prefixWord, tailWord_1096495, baseEnd_1096495] using wordTrace_append hprefix tailTrace_1096495
  have hstable : (prefixWord ++ tailWord_1096495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096495).length < 2 ^ (prefixWord ++ tailWord_1096495).sum := by decide
  have hdescent : baseEnd_1096495 < baseStart_1096495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096532 : List Nat := [2, 4, 1, 1, 4, 1, 10]
def baseStart_1096532 : Nat := 118140960795 + 1096532 * 2 ^ 59
def prefixEnd_1096532 : Nat := 4983230072969 + 3 ^ 40 * 1096532 * 2
def baseEnd_1096532 : Nat := 6951209494271716632187

theorem tailTrace_1096532 : CollatzResearch.WordTrace tailWord_1096532 prefixEnd_1096532 6951209494271716632187 := by
  unfold tailWord_1096532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19996903831729655800581925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26662538442306207734109233 19996903831729655800581925)
  ·
    refine ⟨3749419468449310462609111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19996903831729655800581925 3749419468449310462609111)
    ·
      refine ⟨5624129202673965693913667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749419468449310462609111 5624129202673965693913667)
      ·
        refine ⟨8436193804010948540870501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624129202673965693913667 8436193804010948540870501)
        ·
          refine ⟨1581786338252052851413219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8436193804010948540870501 1581786338252052851413219)
          ·
            refine ⟨2372679507378079277119829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581786338252052851413219 2372679507378079277119829)
            ·
              refine ⟨6951209494271716632187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2372679507378079277119829 6951209494271716632187)
              ·
                rfl

theorem cell23_1096532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 10].length) (baseStart_1096532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096532 prefixEnd_1096532 := by exact prefixLift 1096532
  have htrace : WordTrace (prefixWord ++ tailWord_1096532) baseStart_1096532 baseEnd_1096532 := by
    simpa [prefixWord, tailWord_1096532, baseEnd_1096532] using wordTrace_append hprefix tailTrace_1096532
  have hstable : (prefixWord ++ tailWord_1096532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096532).length < 2 ^ (prefixWord ++ tailWord_1096532).sum := by decide
  have hdescent : baseEnd_1096532 < baseStart_1096532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096545 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1096545 : Nat := 118140960795 + 1096545 * 2 ^ 59
def prefixEnd_1096545 : Nat := 4983230072969 + 3 ^ 40 * 1096545 * 2
def baseEnd_1096545 : Nat := 187684881428172498781529

theorem tailTrace_1096545 : CollatzResearch.WordTrace tailWord_1096545 prefixEnd_1096545 187684881428172498781529 := by
  unfold tailWord_1096545
  simp only [CollatzResearch.WordTrace]
  refine ⟨39994281812412214821387089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26662854541608143214258059 39994281812412214821387089)
  ·
    refine ⟨29995711359309161116040317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39994281812412214821387089 29995711359309161116040317)
    ·
      refine ⟨11248391759740935418515119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29995711359309161116040317 11248391759740935418515119)
      ·
        refine ⟨16872587639611403127772679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11248391759740935418515119 16872587639611403127772679)
        ·
          refine ⟨25308881459417104691659019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16872587639611403127772679 25308881459417104691659019)
          ·
            refine ⟨37963322189125657037488529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25308881459417104691659019 37963322189125657037488529)
            ·
              refine ⟨28472491641844242778116397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37963322189125657037488529 28472491641844242778116397)
              ·
                refine ⟨10677184365691591041793649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28472491641844242778116397 10677184365691591041793649)
                ·
                  refine ⟨8007888274268693281345237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10677184365691591041793649 8007888274268693281345237)
                  ·
                    refine ⟨187684881428172498781529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8007888274268693281345237 187684881428172498781529)
                    ·
                      rfl

theorem cell23_1096545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1096545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096545 prefixEnd_1096545 := by exact prefixLift 1096545
  have htrace : WordTrace (prefixWord ++ tailWord_1096545) baseStart_1096545 baseEnd_1096545 := by
    simpa [prefixWord, tailWord_1096545, baseEnd_1096545] using wordTrace_append hprefix tailTrace_1096545
  have hstable : (prefixWord ++ tailWord_1096545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096545).length < 2 ^ (prefixWord ++ tailWord_1096545).sum := by decide
  have hdescent : baseEnd_1096545 < baseStart_1096545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096559 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 3]
def baseStart_1096559 : Nat := 118140960795 + 1096559 * 2 ^ 59
def prefixEnd_1096559 : Nat := 4983230072969 + 3 ^ 40 * 1096559 * 2
def baseEnd_1096559 : Nat := 563061833013680441569523

theorem tailTrace_1096559 : CollatzResearch.WordTrace tailWord_1096559 prefixEnd_1096559 563061833013680441569523 := by
  unfold tailWord_1096559
  simp only [CollatzResearch.WordTrace]
  refine ⟨39994792434361495212396731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26663194956240996808264487 39994792434361495212396731)
  ·
    refine ⟨59992188651542242818595097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39994792434361495212396731 59992188651542242818595097)
    ·
      refine ⟨44994141488656682113946323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59992188651542242818595097 44994141488656682113946323)
      ·
        refine ⟨67491212232985023170919485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44994141488656682113946323 67491212232985023170919485)
        ·
          refine ⟨25309204587369383689094807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67491212232985023170919485 25309204587369383689094807)
          ·
            refine ⟨37963806881054075533642211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25309204587369383689094807 37963806881054075533642211)
            ·
              refine ⟨56945710321581113300463317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37963806881054075533642211 56945710321581113300463317)
              ·
                refine ⟨1334665085662057342979609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56945710321581113300463317 1334665085662057342979609)
                ·
                  refine ⟨1000998814246543007234707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1334665085662057342979609 1000998814246543007234707)
                  ·
                    refine ⟨1501498221369814510852061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1000998814246543007234707 1501498221369814510852061)
                    ·
                      refine ⟨563061833013680441569523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1501498221369814510852061 563061833013680441569523)
                      ·
                        rfl

theorem cell23_1096559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 3].length) (baseStart_1096559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096559 prefixEnd_1096559 := by exact prefixLift 1096559
  have htrace : WordTrace (prefixWord ++ tailWord_1096559) baseStart_1096559 baseEnd_1096559 := by
    simpa [prefixWord, tailWord_1096559, baseEnd_1096559] using wordTrace_append hprefix tailTrace_1096559
  have hstable : (prefixWord ++ tailWord_1096559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096559).length < 2 ^ (prefixWord ++ tailWord_1096559).sum := by decide
  have hdescent : baseEnd_1096559 < baseStart_1096559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096566 : List Nat := [5, 1, 1, 3, 1, 3, 2, 7]
def baseStart_1096566 : Nat := 118140960795 + 1096566 * 2 ^ 59
def prefixEnd_1096566 : Nat := 4983230072969 + 3 ^ 40 * 1096566 * 2
def baseEnd_1096566 : Nat := 20854275088083774599333

theorem tailTrace_1096566 : CollatzResearch.WordTrace tailWord_1096566 prefixEnd_1096566 20854275088083774599333 := by
  unfold tailWord_1096566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2499690484083508462993847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26663365163557423605267701 2499690484083508462993847)
  ·
    refine ⟨3749535726125262694490771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2499690484083508462993847 3749535726125262694490771)
    ·
      refine ⟨5624303589187894041736157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749535726125262694490771 5624303589187894041736157)
      ·
        refine ⟨2109113845945460265651059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5624303589187894041736157 2109113845945460265651059)
        ·
          refine ⟨3163670768918190398476589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109113845945460265651059 3163670768918190398476589)
          ·
            refine ⟨1186376538344321399428721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3163670768918190398476589 1186376538344321399428721)
            ·
              refine ⟨889782403758241049571541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186376538344321399428721 889782403758241049571541)
              ·
                refine ⟨20854275088083774599333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 889782403758241049571541 20854275088083774599333)
                ·
                  rfl

theorem cell23_1096566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_1096566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096566 prefixEnd_1096566 := by exact prefixLift 1096566
  have htrace : WordTrace (prefixWord ++ tailWord_1096566) baseStart_1096566 baseEnd_1096566 := by
    simpa [prefixWord, tailWord_1096566, baseEnd_1096566] using wordTrace_append hprefix tailTrace_1096566
  have hstable : (prefixWord ++ tailWord_1096566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096566).length < 2 ^ (prefixWord ++ tailWord_1096566).sum := by decide
  have hdescent : baseEnd_1096566 < baseStart_1096566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096575 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 1, 8]
def baseStart_1096575 : Nat := 118140960795 + 1096575 * 2 ^ 59
def prefixEnd_1096575 : Nat := 4983230072969 + 3 ^ 40 * 1096575 * 2
def baseEnd_1096575 : Nat := 187690016234717459656483

theorem tailTrace_1096575 : CollatzResearch.WordTrace tailWord_1096575 prefixEnd_1096575 187690016234717459656483 := by
  unfold tailWord_1096575
  simp only [CollatzResearch.WordTrace]
  refine ⟨39995376002303529944979179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26663584001535686629986119 39995376002303529944979179)
  ·
    refine ⟨59993064003455294917468769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39995376002303529944979179 59993064003455294917468769)
    ·
      refine ⟨44994798002591471188101577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59993064003455294917468769 44994798002591471188101577)
      ·
        refine ⟨33746098501943603391076183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44994798002591471188101577 33746098501943603391076183)
        ·
          refine ⟨50619147752915405086614275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33746098501943603391076183 50619147752915405086614275)
          ·
            refine ⟨75928721629373107629921413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50619147752915405086614275 75928721629373107629921413)
            ·
              refine ⟨14236635305507457680610265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75928721629373107629921413 14236635305507457680610265)
              ·
                refine ⟨10677476479130593260457699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14236635305507457680610265 10677476479130593260457699)
                ·
                  refine ⟨16016214718695889890686549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10677476479130593260457699 16016214718695889890686549)
                  ·
                    refine ⟨187690016234717459656483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16016214718695889890686549 187690016234717459656483)
                    ·
                      rfl

theorem cell23_1096575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_1096575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096575 prefixEnd_1096575 := by exact prefixLift 1096575
  have htrace : WordTrace (prefixWord ++ tailWord_1096575) baseStart_1096575 baseEnd_1096575 := by
    simpa [prefixWord, tailWord_1096575, baseEnd_1096575] using wordTrace_append hprefix tailTrace_1096575
  have hstable : (prefixWord ++ tailWord_1096575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096575).length < 2 ^ (prefixWord ++ tailWord_1096575).sum := by decide
  have hdescent : baseEnd_1096575 < baseStart_1096575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096595 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6]
def baseStart_1096595 : Nat := 118140960795 + 1096595 * 2 ^ 59
def prefixEnd_1096595 : Nat := 4983230072969 + 3 ^ 40 * 1096595 * 2
def baseEnd_1096595 : Nat := 563080318317242300719357

theorem tailTrace_1096595 : CollatzResearch.WordTrace tailWord_1096595 prefixEnd_1096595 563080318317242300719357 := by
  unfold tailWord_1096595
  simp only [CollatzResearch.WordTrace]
  refine ⟨39996105462231073360707239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26664070308154048907138159 39996105462231073360707239)
  ·
    refine ⟨59994158193346610041060859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39996105462231073360707239 59994158193346610041060859)
    ·
      refine ⟨89991237290019915061591289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59994158193346610041060859 89991237290019915061591289)
      ·
        refine ⟨67493427967514936296193467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89991237290019915061591289 67493427967514936296193467)
        ·
          refine ⟨101240141951272404444290201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67493427967514936296193467 101240141951272404444290201)
          ·
            refine ⟨75930106463454303333217651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101240141951272404444290201 75930106463454303333217651)
            ·
              refine ⟨113895159695181454999826477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75930106463454303333217651 113895159695181454999826477)
              ·
                refine ⟨42710684885693045624934929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113895159695181454999826477 42710684885693045624934929)
                ·
                  refine ⟨32033013664269784218701197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42710684885693045624934929 32033013664269784218701197)
                  ·
                    refine ⟨12012380124101169082012949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32033013664269784218701197 12012380124101169082012949)
                    ·
                      refine ⟨563080318317242300719357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12012380124101169082012949 563080318317242300719357)
                      ·
                        rfl

theorem cell23_1096595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_1096595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096595 prefixEnd_1096595 := by exact prefixLift 1096595
  have htrace : WordTrace (prefixWord ++ tailWord_1096595) baseStart_1096595 baseEnd_1096595 := by
    simpa [prefixWord, tailWord_1096595, baseEnd_1096595] using wordTrace_append hprefix tailTrace_1096595
  have hstable : (prefixWord ++ tailWord_1096595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096595).length < 2 ^ (prefixWord ++ tailWord_1096595).sum := by decide
  have hdescent : baseEnd_1096595 < baseStart_1096595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096610 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_1096610 : Nat := 118140960795 + 1096610 * 2 ^ 59
def prefixEnd_1096610 : Nat := 4983230072969 + 3 ^ 40 * 1096610 * 2
def baseEnd_1096610 : Nat := 563088020527059742031789

theorem tailTrace_1096610 : CollatzResearch.WordTrace tailWord_1096610 prefixEnd_1096610 563088020527059742031789 := by
  unfold tailWord_1096610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999163139294182730625821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26664435038117820615002189 9999163139294182730625821)
  ·
    refine ⟨3749686177235318523984683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9999163139294182730625821 3749686177235318523984683)
    ·
      refine ⟨5624529265852977785977025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749686177235318523984683 5624529265852977785977025)
      ·
        refine ⟨4218396949389733339482769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5624529265852977785977025 4218396949389733339482769)
        ·
          refine ⟨3163797712042300004612077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4218396949389733339482769 3163797712042300004612077)
          ·
            refine ⟨1186424142015862501729529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3163797712042300004612077 1186424142015862501729529)
            ·
              refine ⟨889818106511896876297147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186424142015862501729529 889818106511896876297147)
              ·
                refine ⟨1334727159767845314445721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889818106511896876297147 1334727159767845314445721)
                ·
                  refine ⟨1001045369825883985834291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1334727159767845314445721 1001045369825883985834291)
                  ·
                    refine ⟨1501568054738825978751437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001045369825883985834291 1501568054738825978751437)
                    ·
                      refine ⟨563088020527059742031789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1501568054738825978751437 563088020527059742031789)
                      ·
                        rfl

theorem cell23_1096610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_1096610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096610 prefixEnd_1096610 := by exact prefixLift 1096610
  have htrace : WordTrace (prefixWord ++ tailWord_1096610) baseStart_1096610 baseEnd_1096610 := by
    simpa [prefixWord, tailWord_1096610, baseEnd_1096610] using wordTrace_append hprefix tailTrace_1096610
  have hstable : (prefixWord ++ tailWord_1096610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096610).length < 2 ^ (prefixWord ++ tailWord_1096610).sum := by decide
  have hdescent : baseEnd_1096610 < baseStart_1096610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096612 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1096612 : Nat := 118140960795 + 1096612 * 2 ^ 59
def prefixEnd_1096612 : Nat := 4983230072969 + 3 ^ 40 * 1096612 * 2
def baseEnd_1096612 : Nat := 563089047488368734206779

theorem tailTrace_1096612 : CollatzResearch.WordTrace tailWord_1096612 prefixEnd_1096612 563089047488368734206779 := by
  unfold tailWord_1096612
  simp only [CollatzResearch.WordTrace]
  refine ⟨19998362751584742632038045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26664483668779656842717393 19998362751584742632038045)
  ·
    refine ⟨7499386031844278487014267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19998362751584742632038045 7499386031844278487014267)
    ·
      refine ⟨11249079047766417730521401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7499386031844278487014267 11249079047766417730521401)
      ·
        refine ⟨8436809285824813297891051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11249079047766417730521401 8436809285824813297891051)
        ·
          refine ⟨12655213928737219946836577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8436809285824813297891051 12655213928737219946836577)
          ·
            refine ⟨9491410446552914960127433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12655213928737219946836577 9491410446552914960127433)
            ·
              refine ⟨7118557834914686220095575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9491410446552914960127433 7118557834914686220095575)
              ·
                refine ⟨10677836752372029330143363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7118557834914686220095575 10677836752372029330143363)
                ·
                  refine ⟨16016755128558043995215045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10677836752372029330143363 16016755128558043995215045)
                  ·
                    refine ⟨3003141586604633249102821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16016755128558043995215045 3003141586604633249102821)
                    ·
                      refine ⟨563089047488368734206779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3003141586604633249102821 563089047488368734206779)
                      ·
                        rfl

theorem cell23_1096612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1096612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096612 prefixEnd_1096612 := by exact prefixLift 1096612
  have htrace : WordTrace (prefixWord ++ tailWord_1096612) baseStart_1096612 baseEnd_1096612 := by
    simpa [prefixWord, tailWord_1096612, baseEnd_1096612] using wordTrace_append hprefix tailTrace_1096612
  have hstable : (prefixWord ++ tailWord_1096612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096612).length < 2 ^ (prefixWord ++ tailWord_1096612).sum := by decide
  have hdescent : baseEnd_1096612 < baseStart_1096612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096689 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_1096689 : Nat := 118140960795 + 1096689 * 2 ^ 59
def prefixEnd_1096689 : Nat := 4983230072969 + 3 ^ 40 * 1096689 * 2
def baseEnd_1096689 : Nat := 563128585498764932943925

theorem tailTrace_1096689 : CollatzResearch.WordTrace tailWord_1096689 prefixEnd_1096689 563128585498764932943925 := by
  unfold tailWord_1096689
  simp only [CollatzResearch.WordTrace]
  refine ⟨39999533923890527414629121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26666355949260351609752747 39999533923890527414629121)
  ·
    refine ⟨29999650442917895560971841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39999533923890527414629121 29999650442917895560971841)
    ·
      refine ⟨22499737832188421670728881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29999650442917895560971841 22499737832188421670728881)
      ·
        refine ⟨16874803374141316253046661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22499737832188421670728881 16874803374141316253046661)
        ·
          refine ⟨3164025632651496797446249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16874803374141316253046661 3164025632651496797446249)
          ·
            refine ⟨2373019224488622598084687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3164025632651496797446249 2373019224488622598084687)
            ·
              refine ⟨3559528836732933897127031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373019224488622598084687 3559528836732933897127031)
              ·
                refine ⟨5339293255099400845690547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559528836732933897127031 5339293255099400845690547)
                ·
                  refine ⟨8008939882649101268535821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5339293255099400845690547 8008939882649101268535821)
                  ·
                    refine ⟨3003352455993412975700933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8008939882649101268535821 3003352455993412975700933)
                    ·
                      refine ⟨563128585498764932943925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3003352455993412975700933 563128585498764932943925)
                      ·
                        rfl

theorem cell23_1096689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_1096689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096689 prefixEnd_1096689 := by exact prefixLift 1096689
  have htrace : WordTrace (prefixWord ++ tailWord_1096689) baseStart_1096689 baseEnd_1096689 := by
    simpa [prefixWord, tailWord_1096689, baseEnd_1096689] using wordTrace_append hprefix tailTrace_1096689
  have hstable : (prefixWord ++ tailWord_1096689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096689).length < 2 ^ (prefixWord ++ tailWord_1096689).sum := by decide
  have hdescent : baseEnd_1096689 < baseStart_1096689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096709 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_1096709 : Nat := 118140960795 + 1096709 * 2 ^ 59
def prefixEnd_1096709 : Nat := 4983230072969 + 3 ^ 40 * 1096709 * 2
def baseEnd_1096709 : Nat := 563138855111854854693833

theorem tailTrace_1096709 : CollatzResearch.WordTrace tailWord_1096709 prefixEnd_1096709 563138855111854854693833 := by
  unfold tailWord_1096709
  simp only [CollatzResearch.WordTrace]
  refine ⟨40000263383818070830357181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26666842255878713886904787 40000263383818070830357181)
  ·
    refine ⟨15000098768931776561383943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40000263383818070830357181 15000098768931776561383943)
    ·
      refine ⟨22500148153397664842075915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15000098768931776561383943 22500148153397664842075915)
      ·
        refine ⟨33750222230096497263113873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22500148153397664842075915 33750222230096497263113873)
        ·
          refine ⟨25312666672572372947335405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33750222230096497263113873 25312666672572372947335405)
          ·
            refine ⟨9492250002214639855250777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25312666672572372947335405 9492250002214639855250777)
            ·
              refine ⟨7119187501660979891438083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9492250002214639855250777 7119187501660979891438083)
              ·
                refine ⟨10678781252491469837157125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7119187501660979891438083 10678781252491469837157125)
                ·
                  refine ⟨2002271484842150594466961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10678781252491469837157125 2002271484842150594466961)
                  ·
                    refine ⟨1501703613631612945850221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2002271484842150594466961 1501703613631612945850221)
                    ·
                      refine ⟨563138855111854854693833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1501703613631612945850221 563138855111854854693833)
                      ·
                        rfl

theorem cell23_1096709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_1096709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096709 prefixEnd_1096709 := by exact prefixLift 1096709
  have htrace : WordTrace (prefixWord ++ tailWord_1096709) baseStart_1096709 baseEnd_1096709 := by
    simpa [prefixWord, tailWord_1096709, baseEnd_1096709] using wordTrace_append hprefix tailTrace_1096709
  have hstable : (prefixWord ++ tailWord_1096709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096709).length < 2 ^ (prefixWord ++ tailWord_1096709).sum := by decide
  have hdescent : baseEnd_1096709 < baseStart_1096709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096716 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_1096716 : Nat := 118140960795 + 1096716 * 2 ^ 59
def prefixEnd_1096716 : Nat := 4983230072969 + 3 ^ 40 * 1096716 * 2
def baseEnd_1096716 : Nat := 187714149825478775768767

theorem tailTrace_1096716 : CollatzResearch.WordTrace tailWord_1096716 prefixEnd_1096716 187714149825478775768767 := by
  unfold tailWord_1096716
  simp only [CollatzResearch.WordTrace]
  refine ⟨20000259347396355512931001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26667012463195140683908001 20000259347396355512931001)
  ·
    refine ⟨15000194510547266634698251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20000259347396355512931001 15000194510547266634698251)
    ·
      refine ⟨22500291765820899952047377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15000194510547266634698251 22500291765820899952047377)
      ·
        refine ⟨16875218824365674964035533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22500291765820899952047377 16875218824365674964035533)
        ·
          refine ⟨6328207059137128111513325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16875218824365674964035533 6328207059137128111513325)
          ·
            refine ⟨2373077647176423041817497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6328207059137128111513325 2373077647176423041817497)
            ·
              refine ⟨1779808235382317281363123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373077647176423041817497 1779808235382317281363123)
              ·
                refine ⟨2669712353073475922044685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1779808235382317281363123 2669712353073475922044685)
                ·
                  refine ⟨1001142132402553470766757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2669712353073475922044685 1001142132402553470766757)
                  ·
                    refine ⟨187714149825478775768767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001142132402553470766757 187714149825478775768767)
                    ·
                      rfl

theorem cell23_1096716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_1096716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096716 prefixEnd_1096716 := by exact prefixLift 1096716
  have htrace : WordTrace (prefixWord ++ tailWord_1096716) baseStart_1096716 baseEnd_1096716 := by
    simpa [prefixWord, tailWord_1096716, baseEnd_1096716] using wordTrace_append hprefix tailTrace_1096716
  have hstable : (prefixWord ++ tailWord_1096716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096716).length < 2 ^ (prefixWord ++ tailWord_1096716).sum := by decide
  have hdescent : baseEnd_1096716 < baseStart_1096716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096773 : List Nat := [1, 3, 1, 1, 1, 3, 2, 6, 1, 1, 3]
def baseStart_1096773 : Nat := 118140960795 + 1096773 * 2 ^ 59
def prefixEnd_1096773 : Nat := 4983230072969 + 3 ^ 40 * 1096773 * 2
def baseEnd_1096773 : Nat := 563171717873742604293539

theorem tailTrace_1096773 : CollatzResearch.WordTrace tailWord_1096773 prefixEnd_1096773 563171717873742604293539 := by
  unfold tailWord_1096773
  simp only [CollatzResearch.WordTrace]
  refine ⟨40002597655586209760686973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26668398437057473173791315 40002597655586209760686973)
  ·
    refine ⟨15000974120844828660257615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40002597655586209760686973 15000974120844828660257615)
    ·
      refine ⟨22501461181267242990386423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15000974120844828660257615 22501461181267242990386423)
      ·
        refine ⟨33752191771900864485579635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22501461181267242990386423 33752191771900864485579635)
        ·
          refine ⟨50628287657851296728369453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33752191771900864485579635 50628287657851296728369453)
          ·
            refine ⟨18985607871694236273138545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50628287657851296728369453 18985607871694236273138545)
            ·
              refine ⟨14239205903770677204853909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18985607871694236273138545 14239205903770677204853909)
              ·
                refine ⟨667462776739250493977527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14239205903770677204853909 667462776739250493977527)
                ·
                  refine ⟨1001194165108875740966291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667462776739250493977527 1001194165108875740966291)
                  ·
                    refine ⟨1501791247663313611449437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001194165108875740966291 1501791247663313611449437)
                    ·
                      refine ⟨563171717873742604293539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1501791247663313611449437 563171717873742604293539)
                      ·
                        rfl

theorem cell23_1096773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_1096773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096773 prefixEnd_1096773 := by exact prefixLift 1096773
  have htrace : WordTrace (prefixWord ++ tailWord_1096773) baseStart_1096773 baseEnd_1096773 := by
    simpa [prefixWord, tailWord_1096773, baseEnd_1096773] using wordTrace_append hprefix tailTrace_1096773
  have hstable : (prefixWord ++ tailWord_1096773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096773).length < 2 ^ (prefixWord ++ tailWord_1096773).sum := by decide
  have hdescent : baseEnd_1096773 < baseStart_1096773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096789 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_1096789 : Nat := 118140960795 + 1096789 * 2 ^ 59
def prefixEnd_1096789 : Nat := 4983230072969 + 3 ^ 40 * 1096789 * 2
def baseEnd_1096789 : Nat := 187726644521404847231155

theorem tailTrace_1096789 : CollatzResearch.WordTrace tailWord_1096789 prefixEnd_1096789 187726644521404847231155 := by
  unfold tailWord_1096789
  simp only [CollatzResearch.WordTrace]
  refine ⟨40003181223528244493269421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26668787482352162995512947 40003181223528244493269421)
  ·
    refine ⟨15001192958823091684976033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40003181223528244493269421 15001192958823091684976033)
    ·
      refine ⟨11250894719117318763732025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15001192958823091684976033 11250894719117318763732025)
      ·
        refine ⟨8438171039337989072799019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11250894719117318763732025 8438171039337989072799019)
        ·
          refine ⟨12657256559006983609198529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8438171039337989072799019 12657256559006983609198529)
          ·
            refine ⟨9492942419255237706898897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12657256559006983609198529 9492942419255237706898897)
            ·
              refine ⟨7119706814441428280174173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9492942419255237706898897 7119706814441428280174173)
              ·
                refine ⟨2669890055415535605065315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7119706814441428280174173 2669890055415535605065315)
                ·
                  refine ⟨4004835083123303407597973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669890055415535605065315 4004835083123303407597973)
                  ·
                    refine ⟨187726644521404847231155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4004835083123303407597973 187726644521404847231155)
                    ·
                      rfl

theorem cell23_1096789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_1096789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096789 prefixEnd_1096789 := by exact prefixLift 1096789
  have htrace : WordTrace (prefixWord ++ tailWord_1096789) baseStart_1096789 baseEnd_1096789 := by
    simpa [prefixWord, tailWord_1096789, baseEnd_1096789] using wordTrace_append hprefix tailTrace_1096789
  have hstable : (prefixWord ++ tailWord_1096789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096789).length < 2 ^ (prefixWord ++ tailWord_1096789).sum := by decide
  have hdescent : baseEnd_1096789 < baseStart_1096789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096796 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1096796 : Nat := 118140960795 + 1096796 * 2 ^ 59
def prefixEnd_1096796 : Nat := 4983230072969 + 3 ^ 40 * 1096796 * 2
def baseEnd_1096796 : Nat := 563183527928796014305933

theorem tailTrace_1096796 : CollatzResearch.WordTrace tailWord_1096796 prefixEnd_1096796 563183527928796014305933 := by
  unfold tailWord_1096796
  simp only [CollatzResearch.WordTrace]
  refine ⟨20001718267251442344387121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26668957689668589792516161 20001718267251442344387121)
  ·
    refine ⟨15001288700438581758290341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20001718267251442344387121 15001288700438581758290341)
    ·
      refine ⟨2812741631332234079679439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15001288700438581758290341 2812741631332234079679439)
      ·
        refine ⟨4219112446998351119519159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812741631332234079679439 4219112446998351119519159)
        ·
          refine ⟨6328668670497526679278739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219112446998351119519159 6328668670497526679278739)
          ·
            refine ⟨9493003005746290018918109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328668670497526679278739 9493003005746290018918109)
            ·
              refine ⟨3559876127154858757094291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9493003005746290018918109 3559876127154858757094291)
              ·
                refine ⟨5339814190732288135641437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559876127154858757094291 5339814190732288135641437)
                ·
                  refine ⟨2002430321524608050865539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5339814190732288135641437 2002430321524608050865539)
                  ·
                    refine ⟨3003645482286912076298309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2002430321524608050865539 3003645482286912076298309)
                    ·
                      refine ⟨563183527928796014305933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3003645482286912076298309 563183527928796014305933)
                      ·
                        rfl

theorem cell23_1096796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1096796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096796 prefixEnd_1096796 := by exact prefixLift 1096796
  have htrace : WordTrace (prefixWord ++ tailWord_1096796) baseStart_1096796 baseEnd_1096796 := by
    simpa [prefixWord, tailWord_1096796, baseEnd_1096796] using wordTrace_append hprefix tailTrace_1096796
  have hstable : (prefixWord ++ tailWord_1096796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096796).length < 2 ^ (prefixWord ++ tailWord_1096796).sum := by decide
  have hdescent : baseEnd_1096796 < baseStart_1096796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096809 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_1096809 : Nat := 118140960795 + 1096809 * 2 ^ 59
def prefixEnd_1096809 : Nat := 4983230072969 + 3 ^ 40 * 1096809 * 2
def baseEnd_1096809 : Nat := 563190203177304463443373

theorem tailTrace_1096809 : CollatzResearch.WordTrace tailWord_1096809 prefixEnd_1096809 563190203177304463443373 := by
  unfold tailWord_1096809
  simp only [CollatzResearch.WordTrace]
  refine ⟨40003910683455787908997481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26669273788970525272664987 40003910683455787908997481)
  ·
    refine ⟨30002933012591840931748111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40003910683455787908997481 30002933012591840931748111)
    ·
      refine ⟨45004399518887761397622167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30002933012591840931748111 45004399518887761397622167)
      ·
        refine ⟨67506599278331642096433251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45004399518887761397622167 67506599278331642096433251)
        ·
          refine ⟨101259898917497463144649877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67506599278331642096433251 101259898917497463144649877)
          ·
            refine ⟨4746557761757693584905463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101259898917497463144649877 4746557761757693584905463)
            ·
              refine ⟨7119836642636540377358195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746557761757693584905463 7119836642636540377358195)
              ·
                refine ⟨10679754963954810566037293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7119836642636540377358195 10679754963954810566037293)
                ·
                  refine ⟨4004908111483053962263985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10679754963954810566037293 4004908111483053962263985)
                  ·
                    refine ⟨3003681083612290471697989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4004908111483053962263985 3003681083612290471697989)
                    ·
                      refine ⟨563190203177304463443373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3003681083612290471697989 563190203177304463443373)
                      ·
                        rfl

theorem cell23_1096809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_1096809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096809 prefixEnd_1096809 := by exact prefixLift 1096809
  have htrace : WordTrace (prefixWord ++ tailWord_1096809) baseStart_1096809 baseEnd_1096809 := by
    simpa [prefixWord, tailWord_1096809, baseEnd_1096809] using wordTrace_append hprefix tailTrace_1096809
  have hstable : (prefixWord ++ tailWord_1096809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096809).length < 2 ^ (prefixWord ++ tailWord_1096809).sum := by decide
  have hdescent : baseEnd_1096809 < baseStart_1096809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096836 : List Nat := [2, 3, 2, 1, 2, 4, 1, 8]
def baseStart_1096836 : Nat := 118140960795 + 1096836 * 2 ^ 59
def prefixEnd_1096836 : Nat := 4983230072969 + 3 ^ 40 * 1096836 * 2
def baseEnd_1096836 : Nat := 20859409894628735474287

theorem tailTrace_1096836 : CollatzResearch.WordTrace tailWord_1096836 prefixEnd_1096836 20859409894628735474287 := by
  unfold tailWord_1096836
  simp only [CollatzResearch.WordTrace]
  refine ⟨20002447727178985760115181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26669930302905314346820241 20002447727178985760115181)
  ·
    refine ⟨7500917897692119660043193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20002447727178985760115181 7500917897692119660043193)
    ·
      refine ⟨5625688423269089745032395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7500917897692119660043193 5625688423269089745032395)
      ·
        refine ⟨8438532634903634617548593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625688423269089745032395 8438532634903634617548593)
        ·
          refine ⟨6328899476177725963161445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8438532634903634617548593 6328899476177725963161445)
          ·
            refine ⟨1186668651783323618092771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6328899476177725963161445 1186668651783323618092771)
            ·
              refine ⟨1780002977674985427139157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186668651783323618092771 1780002977674985427139157)
              ·
                refine ⟨20859409894628735474287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1780002977674985427139157 20859409894628735474287)
                ·
                  rfl

theorem cell23_1096836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 8].length) (baseStart_1096836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096836 prefixEnd_1096836 := by exact prefixLift 1096836
  have htrace : WordTrace (prefixWord ++ tailWord_1096836) baseStart_1096836 baseEnd_1096836 := by
    simpa [prefixWord, tailWord_1096836, baseEnd_1096836] using wordTrace_append hprefix tailTrace_1096836
  have hstable : (prefixWord ++ tailWord_1096836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096836).length < 2 ^ (prefixWord ++ tailWord_1096836).sum := by decide
  have hdescent : baseEnd_1096836 < baseStart_1096836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096879 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 2, 6]
def baseStart_1096879 : Nat := 118140960795 + 1096879 * 2 ^ 59
def prefixEnd_1096879 : Nat := 4983230072969 + 3 ^ 40 * 1096879 * 2
def baseEnd_1096879 : Nat := 187742048941039729856017

theorem tailTrace_1096879 : CollatzResearch.WordTrace tailWord_1096879 prefixEnd_1096879 187742048941039729856017 := by
  unfold tailWord_1096879
  simp only [CollatzResearch.WordTrace]
  refine ⟨40006463793202189864045691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26670975862134793242697127 40006463793202189864045691)
  ·
    refine ⟨60009695689803284796068537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40006463793202189864045691 60009695689803284796068537)
    ·
      refine ⟨45007271767352463597051403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60009695689803284796068537 45007271767352463597051403)
      ·
        refine ⟨67510907651028695395577105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45007271767352463597051403 67510907651028695395577105)
        ·
          refine ⟨50633180738271521546682829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67510907651028695395577105 50633180738271521546682829)
          ·
            refine ⟨18987442776851820580006061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50633180738271521546682829 18987442776851820580006061)
            ·
              refine ⟨7120291041319432717502273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18987442776851820580006061 7120291041319432717502273)
              ·
                refine ⟨5340218280989574538126705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7120291041319432717502273 5340218280989574538126705)
                ·
                  refine ⟨4005163710742180903595029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340218280989574538126705 4005163710742180903595029)
                  ·
                    refine ⟨187742048941039729856017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4005163710742180903595029 187742048941039729856017)
                    ·
                      rfl

theorem cell23_1096879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_1096879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096879 prefixEnd_1096879 := by exact prefixLift 1096879
  have htrace : WordTrace (prefixWord ++ tailWord_1096879) baseStart_1096879 baseEnd_1096879 := by
    simpa [prefixWord, tailWord_1096879, baseEnd_1096879] using wordTrace_append hprefix tailTrace_1096879
  have hstable : (prefixWord ++ tailWord_1096879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096879).length < 2 ^ (prefixWord ++ tailWord_1096879).sum := by decide
  have hdescent : baseEnd_1096879 < baseStart_1096879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096899 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4]
def baseStart_1096899 : Nat := 118140960795 + 1096899 * 2 ^ 59
def prefixEnd_1096899 : Nat := 4983230072969 + 3 ^ 40 * 1096899 * 2
def baseEnd_1096899 : Nat := 563236416436209111317959

theorem tailTrace_1096899 : CollatzResearch.WordTrace tailWord_1096899 prefixEnd_1096899 563236416436209111317959 := by
  unfold tailWord_1096899
  simp only [CollatzResearch.WordTrace]
  refine ⟨40007193253129733279773751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26671462168753155519849167 40007193253129733279773751)
  ·
    refine ⟨60010789879694599919660627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40007193253129733279773751 60010789879694599919660627)
    ·
      refine ⟨90016184819541899879490941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60010789879694599919660627 90016184819541899879490941)
      ·
        refine ⟨33756069307328212454809103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90016184819541899879490941 33756069307328212454809103)
        ·
          refine ⟨50634103960992318682213655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33756069307328212454809103 50634103960992318682213655)
          ·
            refine ⟨75951155941488478023320483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50634103960992318682213655 75951155941488478023320483)
            ·
              refine ⟨113926733912232717034980725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75951155941488478023320483 113926733912232717034980725)
              ·
                refine ⟨10680631304271817222029443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113926733912232717034980725 10680631304271817222029443)
                ·
                  refine ⟨16020946956407725833044165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10680631304271817222029443 16020946956407725833044165)
                  ·
                    refine ⟨3003927554326448593695781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16020946956407725833044165 3003927554326448593695781)
                    ·
                      refine ⟨563236416436209111317959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3003927554326448593695781 563236416436209111317959)
                      ·
                        rfl

theorem cell23_1096899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_1096899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096899 prefixEnd_1096899 := by exact prefixLift 1096899
  have htrace : WordTrace (prefixWord ++ tailWord_1096899) baseStart_1096899 baseEnd_1096899 := by
    simpa [prefixWord, tailWord_1096899, baseEnd_1096899] using wordTrace_append hprefix tailTrace_1096899
  have hstable : (prefixWord ++ tailWord_1096899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096899).length < 2 ^ (prefixWord ++ tailWord_1096899).sum := by decide
  have hdescent : baseEnd_1096899 < baseStart_1096899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096943 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 7]
def baseStart_1096943 : Nat := 118140960795 + 1096943 * 2 ^ 59
def prefixEnd_1096943 : Nat := 4983230072969 + 3 ^ 40 * 1096943 * 2
def baseEnd_1096943 : Nat := 62584334398334104351973

theorem tailTrace_1096943 : CollatzResearch.WordTrace tailWord_1096943 prefixEnd_1096943 62584334398334104351973 := by
  unfold tailWord_1096943
  simp only [CollatzResearch.WordTrace]
  refine ⟨40008798064970328794375483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26672532043313552529583655 40008798064970328794375483)
  ·
    refine ⟨60013197097455493191563225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40008798064970328794375483 60013197097455493191563225)
    ·
      refine ⟨45009897823091619893672419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60013197097455493191563225 45009897823091619893672419)
      ·
        refine ⟨67514846734637429840508629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45009897823091619893672419 67514846734637429840508629)
        ·
          refine ⟨1582379220343064761886921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 67514846734637429840508629 1582379220343064761886921)
          ·
            refine ⟨1186784415257298571415191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1582379220343064761886921 1186784415257298571415191)
            ·
              refine ⟨1780176622885947857122787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186784415257298571415191 1780176622885947857122787)
              ·
                refine ⟨2670264934328921785684181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780176622885947857122787 2670264934328921785684181)
                ·
                  refine ⟨62584334398334104351973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2670264934328921785684181 62584334398334104351973)
                  ·
                    rfl

theorem cell23_1096943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 7].length) (baseStart_1096943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096943 prefixEnd_1096943 := by exact prefixLift 1096943
  have htrace : WordTrace (prefixWord ++ tailWord_1096943) baseStart_1096943 baseEnd_1096943 := by
    simpa [prefixWord, tailWord_1096943, baseEnd_1096943] using wordTrace_append hprefix tailTrace_1096943
  have hstable : (prefixWord ++ tailWord_1096943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096943).length < 2 ^ (prefixWord ++ tailWord_1096943).sum := by decide
  have hdescent : baseEnd_1096943 < baseStart_1096943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096948 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1096948 : Nat := 118140960795 + 1096948 * 2 ^ 59
def prefixEnd_1096948 : Nat := 4983230072969 + 3 ^ 40 * 1096948 * 2
def baseEnd_1096948 : Nat := 563261576988279419605235

theorem tailTrace_1096948 : CollatzResearch.WordTrace tailWord_1096948 prefixEnd_1096948 563261576988279419605235 := by
  unfold tailWord_1096948
  simp only [CollatzResearch.WordTrace]
  refine ⟨20004490214976107324153749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26672653619968143098871665 20004490214976107324153749)
  ·
    refine ⟨937710478827005030819707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20004490214976107324153749 937710478827005030819707)
    ·
      refine ⟨1406565718240507546229561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 937710478827005030819707 1406565718240507546229561)
      ·
        refine ⟨1054924288680380659672171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1406565718240507546229561 1054924288680380659672171)
        ·
          refine ⟨1582386433020570989508257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054924288680380659672171 1582386433020570989508257)
          ·
            refine ⟨1186789824765428242131193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1582386433020570989508257 1186789824765428242131193)
            ·
              refine ⟨890092368574071181598395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186789824765428242131193 890092368574071181598395)
              ·
                refine ⟨1335138552861106772397593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890092368574071181598395 1335138552861106772397593)
                ·
                  refine ⟨1001353914645830079298195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1335138552861106772397593 1001353914645830079298195)
                  ·
                    refine ⟨1502030871968745118947293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001353914645830079298195 1502030871968745118947293)
                    ·
                      refine ⟨563261576988279419605235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502030871968745118947293 563261576988279419605235)
                      ·
                        rfl

theorem cell23_1096948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1096948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096948 prefixEnd_1096948 := by exact prefixLift 1096948
  have htrace : WordTrace (prefixWord ++ tailWord_1096948) baseStart_1096948 baseEnd_1096948 := by
    simpa [prefixWord, tailWord_1096948, baseEnd_1096948] using wordTrace_append hprefix tailTrace_1096948
  have hstable : (prefixWord ++ tailWord_1096948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096948).length < 2 ^ (prefixWord ++ tailWord_1096948).sum := by decide
  have hdescent : baseEnd_1096948 < baseStart_1096948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096979 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9]
def baseStart_1096979 : Nat := 118140960795 + 1096979 * 2 ^ 59
def prefixEnd_1096979 : Nat := 4983230072969 + 3 ^ 40 * 1096979 * 2
def baseEnd_1096979 : Nat := 563277494888568798317591

theorem tailTrace_1096979 : CollatzResearch.WordTrace tailWord_1096979 prefixEnd_1096979 563277494888568798317591 := by
  unfold tailWord_1096979
  simp only [CollatzResearch.WordTrace]
  refine ⟨40010111092839906942685991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26673407395226604628457327 40010111092839906942685991)
  ·
    refine ⟨60015166639259860414028987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40010111092839906942685991 60015166639259860414028987)
    ·
      refine ⟨90022749958889790621043481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60015166639259860414028987 90022749958889790621043481)
      ·
        refine ⟨67517062469167342965782611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90022749958889790621043481 67517062469167342965782611)
        ·
          refine ⟨101275593703751014448673917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67517062469167342965782611 101275593703751014448673917)
          ·
            refine ⟨37978347638906630418252719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101275593703751014448673917 37978347638906630418252719)
            ·
              refine ⟨56967521458359945627379079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37978347638906630418252719 56967521458359945627379079)
              ·
                refine ⟨85451282187539918441068619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56967521458359945627379079 85451282187539918441068619)
                ·
                  refine ⟨128176923281309877661602929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85451282187539918441068619 128176923281309877661602929)
                  ·
                    refine ⟨96132692460982408246202197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128176923281309877661602929 96132692460982408246202197)
                    ·
                      refine ⟨563277494888568798317591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 96132692460982408246202197 563277494888568798317591)
                      ·
                        rfl

theorem cell23_1096979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_1096979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096979 prefixEnd_1096979 := by exact prefixLift 1096979
  have htrace : WordTrace (prefixWord ++ tailWord_1096979) baseStart_1096979 baseEnd_1096979 := by
    simpa [prefixWord, tailWord_1096979, baseEnd_1096979] using wordTrace_append hprefix tailTrace_1096979
  have hstable : (prefixWord ++ tailWord_1096979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096979).length < 2 ^ (prefixWord ++ tailWord_1096979).sum := by decide
  have hdescent : baseEnd_1096979 < baseStart_1096979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096993 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_1096993 : Nat := 118140960795 + 1096993 * 2 ^ 59
def prefixEnd_1096993 : Nat := 4983230072969 + 3 ^ 40 * 1096993 * 2
def baseEnd_1096993 : Nat := 563284683617731743542527

theorem tailTrace_1096993 : CollatzResearch.WordTrace tailWord_1096993 prefixEnd_1096993 563284683617731743542527 := by
  unfold tailWord_1096993
  simp only [CollatzResearch.WordTrace]
  refine ⟨40010621714789187333695633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26673747809859458222463755 40010621714789187333695633)
  ·
    refine ⟨30007966286091890500271725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40010621714789187333695633 30007966286091890500271725)
    ·
      refine ⟨11252987357284458937601897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30007966286091890500271725 11252987357284458937601897)
      ·
        refine ⟨8439740517963344203201423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11252987357284458937601897 8439740517963344203201423)
        ·
          refine ⟨12659610776945016304802135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8439740517963344203201423 12659610776945016304802135)
          ·
            refine ⟨18989416165417524457203203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12659610776945016304802135 18989416165417524457203203)
            ·
              refine ⟨28484124248126286685804805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18989416165417524457203203 28484124248126286685804805)
              ·
                refine ⟨5340773296523678753588401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28484124248126286685804805 5340773296523678753588401)
                ·
                  refine ⟨4005579972392759065191301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340773296523678753588401 4005579972392759065191301)
                  ·
                    refine ⟨751046244823642324723369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4005579972392759065191301 751046244823642324723369)
                    ·
                      refine ⟨563284683617731743542527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751046244823642324723369 563284683617731743542527)
                      ·
                        rfl

theorem cell23_1096993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_1096993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096993 prefixEnd_1096993 := by exact prefixLift 1096993
  have htrace : WordTrace (prefixWord ++ tailWord_1096993) baseStart_1096993 baseEnd_1096993 := by
    simpa [prefixWord, tailWord_1096993, baseEnd_1096993] using wordTrace_append hprefix tailTrace_1096993
  have hstable : (prefixWord ++ tailWord_1096993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096993).length < 2 ^ (prefixWord ++ tailWord_1096993).sum := by decide
  have hdescent : baseEnd_1096993 < baseStart_1096993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096994 : List Nat := [3, 3, 1, 1, 5, 1, 2, 2, 5]
def baseStart_1096994 : Nat := 118140960795 + 1096994 * 2 ^ 59
def prefixEnd_1096994 : Nat := 4983230072969 + 3 ^ 40 * 1096994 * 2
def baseEnd_1096994 : Nat := 62587244122042915514447

theorem tailTrace_1096994 : CollatzResearch.WordTrace tailWord_1096994 prefixEnd_1096994 62587244122042915514447 := by
  unfold tailWord_1096994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10002664546946391126120509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26673772125190376336321357 10002664546946391126120509)
  ·
    refine ⟨3750999205104896672295191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10002664546946391126120509 3750999205104896672295191)
    ·
      refine ⟨5626498807657345008442787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750999205104896672295191 5626498807657345008442787)
      ·
        refine ⟨8439748211486017512664181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5626498807657345008442787 8439748211486017512664181)
        ·
          refine ⟨791226394826814141812267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8439748211486017512664181 791226394826814141812267)
          ·
            refine ⟨1186839592240221212718401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791226394826814141812267 1186839592240221212718401)
            ·
              refine ⟨890129694180165909538801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186839592240221212718401 890129694180165909538801)
              ·
                refine ⟨667597270635124432154101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890129694180165909538801 667597270635124432154101)
                ·
                  refine ⟨62587244122042915514447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 667597270635124432154101 62587244122042915514447)
                  ·
                    rfl

theorem cell23_1096994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_1096994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096994 prefixEnd_1096994 := by exact prefixLift 1096994
  have htrace : WordTrace (prefixWord ++ tailWord_1096994) baseStart_1096994 baseEnd_1096994 := by
    simpa [prefixWord, tailWord_1096994, baseEnd_1096994] using wordTrace_append hprefix tailTrace_1096994
  have hstable : (prefixWord ++ tailWord_1096994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096994).length < 2 ^ (prefixWord ++ tailWord_1096994).sum := by decide
  have hdescent : baseEnd_1096994 < baseStart_1096994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1096996 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1096996 : Nat := 118140960795 + 1096996 * 2 ^ 59
def prefixEnd_1096996 : Nat := 4983230072969 + 3 ^ 40 * 1096996 * 2
def baseEnd_1096996 : Nat := 563286224059695231805013

theorem tailTrace_1096996 : CollatzResearch.WordTrace tailWord_1096996 prefixEnd_1096996 563286224059695231805013 := by
  unfold tailWord_1096996
  simp only [CollatzResearch.WordTrace]
  refine ⟨20005365566889159423027421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26673820755852212564036561 20005365566889159423027421)
  ·
    refine ⟨7502012087583434783635283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20005365566889159423027421 7502012087583434783635283)
    ·
      refine ⟨11253018131375152175452925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7502012087583434783635283 11253018131375152175452925)
      ·
        refine ⟨4219881799265682065794847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11253018131375152175452925 4219881799265682065794847)
        ·
          refine ⟨6329822698898523098692271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219881799265682065794847 6329822698898523098692271)
          ·
            refine ⟨9494734048347784648038407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6329822698898523098692271 9494734048347784648038407)
            ·
              refine ⟨14242101072521676972057611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9494734048347784648038407 14242101072521676972057611)
              ·
                refine ⟨21363151608782515458086417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14242101072521676972057611 21363151608782515458086417)
                ·
                  refine ⟨16022363706586886593564813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21363151608782515458086417 16022363706586886593564813)
                  ·
                    refine ⟨6008386389970082472586805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16022363706586886593564813 6008386389970082472586805)
                    ·
                      refine ⟨563286224059695231805013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6008386389970082472586805 563286224059695231805013)
                      ·
                        rfl

theorem cell23_1096996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1096996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1096996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1096996 prefixEnd_1096996 := by exact prefixLift 1096996
  have htrace : WordTrace (prefixWord ++ tailWord_1096996) baseStart_1096996 baseEnd_1096996 := by
    simpa [prefixWord, tailWord_1096996, baseEnd_1096996] using wordTrace_append hprefix tailTrace_1096996
  have hstable : (prefixWord ++ tailWord_1096996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1096996).length < 2 ^ (prefixWord ++ tailWord_1096996).sum := by decide
  have hdescent : baseEnd_1096996 < baseStart_1096996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1096996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097010 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_1097010 : Nat := 118140960795 + 1097010 * 2 ^ 59
def prefixEnd_1097010 : Nat := 4983230072969 + 3 ^ 40 * 1097010 * 2
def baseEnd_1097010 : Nat := 563293412788858177029949

theorem tailTrace_1097010 : CollatzResearch.WordTrace tailWord_1097010 prefixEnd_1097010 563293412788858177029949 := by
  unfold tailWord_1097010
  simp only [CollatzResearch.WordTrace]
  refine ⟨10002810438931899809266121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26674161170485066158042989 10002810438931899809266121)
  ·
    refine ⟨7502107829198924856949591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10002810438931899809266121 7502107829198924856949591)
    ·
      refine ⟨11253161743798387285424387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7502107829198924856949591 11253161743798387285424387)
      ·
        refine ⟨16879742615697580928136581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11253161743798387285424387 16879742615697580928136581)
        ·
          refine ⟨3164951740443296424025609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16879742615697580928136581 3164951740443296424025609)
          ·
            refine ⟨2373713805332472318019207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3164951740443296424025609 2373713805332472318019207)
            ·
              refine ⟨3560570707998708477028811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373713805332472318019207 3560570707998708477028811)
              ·
                refine ⟨5340856061998062715543217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560570707998708477028811 5340856061998062715543217)
                ·
                  refine ⟨4005642046498547036657413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340856061998062715543217 4005642046498547036657413)
                  ·
                    refine ⟨751057883718477569373265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4005642046498547036657413 751057883718477569373265)
                    ·
                      refine ⟨563293412788858177029949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751057883718477569373265 563293412788858177029949)
                      ·
                        rfl

theorem cell23_1097010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_1097010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097010 prefixEnd_1097010 := by exact prefixLift 1097010
  have htrace : WordTrace (prefixWord ++ tailWord_1097010) baseStart_1097010 baseEnd_1097010 := by
    simpa [prefixWord, tailWord_1097010, baseEnd_1097010] using wordTrace_append hprefix tailTrace_1097010
  have hstable : (prefixWord ++ tailWord_1097010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097010).length < 2 ^ (prefixWord ++ tailWord_1097010).sum := by decide
  have hdescent : baseEnd_1097010 < baseStart_1097010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097043 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 3]
def baseStart_1097043 : Nat := 118140960795 + 1097043 * 2 ^ 59
def prefixEnd_1097043 : Nat := 4983230072969 + 3 ^ 40 * 1097043 * 2
def baseEnd_1097043 : Nat := 563310357650456547917297

theorem tailTrace_1097043 : CollatzResearch.WordTrace tailWord_1097043 prefixEnd_1097043 563310357650456547917297 := by
  unfold tailWord_1097043
  simp only [CollatzResearch.WordTrace]
  refine ⟨40012445364608045873015783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26674963576405363915343855 40012445364608045873015783)
  ·
    refine ⟨60018668046912068809523675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40012445364608045873015783 60018668046912068809523675)
    ·
      refine ⟨90028002070368103214285513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60018668046912068809523675 90028002070368103214285513)
      ·
        refine ⟨67521001552776077410714135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90028002070368103214285513 67521001552776077410714135)
        ·
          refine ⟨101281502329164116116071203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67521001552776077410714135 101281502329164116116071203)
          ·
            refine ⟨151922253493746174174106805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101281502329164116116071203 151922253493746174174106805)
            ·
              refine ⟨14242711265038703828822513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151922253493746174174106805 14242711265038703828822513)
              ·
                refine ⟨10682033448779027871616885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14242711265038703828822513 10682033448779027871616885)
                ·
                  refine ⟨1001440635823033862964083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10682033448779027871616885 1001440635823033862964083)
                  ·
                    refine ⟨1502160953734550794446125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001440635823033862964083 1502160953734550794446125)
                    ·
                      refine ⟨563310357650456547917297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502160953734550794446125 563310357650456547917297)
                      ·
                        rfl

theorem cell23_1097043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 3].length) (baseStart_1097043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097043 prefixEnd_1097043 := by exact prefixLift 1097043
  have htrace : WordTrace (prefixWord ++ tailWord_1097043) baseStart_1097043 baseEnd_1097043 := by
    simpa [prefixWord, tailWord_1097043, baseEnd_1097043] using wordTrace_append hprefix tailTrace_1097043
  have hstable : (prefixWord ++ tailWord_1097043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097043).length < 2 ^ (prefixWord ++ tailWord_1097043).sum := by decide
  have hdescent : baseEnd_1097043 < baseStart_1097043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097060 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_1097060 : Nat := 118140960795 + 1097060 * 2 ^ 59
def prefixEnd_1097060 : Nat := 4983230072969 + 3 ^ 40 * 1097060 * 2
def baseEnd_1097060 : Nat := 563319086821582981404719

theorem tailTrace_1097060 : CollatzResearch.WordTrace tailWord_1097060 prefixEnd_1097060 563319086821582981404719 := by
  unfold tailWord_1097060
  simp only [CollatzResearch.WordTrace]
  refine ⟨20006532702773228888192317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26675376937030971850923089 20006532702773228888192317)
  ·
    refine ⟨7502449763539960833072119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20006532702773228888192317 7502449763539960833072119)
    ·
      refine ⟨11253674645309941249608179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7502449763539960833072119 11253674645309941249608179)
      ·
        refine ⟨16880511967964911874412269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11253674645309941249608179 16880511967964911874412269)
        ·
          refine ⟨6330191987986841952904601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16880511967964911874412269 6330191987986841952904601)
          ·
            refine ⟨4747643990990131464678451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6330191987986841952904601 4747643990990131464678451)
            ·
              refine ⟨7121465986485197197017677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747643990990131464678451 7121465986485197197017677)
              ·
                refine ⟨2670549744931948948881629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7121465986485197197017677 2670549744931948948881629)
                ·
                  refine ⟨1001456154349480855830611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2670549744931948948881629 1001456154349480855830611)
                  ·
                    refine ⟨1502184231524221283745917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001456154349480855830611 1502184231524221283745917)
                    ·
                      refine ⟨563319086821582981404719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502184231524221283745917 563319086821582981404719)
                      ·
                        rfl

theorem cell23_1097060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_1097060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097060 prefixEnd_1097060 := by exact prefixLift 1097060
  have htrace : WordTrace (prefixWord ++ tailWord_1097060) baseStart_1097060 baseEnd_1097060 := by
    simpa [prefixWord, tailWord_1097060, baseEnd_1097060] using wordTrace_append hprefix tailTrace_1097060
  have hstable : (prefixWord ++ tailWord_1097060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097060).length < 2 ^ (prefixWord ++ tailWord_1097060).sum := by decide
  have hdescent : baseEnd_1097060 < baseStart_1097060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097083 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 2, 6, 2]
def baseStart_1097083 : Nat := 118140960795 + 1097083 * 2 ^ 59
def prefixEnd_1097083 : Nat := 4983230072969 + 3 ^ 40 * 1097083 * 2
def baseEnd_1097083 : Nat := 563330896876636391417113

theorem tailTrace_1097083 : CollatzResearch.WordTrace tailWord_1097083 prefixEnd_1097083 563330896876636391417113 := by
  unfold tailWord_1097083
  simp only [CollatzResearch.WordTrace]
  refine ⟨40013904284463132704471903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26675936189642088469647935 40013904284463132704471903)
  ·
    refine ⟨60020856426694699056707855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40013904284463132704471903 60020856426694699056707855)
    ·
      refine ⟨90031284640042048585061783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60020856426694699056707855 90031284640042048585061783)
      ·
        refine ⟨135046926960063072877592675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90031284640042048585061783 135046926960063072877592675)
        ·
          refine ⟨202570390440094609316389013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135046926960063072877592675 202570390440094609316389013)
          ·
            refine ⟨9495487051879434811705735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 202570390440094609316389013 9495487051879434811705735)
            ·
              refine ⟨14243230577819152217558603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9495487051879434811705735 14243230577819152217558603)
              ·
                refine ⟨21364845866728728326337905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14243230577819152217558603 21364845866728728326337905)
                ·
                  refine ⟨16023634400046546244753429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21364845866728728326337905 16023634400046546244753429)
                  ·
                    refine ⟨751107862502181855222817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16023634400046546244753429 751107862502181855222817)
                    ·
                      refine ⟨563330896876636391417113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751107862502181855222817 563330896876636391417113)
                      ·
                        rfl

theorem cell23_1097083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6, 2].length) (baseStart_1097083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097083 prefixEnd_1097083 := by exact prefixLift 1097083
  have htrace : WordTrace (prefixWord ++ tailWord_1097083) baseStart_1097083 baseEnd_1097083 := by
    simpa [prefixWord, tailWord_1097083, baseEnd_1097083] using wordTrace_append hprefix tailTrace_1097083
  have hstable : (prefixWord ++ tailWord_1097083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097083).length < 2 ^ (prefixWord ++ tailWord_1097083).sum := by decide
  have hdescent : baseEnd_1097083 < baseStart_1097083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097093 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_1097093 : Nat := 118140960795 + 1097093 * 2 ^ 59
def prefixEnd_1097093 : Nat := 4983230072969 + 3 ^ 40 * 1097093 * 2
def baseEnd_1097093 : Nat := 187778677227727117430689

theorem tailTrace_1097093 : CollatzResearch.WordTrace tailWord_1097093 prefixEnd_1097093 187778677227727117430689 := by
  unfold tailWord_1097093
  simp only [CollatzResearch.WordTrace]
  refine ⟨40014269014426904412335933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26676179342951269608223955 40014269014426904412335933)
  ·
    refine ⟨15005350880410089154625975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40014269014426904412335933 15005350880410089154625975)
    ·
      refine ⟨22508026320615133731938963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15005350880410089154625975 22508026320615133731938963)
      ·
        refine ⟨33762039480922700597908445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22508026320615133731938963 33762039480922700597908445)
        ·
          refine ⟨12660764805346012724215667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33762039480922700597908445 12660764805346012724215667)
          ·
            refine ⟨18991147208019019086323501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12660764805346012724215667 18991147208019019086323501)
            ·
              refine ⟨7121680203007132157371313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18991147208019019086323501 7121680203007132157371313)
              ·
                refine ⟨5341260152255349118028485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7121680203007132157371313 5341260152255349118028485)
                ·
                  refine ⟨1001486278547877959630341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5341260152255349118028485 1001486278547877959630341)
                  ·
                    refine ⟨187778677227727117430689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001486278547877959630341 187778677227727117430689)
                    ·
                      rfl

theorem cell23_1097093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_1097093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097093 prefixEnd_1097093 := by exact prefixLift 1097093
  have htrace : WordTrace (prefixWord ++ tailWord_1097093) baseStart_1097093 baseEnd_1097093 := by
    simpa [prefixWord, tailWord_1097093, baseEnd_1097093] using wordTrace_append hprefix tailTrace_1097093
  have hstable : (prefixWord ++ tailWord_1097093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097093).length < 2 ^ (prefixWord ++ tailWord_1097093).sum := by decide
  have hdescent : baseEnd_1097093 < baseStart_1097093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097136 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 4, 7]
def baseStart_1097136 : Nat := 118140960795 + 1097136 * 2 ^ 59
def prefixEnd_1097136 : Nat := 4983230072969 + 3 ^ 40 * 1097136 * 2
def baseEnd_1097136 : Nat := 187786037117108228018123

theorem tailTrace_1097136 : CollatzResearch.WordTrace tailWord_1097136 prefixEnd_1097136 187786037117108228018123 := by
  unfold tailWord_1097136
  simp only [CollatzResearch.WordTrace]
  refine ⟨20007918676635561378075631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26677224902180748504100841 20007918676635561378075631)
  ·
    refine ⟨30011878014953342067113447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20007918676635561378075631 30011878014953342067113447)
    ·
      refine ⟨45017817022430013100670171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30011878014953342067113447 45017817022430013100670171)
      ·
        refine ⟨67526725533645019651005257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45017817022430013100670171 67526725533645019651005257)
        ·
          refine ⟨50645044150233764738253943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67526725533645019651005257 50645044150233764738253943)
          ·
            refine ⟨75967566225350647107380915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50645044150233764738253943 75967566225350647107380915)
            ·
              refine ⟨113951349338025970661071373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75967566225350647107380915 113951349338025970661071373)
              ·
                refine ⟨42731756001759738997901765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113951349338025970661071373 42731756001759738997901765)
                ·
                  refine ⟨8012204250329951062106581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42731756001759738997901765 8012204250329951062106581)
                  ·
                    refine ⟨187786037117108228018123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8012204250329951062106581 187786037117108228018123)
                    ·
                      rfl

theorem cell23_1097136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_1097136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097136 prefixEnd_1097136 := by exact prefixLift 1097136
  have htrace : WordTrace (prefixWord ++ tailWord_1097136) baseStart_1097136 baseEnd_1097136 := by
    simpa [prefixWord, tailWord_1097136, baseEnd_1097136] using wordTrace_append hprefix tailTrace_1097136
  have hstable : (prefixWord ++ tailWord_1097136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097136).length < 2 ^ (prefixWord ++ tailWord_1097136).sum := by decide
  have hdescent : baseEnd_1097136 < baseStart_1097136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097173 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1097173 : Nat := 118140960795 + 1097173 * 2 ^ 59
def prefixEnd_1097173 : Nat := 4983230072969 + 3 ^ 40 * 1097173 * 2
def baseEnd_1097173 : Nat := 563377110135541039291699

theorem tailTrace_1097173 : CollatzResearch.WordTrace tailWord_1097173 prefixEnd_1097173 563377110135541039291699 := by
  unfold tailWord_1097173
  simp only [CollatzResearch.WordTrace]
  refine ⟨40017186854137078075248173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26678124569424718716832115 40017186854137078075248173)
  ·
    refine ⟨15006445070301404278218065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40017186854137078075248173 15006445070301404278218065)
    ·
      refine ⟨11254833802726053208663549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15006445070301404278218065 11254833802726053208663549)
      ·
        refine ⟨4220562676022269953248831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11254833802726053208663549 4220562676022269953248831)
        ·
          refine ⟨6330844014033404929873247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220562676022269953248831 6330844014033404929873247)
          ·
            refine ⟨9496266021050107394809871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330844014033404929873247 9496266021050107394809871)
            ·
              refine ⟨14244399031575161092214807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9496266021050107394809871 14244399031575161092214807)
              ·
                refine ⟨21366598547362741638322211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14244399031575161092214807 21366598547362741638322211)
                ·
                  refine ⟨32049897821044112457483317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21366598547362741638322211 32049897821044112457483317)
                  ·
                    refine ⟨3004677920722885542889061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32049897821044112457483317 3004677920722885542889061)
                    ·
                      refine ⟨563377110135541039291699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3004677920722885542889061 563377110135541039291699)
                      ·
                        rfl

theorem cell23_1097173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1097173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097173 prefixEnd_1097173 := by exact prefixLift 1097173
  have htrace : WordTrace (prefixWord ++ tailWord_1097173) baseStart_1097173 baseEnd_1097173 := by
    simpa [prefixWord, tailWord_1097173, baseEnd_1097173] using wordTrace_append hprefix tailTrace_1097173
  have hstable : (prefixWord ++ tailWord_1097173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097173).length < 2 ^ (prefixWord ++ tailWord_1097173).sum := by decide
  have hdescent : baseEnd_1097173 < baseStart_1097173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097183 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 2, 6]
def baseStart_1097183 : Nat := 118140960795 + 1097183 * 2 ^ 59
def prefixEnd_1097183 : Nat := 4983230072969 + 3 ^ 40 * 1097183 * 2
def baseEnd_1097183 : Nat := 187794081647362000055551

theorem tailTrace_1097183 : CollatzResearch.WordTrace tailWord_1097183 prefixEnd_1097183 187794081647362000055551 := by
  unfold tailWord_1097183
  simp only [CollatzResearch.WordTrace]
  refine ⟨40017551584100849783112203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26678367722733899855408135 40017551584100849783112203)
  ·
    refine ⟨60026327376151274674668305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40017551584100849783112203 60026327376151274674668305)
    ·
      refine ⟨45019745532113456006001229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60026327376151274674668305 45019745532113456006001229)
      ·
        refine ⟨16882404574542546002250461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45019745532113456006001229 16882404574542546002250461)
        ·
          refine ⟨6330901715453454750843923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16882404574542546002250461 6330901715453454750843923)
          ·
            refine ⟨9496352573180182126265885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330901715453454750843923 9496352573180182126265885)
            ·
              refine ⟨3561132214942568297349707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9496352573180182126265885 3561132214942568297349707)
              ·
                refine ⟨5341698322413852446024561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561132214942568297349707 5341698322413852446024561)
                ·
                  refine ⟨4006273741810389334518421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5341698322413852446024561 4006273741810389334518421)
                  ·
                    refine ⟨187794081647362000055551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4006273741810389334518421 187794081647362000055551)
                    ·
                      rfl

theorem cell23_1097183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_1097183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097183 prefixEnd_1097183 := by exact prefixLift 1097183
  have htrace : WordTrace (prefixWord ++ tailWord_1097183) baseStart_1097183 baseEnd_1097183 := by
    simpa [prefixWord, tailWord_1097183, baseEnd_1097183] using wordTrace_append hprefix tailTrace_1097183
  have hstable : (prefixWord ++ tailWord_1097183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097183).length < 2 ^ (prefixWord ++ tailWord_1097183).sum := by decide
  have hdescent : baseEnd_1097183 < baseStart_1097183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097224 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_1097224 : Nat := 118140960795 + 1097224 * 2 ^ 59
def prefixEnd_1097224 : Nat := 4983230072969 + 3 ^ 40 * 1097224 * 2
def baseEnd_1097224 : Nat := 563403297648920339753965

theorem tailTrace_1097224 : CollatzResearch.WordTrace tailWord_1097224 prefixEnd_1097224 563403297648920339753965 := by
  unfold tailWord_1097224
  simp only [CollatzResearch.WordTrace]
  refine ⟨20009523488476156892677363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26679364651301542523569817 20009523488476156892677363)
  ·
    refine ⟨30014285232714235339016045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20009523488476156892677363 30014285232714235339016045)
    ·
      refine ⟨11255356962267838252131017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30014285232714235339016045 11255356962267838252131017)
      ·
        refine ⟨8441517721700878689098263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11255356962267838252131017 8441517721700878689098263)
        ·
          refine ⟨12662276582551318033647395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8441517721700878689098263 12662276582551318033647395)
          ·
            refine ⟨18993414873826977050471093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12662276582551318033647395 18993414873826977050471093)
            ·
              refine ⟨1780632644421279098481665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18993414873826977050471093 1780632644421279098481665)
              ·
                refine ⟨1335474483315959323861249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780632644421279098481665 1335474483315959323861249)
                ·
                  refine ⟨1001605862486969492895937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1335474483315959323861249 1001605862486969492895937)
                  ·
                    refine ⟨751204396865227119671953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1001605862486969492895937 751204396865227119671953)
                    ·
                      refine ⟨563403297648920339753965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751204396865227119671953 563403297648920339753965)
                      ·
                        rfl

theorem cell23_1097224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_1097224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097224 prefixEnd_1097224 := by exact prefixLift 1097224
  have htrace : WordTrace (prefixWord ++ tailWord_1097224) baseStart_1097224 baseEnd_1097224 := by
    simpa [prefixWord, tailWord_1097224, baseEnd_1097224] using wordTrace_append hprefix tailTrace_1097224
  have hstable : (prefixWord ++ tailWord_1097224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097224).length < 2 ^ (prefixWord ++ tailWord_1097224).sum := by decide
  have hdescent : baseEnd_1097224 < baseStart_1097224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097253 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1097253 : Nat := 118140960795 + 1097253 * 2 ^ 59
def prefixEnd_1097253 : Nat := 4983230072969 + 3 ^ 40 * 1097253 * 2
def baseEnd_1097253 : Nat := 563418188587900726291331

theorem tailTrace_1097253 : CollatzResearch.WordTrace tailWord_1097253 prefixEnd_1097253 563418188587900726291331 := by
  unfold tailWord_1097253
  simp only [CollatzResearch.WordTrace]
  refine ⟨40020104693847251738160413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26680069795898167825440275 40020104693847251738160413)
  ·
    refine ⟨15007539260192719401810155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40020104693847251738160413 15007539260192719401810155)
    ·
      refine ⟨22511308890289079102715233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15007539260192719401810155 22511308890289079102715233)
      ·
        refine ⟨16883481667716809327036425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22511308890289079102715233 16883481667716809327036425)
        ·
          refine ⟨12662611250787606995277319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16883481667716809327036425 12662611250787606995277319)
          ·
            refine ⟨18993916876181410492915979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12662611250787606995277319 18993916876181410492915979)
            ·
              refine ⟨28490875314272115739373969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18993916876181410492915979 28490875314272115739373969)
              ·
                refine ⟨21368156485704086804530477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28490875314272115739373969 21368156485704086804530477)
                ·
                  refine ⟨8013058682139032551698929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21368156485704086804530477 8013058682139032551698929)
                  ·
                    refine ⟨6009794011604274413774197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8013058682139032551698929 6009794011604274413774197)
                    ·
                      refine ⟨563418188587900726291331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6009794011604274413774197 563418188587900726291331)
                      ·
                        rfl

theorem cell23_1097253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1097253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097253 prefixEnd_1097253 := by exact prefixLift 1097253
  have htrace : WordTrace (prefixWord ++ tailWord_1097253) baseStart_1097253 baseEnd_1097253 := by
    simpa [prefixWord, tailWord_1097253, baseEnd_1097253] using wordTrace_append hprefix tailTrace_1097253
  have hstable : (prefixWord ++ tailWord_1097253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097253).length < 2 ^ (prefixWord ++ tailWord_1097253).sum := by decide
  have hdescent : baseEnd_1097253 < baseStart_1097253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097277 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_1097277 : Nat := 118140960795 + 1097277 * 2 ^ 59
def prefixEnd_1097277 : Nat := 4983230072969 + 3 ^ 40 * 1097277 * 2
def baseEnd_1097277 : Nat := 187810170707869544130407

theorem tailTrace_1097277 : CollatzResearch.WordTrace tailWord_1097277 prefixEnd_1097277 187810170707869544130407 := by
  unfold tailWord_1097277
  simp only [CollatzResearch.WordTrace]
  refine ⟨40020980045760303837034085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26680653363840202558022723 40020980045760303837034085)
  ·
    refine ⟨7503933758580056969443891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40020980045760303837034085 7503933758580056969443891)
    ·
      refine ⟨11255900637870085454165837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7503933758580056969443891 11255900637870085454165837)
      ·
        refine ⟨4220962739201282045312189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11255900637870085454165837 4220962739201282045312189)
        ·
          refine ⟨1582861027200480766992071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4220962739201282045312189 1582861027200480766992071)
          ·
            refine ⟨2374291540800721150488107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582861027200480766992071 2374291540800721150488107)
            ·
              refine ⟨3561437311201081725732161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374291540800721150488107 3561437311201081725732161)
              ·
                refine ⟨2671077983400811294299121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561437311201081725732161 2671077983400811294299121)
                ·
                  refine ⟨2003308487550608470724341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671077983400811294299121 2003308487550608470724341)
                  ·
                    refine ⟨187810170707869544130407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2003308487550608470724341 187810170707869544130407)
                    ·
                      rfl

theorem cell23_1097277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_1097277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097277 prefixEnd_1097277 := by exact prefixLift 1097277
  have htrace : WordTrace (prefixWord ++ tailWord_1097277) baseStart_1097277 baseEnd_1097277 := by
    simpa [prefixWord, tailWord_1097277, baseEnd_1097277] using wordTrace_append hprefix tailTrace_1097277
  have hstable : (prefixWord ++ tailWord_1097277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097277).length < 2 ^ (prefixWord ++ tailWord_1097277).sum := by decide
  have hdescent : baseEnd_1097277 < baseStart_1097277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097317 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1097317 : Nat := 118140960795 + 1097317 * 2 ^ 59
def prefixEnd_1097317 : Nat := 4983230072969 + 3 ^ 40 * 1097317 * 2
def baseEnd_1097317 : Nat := 563451051349788475891037

theorem tailTrace_1097317 : CollatzResearch.WordTrace tailWord_1097317 prefixEnd_1097317 563451051349788475891037 := by
  unfold tailWord_1097317
  simp only [CollatzResearch.WordTrace]
  refine ⟨40022438965615390668490205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26681625977076927112326803 40022438965615390668490205)
  ·
    refine ⟨15008414612105771500683827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40022438965615390668490205 15008414612105771500683827)
    ·
      refine ⟨22512621918158657251025741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15008414612105771500683827 22512621918158657251025741)
      ·
        refine ⟨8442233219309496469134653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22512621918158657251025741 8442233219309496469134653)
        ·
          refine ⟨3165837457241061175925495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8442233219309496469134653 3165837457241061175925495)
          ·
            refine ⟨4748756185861591763888243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3165837457241061175925495 4748756185861591763888243)
            ·
              refine ⟨7123134278792387645832365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4748756185861591763888243 7123134278792387645832365)
              ·
                refine ⟨2671175354547145367187137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7123134278792387645832365 2671175354547145367187137)
                ·
                  refine ⟨2003381515910359025390353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671175354547145367187137 2003381515910359025390353)
                  ·
                    refine ⟨1502536136932769269042765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2003381515910359025390353 1502536136932769269042765)
                    ·
                      refine ⟨563451051349788475891037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502536136932769269042765 563451051349788475891037)
                      ·
                        rfl

theorem cell23_1097317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1097317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097317 prefixEnd_1097317 := by exact prefixLift 1097317
  have htrace : WordTrace (prefixWord ++ tailWord_1097317) baseStart_1097317 baseEnd_1097317 := by
    simpa [prefixWord, tailWord_1097317, baseEnd_1097317] using wordTrace_append hprefix tailTrace_1097317
  have hstable : (prefixWord ++ tailWord_1097317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097317).length < 2 ^ (prefixWord ++ tailWord_1097317).sum := by decide
  have hdescent : baseEnd_1097317 < baseStart_1097317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097334 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1097334 : Nat := 118140960795 + 1097334 * 2 ^ 59
def prefixEnd_1097334 : Nat := 4983230072969 + 3 ^ 40 * 1097334 * 2
def baseEnd_1097334 : Nat := 563459780520914909378459

theorem tailTrace_1097334 : CollatzResearch.WordTrace tailWord_1097334 prefixEnd_1097334 563459780520914909378459 := by
  unfold tailWord_1097334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2501441187909612660741191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26682039337702535047906037 2501441187909612660741191)
  ·
    refine ⟨3752161781864418991111787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2501441187909612660741191 3752161781864418991111787)
    ·
      refine ⟨5628242672796628486667681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3752161781864418991111787 5628242672796628486667681)
      ·
        refine ⟨4221182004597471365000761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5628242672796628486667681 4221182004597471365000761)
        ·
          refine ⟨3165886503448103523750571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4221182004597471365000761 3165886503448103523750571)
          ·
            refine ⟨4748829755172155285625857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3165886503448103523750571 4748829755172155285625857)
            ·
              refine ⟨3561622316379116464219393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4748829755172155285625857 3561622316379116464219393)
              ·
                refine ⟨2671216737284337348164545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561622316379116464219393 2671216737284337348164545)
                ·
                  refine ⟨2003412552963253011123409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671216737284337348164545 2003412552963253011123409)
                  ·
                    refine ⟨1502559414722439758342557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2003412552963253011123409 1502559414722439758342557)
                    ·
                      refine ⟨563459780520914909378459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502559414722439758342557 563459780520914909378459)
                      ·
                        rfl

theorem cell23_1097334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1097334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097334 prefixEnd_1097334 := by exact prefixLift 1097334
  have htrace : WordTrace (prefixWord ++ tailWord_1097334) baseStart_1097334 baseEnd_1097334 := by
    simpa [prefixWord, tailWord_1097334, baseEnd_1097334] using wordTrace_append hprefix tailTrace_1097334
  have hstable : (prefixWord ++ tailWord_1097334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097334).length < 2 ^ (prefixWord ++ tailWord_1097334).sum := by decide
  have hdescent : baseEnd_1097334 < baseStart_1097334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097341 : List Nat := [1, 4, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_1097341 : Nat := 118140960795 + 1097341 * 2 ^ 59
def prefixEnd_1097341 : Nat := 4983230072969 + 3 ^ 40 * 1097341 * 2
def baseEnd_1097341 : Nat := 187821124961832127330309

theorem tailTrace_1097341 : CollatzResearch.WordTrace tailWord_1097341 prefixEnd_1097341 187821124961832127330309 := by
  unfold tailWord_1097341
  simp only [CollatzResearch.WordTrace]
  refine ⟨40023314317528442767363877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26682209545018961844909251 40023314317528442767363877)
  ·
    refine ⟨7504371434536583018880727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40023314317528442767363877 7504371434536583018880727)
    ·
      refine ⟨11256557151804874528321091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7504371434536583018880727 11256557151804874528321091)
      ·
        refine ⟨16884835727707311792481637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11256557151804874528321091 16884835727707311792481637)
        ·
          refine ⟨3165906698945120961090307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16884835727707311792481637 3165906698945120961090307)
          ·
            refine ⟨4748860048417681441635461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3165906698945120961090307 4748860048417681441635461)
            ·
              refine ⟨890411259078315270306649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4748860048417681441635461 890411259078315270306649)
              ·
                refine ⟨667808444308736452729987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890411259078315270306649 667808444308736452729987)
                ·
                  refine ⟨1001712666463104679094981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667808444308736452729987 1001712666463104679094981)
                  ·
                    refine ⟨187821124961832127330309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001712666463104679094981 187821124961832127330309)
                    ·
                      rfl

theorem cell23_1097341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_1097341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097341 prefixEnd_1097341 := by exact prefixLift 1097341
  have htrace : WordTrace (prefixWord ++ tailWord_1097341) baseStart_1097341 baseEnd_1097341 := by
    simpa [prefixWord, tailWord_1097341, baseEnd_1097341] using wordTrace_append hprefix tailTrace_1097341
  have hstable : (prefixWord ++ tailWord_1097341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097341).length < 2 ^ (prefixWord ++ tailWord_1097341).sum := by decide
  have hdescent : baseEnd_1097341 < baseStart_1097341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097347 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 3]
def baseStart_1097347 : Nat := 118140960795 + 1097347 * 2 ^ 59
def prefixEnd_1097347 : Nat := 4983230072969 + 3 ^ 40 * 1097347 * 2
def baseEnd_1097347 : Nat := 563466455769423358515899

theorem tailTrace_1097347 : CollatzResearch.WordTrace tailWord_1097347 prefixEnd_1097347 563466455769423358515899 := by
  unfold tailWord_1097347
  simp only [CollatzResearch.WordTrace]
  refine ⟨40023533155506705792082295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26682355437004470528054863 40023533155506705792082295)
  ·
    refine ⟨60035299733260058688123443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40023533155506705792082295 60035299733260058688123443)
    ·
      refine ⟨90052949599890088032185165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60035299733260058688123443 90052949599890088032185165)
      ·
        refine ⟨33769856099958783012069437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90052949599890088032185165 33769856099958783012069437)
        ·
          refine ⟨12663696037484543629526039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33769856099958783012069437 12663696037484543629526039)
          ·
            refine ⟨18995544056226815444289059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12663696037484543629526039 18995544056226815444289059)
            ·
              refine ⟨28493316084340223166433589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18995544056226815444289059 28493316084340223166433589)
              ·
                refine ⟨2671248382906895921853149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28493316084340223166433589 2671248382906895921853149)
                ·
                  refine ⟨1001718143590085970694931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2671248382906895921853149 1001718143590085970694931)
                  ·
                    refine ⟨1502577215385128956042397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001718143590085970694931 1502577215385128956042397)
                    ·
                      refine ⟨563466455769423358515899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502577215385128956042397 563466455769423358515899)
                      ·
                        rfl

theorem cell23_1097347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_1097347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097347 prefixEnd_1097347 := by exact prefixLift 1097347
  have htrace : WordTrace (prefixWord ++ tailWord_1097347) baseStart_1097347 baseEnd_1097347 := by
    simpa [prefixWord, tailWord_1097347, baseEnd_1097347] using wordTrace_append hprefix tailTrace_1097347
  have hstable : (prefixWord ++ tailWord_1097347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097347).length < 2 ^ (prefixWord ++ tailWord_1097347).sum := by decide
  have hdescent : baseEnd_1097347 < baseStart_1097347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097398 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1097398 : Nat := 118140960795 + 1097398 * 2 ^ 59
def prefixEnd_1097398 : Nat := 4983230072969 + 3 ^ 40 * 1097398 * 2
def baseEnd_1097398 : Nat := 563492643282802658978165

theorem tailTrace_1097398 : CollatzResearch.WordTrace tailWord_1097398 prefixEnd_1097398 563492643282802658978165 := by
  unfold tailWord_1097398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2501587079895121343886803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26683595518881294334792565 2501587079895121343886803)
  ·
    refine ⟨3752380619842682015830205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2501587079895121343886803 3752380619842682015830205)
    ·
      refine ⟨1407142732441005755936327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3752380619842682015830205 1407142732441005755936327)
      ·
        refine ⟨2110714098661508633904491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407142732441005755936327 2110714098661508633904491)
        ·
          refine ⟨3166071147992262950856737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110714098661508633904491 3166071147992262950856737)
          ·
            refine ⟨2374553360994197213142553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166071147992262950856737 2374553360994197213142553)
            ·
              refine ⟨1780915020745647909856915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374553360994197213142553 1780915020745647909856915)
              ·
                refine ⟨2671372531118471864785373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780915020745647909856915 2671372531118471864785373)
                ·
                  refine ⟨1001764699169426949294515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2671372531118471864785373 1001764699169426949294515)
                  ·
                    refine ⟨1502647048754140423941773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001764699169426949294515 1502647048754140423941773)
                    ·
                      refine ⟨563492643282802658978165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502647048754140423941773 563492643282802658978165)
                      ·
                        rfl

theorem cell23_1097398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1097398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097398 prefixEnd_1097398 := by exact prefixLift 1097398
  have htrace : WordTrace (prefixWord ++ tailWord_1097398) baseStart_1097398 baseEnd_1097398 := by
    simpa [prefixWord, tailWord_1097398, baseEnd_1097398] using wordTrace_append hprefix tailTrace_1097398
  have hstable : (prefixWord ++ tailWord_1097398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097398).length < 2 ^ (prefixWord ++ tailWord_1097398).sum := by decide
  have hdescent : baseEnd_1097398 < baseStart_1097398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097400 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_1097400 : Nat := 118140960795 + 1097400 * 2 ^ 59
def prefixEnd_1097400 : Nat := 4983230072969 + 3 ^ 40 * 1097400 * 2
def baseEnd_1097400 : Nat := 563493670244111651153155

theorem tailTrace_1097400 : CollatzResearch.WordTrace tailWord_1097400 prefixEnd_1097400 563493670244111651153155 := by
  unfold tailWord_1097400
  simp only [CollatzResearch.WordTrace]
  refine ⟨20012733112157347921880827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26683644149543130562507769 20012733112157347921880827)
  ·
    refine ⟨30019099668236021882821241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20012733112157347921880827 30019099668236021882821241)
    ·
      refine ⟨22514324751177016412115931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30019099668236021882821241 22514324751177016412115931)
      ·
        refine ⟨33771487126765524618173897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22514324751177016412115931 33771487126765524618173897)
        ·
          refine ⟨25328615345074143463630423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33771487126765524618173897 25328615345074143463630423)
          ·
            refine ⟨37992923017611215195445635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25328615345074143463630423 37992923017611215195445635)
            ·
              refine ⟨56989384526416822793168453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37992923017611215195445635 56989384526416822793168453)
              ·
                refine ⟨10685509598703154273719085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56989384526416822793168453 10685509598703154273719085)
                ·
                  refine ⟨4007066099513682852644657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10685509598703154273719085 4007066099513682852644657)
                  ·
                    refine ⟨3005299574635262139483493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4007066099513682852644657 3005299574635262139483493)
                    ·
                      refine ⟨563493670244111651153155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3005299574635262139483493 563493670244111651153155)
                      ·
                        rfl

theorem cell23_1097400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_1097400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097400 prefixEnd_1097400 := by exact prefixLift 1097400
  have htrace : WordTrace (prefixWord ++ tailWord_1097400) baseStart_1097400 baseEnd_1097400 := by
    simpa [prefixWord, tailWord_1097400, baseEnd_1097400] using wordTrace_append hprefix tailTrace_1097400
  have hstable : (prefixWord ++ tailWord_1097400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097400).length < 2 ^ (prefixWord ++ tailWord_1097400).sum := by decide
  have hdescent : baseEnd_1097400 < baseStart_1097400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097421 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1097421 : Nat := 118140960795 + 1097421 * 2 ^ 59
def prefixEnd_1097421 : Nat := 4983230072969 + 3 ^ 40 * 1097421 * 2
def baseEnd_1097421 : Nat := 563504453337856068990559

theorem tailTrace_1097421 : CollatzResearch.WordTrace tailWord_1097421 prefixEnd_1097421 563504453337856068990559 := by
  unfold tailWord_1097421
  simp only [CollatzResearch.WordTrace]
  refine ⟨40026232157238616430276117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26684154771492410953517411 40026232157238616430276117)
  ·
    refine ⟨1876229632370560145169193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40026232157238616430276117 1876229632370560145169193)
    ·
      refine ⟨1407172224277920108876895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876229632370560145169193 1407172224277920108876895)
      ·
        refine ⟨2110758336416880163315343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407172224277920108876895 2110758336416880163315343)
        ·
          refine ⟨3166137504625320244973015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110758336416880163315343 3166137504625320244973015)
          ·
            refine ⟨4749206256937980367459523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166137504625320244973015 4749206256937980367459523)
            ·
              refine ⟨7123809385406970551189285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749206256937980367459523 7123809385406970551189285)
              ·
                refine ⟨1335714259763806978347991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7123809385406970551189285 1335714259763806978347991)
                ·
                  refine ⟨2003571389645710467521987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335714259763806978347991 2003571389645710467521987)
                  ·
                    refine ⟨3005357084468565701282981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2003571389645710467521987 3005357084468565701282981)
                    ·
                      refine ⟨563504453337856068990559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3005357084468565701282981 563504453337856068990559)
                      ·
                        rfl

theorem cell23_1097421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1097421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097421 prefixEnd_1097421 := by exact prefixLift 1097421
  have htrace : WordTrace (prefixWord ++ tailWord_1097421) baseStart_1097421 baseEnd_1097421 := by
    simpa [prefixWord, tailWord_1097421, baseEnd_1097421] using wordTrace_append hprefix tailTrace_1097421
  have hstable : (prefixWord ++ tailWord_1097421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097421).length < 2 ^ (prefixWord ++ tailWord_1097421).sum := by decide
  have hdescent : baseEnd_1097421 < baseStart_1097421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097454 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1097454 : Nat := 118140960795 + 1097454 * 2 ^ 59
def prefixEnd_1097454 : Nat := 4983230072969 + 3 ^ 40 * 1097454 * 2
def baseEnd_1097454 : Nat := 563521398199454439877907

theorem tailTrace_1097454 : CollatzResearch.WordTrace tailWord_1097454 prefixEnd_1097454 563521398199454439877907 := by
  unfold tailWord_1097454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003429470764882883278427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26684957177412708710818277 5003429470764882883278427)
  ·
    refine ⟨7505144206147324324917641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5003429470764882883278427 7505144206147324324917641)
    ·
      refine ⟨5628858154610493243688231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7505144206147324324917641 5628858154610493243688231)
      ·
        refine ⟨8443287231915739865532347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5628858154610493243688231 8443287231915739865532347)
        ·
          refine ⟨12664930847873609798298521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8443287231915739865532347 12664930847873609798298521)
          ·
            refine ⟨9498698135905207348723891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12664930847873609798298521 9498698135905207348723891)
            ·
              refine ⟨14248047203857811023085837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9498698135905207348723891 14248047203857811023085837)
              ·
                refine ⟨5343017701446679133657189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14248047203857811023085837 5343017701446679133657189)
                ·
                  refine ⟨1001815819021252337560723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5343017701446679133657189 1001815819021252337560723)
                  ·
                    refine ⟨1502723728531878506341085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001815819021252337560723 1502723728531878506341085)
                    ·
                      refine ⟨563521398199454439877907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502723728531878506341085 563521398199454439877907)
                      ·
                        rfl

theorem cell23_1097454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1097454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097454 prefixEnd_1097454 := by exact prefixLift 1097454
  have htrace : WordTrace (prefixWord ++ tailWord_1097454) baseStart_1097454 baseEnd_1097454 := by
    simpa [prefixWord, tailWord_1097454, baseEnd_1097454] using wordTrace_append hprefix tailTrace_1097454
  have hstable : (prefixWord ++ tailWord_1097454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097454).length < 2 ^ (prefixWord ++ tailWord_1097454).sum := by decide
  have hdescent : baseEnd_1097454 < baseStart_1097454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097471 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 2, 1, 3]
def baseStart_1097471 : Nat := 118140960795 + 1097471 * 2 ^ 59
def prefixEnd_1097471 : Nat := 4983230072969 + 3 ^ 40 * 1097471 * 2
def baseEnd_1097471 : Nat := 563530127370580873365329

theorem tailTrace_1097471 : CollatzResearch.WordTrace tailWord_1097471 prefixEnd_1097471 563530127370580873365329 := by
  unfold tailWord_1097471
  simp only [CollatzResearch.WordTrace]
  refine ⟨40028055807057474969596267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26685370538038316646397511 40028055807057474969596267)
  ·
    refine ⟨60042083710586212454394401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40028055807057474969596267 60042083710586212454394401)
    ·
      refine ⟨45031562782939659340795801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60042083710586212454394401 45031562782939659340795801)
      ·
        refine ⟨33773672087204744505596851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45031562782939659340795801 33773672087204744505596851)
        ·
          refine ⟨50660508130807116758395277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33773672087204744505596851 50660508130807116758395277)
          ·
            refine ⟨18997690549052668784398229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50660508130807116758395277 18997690549052668784398229)
            ·
              refine ⟨890516744486843849268667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18997690549052668784398229 890516744486843849268667)
              ·
                refine ⟨1335775116730265773903001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890516744486843849268667 1335775116730265773903001)
                ·
                  refine ⟨1001831337547699330427251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1335775116730265773903001 1001831337547699330427251)
                  ·
                    refine ⟨1502747006321548995640877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001831337547699330427251 1502747006321548995640877)
                    ·
                      refine ⟨563530127370580873365329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502747006321548995640877 563530127370580873365329)
                      ·
                        rfl

theorem cell23_1097471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_1097471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097471 prefixEnd_1097471 := by exact prefixLift 1097471
  have htrace : WordTrace (prefixWord ++ tailWord_1097471) baseStart_1097471 baseEnd_1097471 := by
    simpa [prefixWord, tailWord_1097471, baseEnd_1097471] using wordTrace_append hprefix tailTrace_1097471
  have hstable : (prefixWord ++ tailWord_1097471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097471).length < 2 ^ (prefixWord ++ tailWord_1097471).sum := by decide
  have hdescent : baseEnd_1097471 < baseStart_1097471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097485 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1097485 : Nat := 118140960795 + 1097485 * 2 ^ 59
def prefixEnd_1097485 : Nat := 4983230072969 + 3 ^ 40 * 1097485 * 2
def baseEnd_1097485 : Nat := 563537316099743818590265

theorem tailTrace_1097485 : CollatzResearch.WordTrace tailWord_1097485 prefixEnd_1097485 563537316099743818590265 := by
  unfold tailWord_1097485
  simp only [CollatzResearch.WordTrace]
  refine ⟨40028566429006755360605909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26685710952671170240403939 40028566429006755360605909)
  ·
    refine ⟨938169525679845828764201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 40028566429006755360605909 938169525679845828764201)
    ·
      refine ⟨703627144259884371573151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 938169525679845828764201 703627144259884371573151)
      ·
        refine ⟨1055440716389826557359727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703627144259884371573151 1055440716389826557359727)
        ·
          refine ⟨1583161074584739836039591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055440716389826557359727 1583161074584739836039591)
          ·
            refine ⟨2374741611877109754059387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583161074584739836039591 2374741611877109754059387)
            ·
              refine ⟨3562112417815664631089081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374741611877109754059387 3562112417815664631089081)
              ·
                refine ⟨2671584313361748473316811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3562112417815664631089081 2671584313361748473316811)
                ·
                  refine ⟨4007376470042622709975217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671584313361748473316811 4007376470042622709975217)
                  ·
                    refine ⟨3005532352531967032481413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4007376470042622709975217 3005532352531967032481413)
                    ·
                      refine ⟨563537316099743818590265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3005532352531967032481413 563537316099743818590265)
                      ·
                        rfl

theorem cell23_1097485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1097485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097485 prefixEnd_1097485 := by exact prefixLift 1097485
  have htrace : WordTrace (prefixWord ++ tailWord_1097485) baseStart_1097485 baseEnd_1097485 := by
    simpa [prefixWord, tailWord_1097485, baseEnd_1097485] using wordTrace_append hprefix tailTrace_1097485
  have hstable : (prefixWord ++ tailWord_1097485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097485).length < 2 ^ (prefixWord ++ tailWord_1097485).sum := by decide
  have hdescent : baseEnd_1097485 < baseStart_1097485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097492 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1097492 : Nat := 118140960795 + 1097492 * 2 ^ 59
def prefixEnd_1097492 : Nat := 4983230072969 + 3 ^ 40 * 1097492 * 2
def baseEnd_1097492 : Nat := 563540910464325291202733

theorem tailTrace_1097492 : CollatzResearch.WordTrace tailWord_1097492 prefixEnd_1097492 563540910464325291202733 := by
  unfold tailWord_1097492
  simp only [CollatzResearch.WordTrace]
  refine ⟨20014410869990697778055365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26685881159987597037407153 20014410869990697778055365)
  ·
    refine ⟨3752702038123255833385381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20014410869990697778055365 3752702038123255833385381)
    ·
      refine ⟨703631632148110468759759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3752702038123255833385381 703631632148110468759759)
      ·
        refine ⟨1055447448222165703139639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703631632148110468759759 1055447448222165703139639)
        ·
          refine ⟨1583171172333248554709459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055447448222165703139639 1583171172333248554709459)
          ·
            refine ⟨2374756758499872832064189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583171172333248554709459 2374756758499872832064189)
            ·
              refine ⟨890533784437452312024071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2374756758499872832064189 890533784437452312024071)
              ·
                refine ⟨1335800676656178468036107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890533784437452312024071 1335800676656178468036107)
                ·
                  refine ⟨2003701014984267702054161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335800676656178468036107 2003701014984267702054161)
                  ·
                    refine ⟨1502775761238200776540621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2003701014984267702054161 1502775761238200776540621)
                    ·
                      refine ⟨563540910464325291202733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502775761238200776540621 563540910464325291202733)
                      ·
                        rfl

theorem cell23_1097492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1097492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097492 prefixEnd_1097492 := by exact prefixLift 1097492
  have htrace : WordTrace (prefixWord ++ tailWord_1097492) baseStart_1097492 baseEnd_1097492 := by
    simpa [prefixWord, tailWord_1097492, baseEnd_1097492] using wordTrace_append hprefix tailTrace_1097492
  have hstable : (prefixWord ++ tailWord_1097492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097492).length < 2 ^ (prefixWord ++ tailWord_1097492).sum := by decide
  have hdescent : baseEnd_1097492 < baseStart_1097492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097498 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2]
def baseStart_1097498 : Nat := 118140960795 + 1097498 * 2 ^ 59
def prefixEnd_1097498 : Nat := 4983230072969 + 3 ^ 40 * 1097498 * 2
def baseEnd_1097498 : Nat := 563543991348252267727705

theorem tailTrace_1097498 : CollatzResearch.WordTrace tailWord_1097498 prefixEnd_1097498 563543991348252267727705 := by
  unfold tailWord_1097498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007260144489914645207287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26686027051973105720552765 10007260144489914645207287)
  ·
    refine ⟨15010890216734871967810931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10007260144489914645207287 15010890216734871967810931)
    ·
      refine ⟨22516335325102307951716397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15010890216734871967810931 22516335325102307951716397)
      ·
        refine ⟨8443625746913365481893649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22516335325102307951716397 8443625746913365481893649)
        ·
          refine ⟨6332719310185024111420237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8443625746913365481893649 6332719310185024111420237)
          ·
            refine ⟨2374769741319384041782589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6332719310185024111420237 2374769741319384041782589)
            ·
              refine ⟨890538652994769015668471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2374769741319384041782589 890538652994769015668471)
              ·
                refine ⟨1335807979492153523502707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890538652994769015668471 1335807979492153523502707)
                ·
                  refine ⟨2003711969238230285254061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335807979492153523502707 2003711969238230285254061)
                  ·
                    refine ⟨751391988464336356970273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2003711969238230285254061 751391988464336356970273)
                    ·
                      refine ⟨563543991348252267727705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751391988464336356970273 563543991348252267727705)
                      ·
                        rfl

theorem cell23_1097498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_1097498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097498 prefixEnd_1097498 := by exact prefixLift 1097498
  have htrace : WordTrace (prefixWord ++ tailWord_1097498) baseStart_1097498 baseEnd_1097498 := by
    simpa [prefixWord, tailWord_1097498, baseEnd_1097498] using wordTrace_append hprefix tailTrace_1097498
  have hstable : (prefixWord ++ tailWord_1097498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097498).length < 2 ^ (prefixWord ++ tailWord_1097498).sum := by decide
  have hdescent : baseEnd_1097498 < baseStart_1097498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097520 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_1097520 : Nat := 118140960795 + 1097520 * 2 ^ 59
def prefixEnd_1097520 : Nat := 4983230072969 + 3 ^ 40 * 1097520 * 2
def baseEnd_1097520 : Nat := 563555287922651181652603

theorem tailTrace_1097520 : CollatzResearch.WordTrace tailWord_1097520 prefixEnd_1097520 563555287922651181652603 := by
  unfold tailWord_1097520
  simp only [CollatzResearch.WordTrace]
  refine ⟨20014921491939978169065007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26686561989253304225420009 20014921491939978169065007)
  ·
    refine ⟨30022382237909967253597511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20014921491939978169065007 30022382237909967253597511)
    ·
      refine ⟨45033573356864950880396267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30022382237909967253597511 45033573356864950880396267)
      ·
        refine ⟨67550360035297426320594401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45033573356864950880396267 67550360035297426320594401)
        ·
          refine ⟨50662770026473069740445801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67550360035297426320594401 50662770026473069740445801)
          ·
            refine ⟨37997077519854802305334351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50662770026473069740445801 37997077519854802305334351)
            ·
              refine ⟨56995616279782203458001527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37997077519854802305334351 56995616279782203458001527)
              ·
                refine ⟨85493424419673305187002291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56995616279782203458001527 85493424419673305187002291)
                ·
                  refine ⟨128240136629509957780503437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85493424419673305187002291 128240136629509957780503437)
                  ·
                    refine ⟨48090051236066234167688789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128240136629509957780503437 48090051236066234167688789)
                    ·
                      refine ⟨563555287922651181652603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 48090051236066234167688789 563555287922651181652603)
                      ·
                        rfl

theorem cell23_1097520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_1097520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097520 prefixEnd_1097520 := by exact prefixLift 1097520
  have htrace : WordTrace (prefixWord ++ tailWord_1097520) baseStart_1097520 baseEnd_1097520 := by
    simpa [prefixWord, tailWord_1097520, baseEnd_1097520] using wordTrace_append hprefix tailTrace_1097520
  have hstable : (prefixWord ++ tailWord_1097520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097520).length < 2 ^ (prefixWord ++ tailWord_1097520).sum := by decide
  have hdescent : baseEnd_1097520 < baseStart_1097520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097524 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1097524 : Nat := 118140960795 + 1097524 * 2 ^ 59
def prefixEnd_1097524 : Nat := 4983230072969 + 3 ^ 40 * 1097524 * 2
def baseEnd_1097524 : Nat := 563557341845269166002585

theorem tailTrace_1097524 : CollatzResearch.WordTrace tailWord_1097524 prefixEnd_1097524 563557341845269166002585 := by
  unfold tailWord_1097524
  simp only [CollatzResearch.WordTrace]
  refine ⟨20014994437932732510637813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26686659250576976680850417 20014994437932732510637813)
  ·
    refine ⟨1876405728556193672872295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20014994437932732510637813 1876405728556193672872295)
    ·
      refine ⟨2814608592834290509308443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1876405728556193672872295 2814608592834290509308443)
      ·
        refine ⟨4221912889251435763962665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814608592834290509308443 4221912889251435763962665)
        ·
          refine ⟨3166434666938576822971999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4221912889251435763962665 3166434666938576822971999)
          ·
            refine ⟨4749652000407865234457999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166434666938576822971999 4749652000407865234457999)
            ·
              refine ⟨7124478000611797851686999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749652000407865234457999 7124478000611797851686999)
              ·
                refine ⟨10686717000917696777530499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7124478000611797851686999 10686717000917696777530499)
                ·
                  refine ⟨16030075501376545166295749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10686717000917696777530499 16030075501376545166295749)
                  ·
                    refine ⟨3005639156508102218680453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16030075501376545166295749 3005639156508102218680453)
                    ·
                      refine ⟨563557341845269166002585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3005639156508102218680453 563557341845269166002585)
                      ·
                        rfl

theorem cell23_1097524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1097524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097524 prefixEnd_1097524 := by exact prefixLift 1097524
  have htrace : WordTrace (prefixWord ++ tailWord_1097524) baseStart_1097524 baseEnd_1097524 := by
    simpa [prefixWord, tailWord_1097524, baseEnd_1097524] using wordTrace_append hprefix tailTrace_1097524
  have hstable : (prefixWord ++ tailWord_1097524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097524).length < 2 ^ (prefixWord ++ tailWord_1097524).sum := by decide
  have hdescent : baseEnd_1097524 < baseStart_1097524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097534 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_1097534 : Nat := 118140960795 + 1097534 * 2 ^ 59
def prefixEnd_1097534 : Nat := 4983230072969 + 3 ^ 40 * 1097534 * 2
def baseEnd_1097534 : Nat := 62618052961312680764171

theorem tailTrace_1097534 : CollatzResearch.WordTrace tailWord_1097534 prefixEnd_1097534 62618052961312680764171 := by
  unfold tailWord_1097534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003794200728654591142457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26686902403886157819426437 5003794200728654591142457)
  ·
    refine ⟨3752845650546490943356843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5003794200728654591142457 3752845650546490943356843)
    ·
      refine ⟨5629268475819736415035265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3752845650546490943356843 5629268475819736415035265)
      ·
        refine ⟨4221951356864802311276449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5629268475819736415035265 4221951356864802311276449)
        ·
          refine ⟨3166463517648601733457337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4221951356864802311276449 3166463517648601733457337)
          ·
            refine ⟨2374847638236451300093003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166463517648601733457337 2374847638236451300093003)
            ·
              refine ⟨3562271457354676950139505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374847638236451300093003 3562271457354676950139505)
              ·
                refine ⟨2671703593016007712604629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3562271457354676950139505 2671703593016007712604629)
                ·
                  refine ⟨62618052961312680764171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2671703593016007712604629 62618052961312680764171)
                  ·
                    rfl

theorem cell23_1097534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_1097534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097534 prefixEnd_1097534 := by exact prefixLift 1097534
  have htrace : WordTrace (prefixWord ++ tailWord_1097534) baseStart_1097534 baseEnd_1097534 := by
    simpa [prefixWord, tailWord_1097534, baseEnd_1097534] using wordTrace_append hprefix tailTrace_1097534
  have hstable : (prefixWord ++ tailWord_1097534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097534).length < 2 ^ (prefixWord ++ tailWord_1097534).sum := by decide
  have hdescent : baseEnd_1097534 < baseStart_1097534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097594 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_1097594 : Nat := 118140960795 + 1097594 * 2 ^ 59
def prefixEnd_1097594 : Nat := 4983230072969 + 3 ^ 40 * 1097594 * 2
def baseEnd_1097594 : Nat := 187864428497027964042421

theorem tailTrace_1097594 : CollatzResearch.WordTrace tailWord_1097594 prefixEnd_1097594 187864428497027964042421 := by
  unfold tailWord_1097594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10008135496402966744080959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26688361323741244650882557 10008135496402966744080959)
  ·
    refine ⟨15012203244604450116121439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10008135496402966744080959 15012203244604450116121439)
    ·
      refine ⟨22518304866906675174182159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15012203244604450116121439 22518304866906675174182159)
      ·
        refine ⟨33777457300360012761273239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22518304866906675174182159 33777457300360012761273239)
        ·
          refine ⟨50666185950540019141909859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33777457300360012761273239 50666185950540019141909859)
          ·
            refine ⟨75999278925810028712864789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50666185950540019141909859 75999278925810028712864789)
            ·
              refine ⟨3562466199647345095915537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75999278925810028712864789 3562466199647345095915537)
              ·
                refine ⟨2671849649735508821936653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3562466199647345095915537 2671849649735508821936653)
                ·
                  refine ⟨1001943618650815808226245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2671849649735508821936653 1001943618650815808226245)
                  ·
                    refine ⟨187864428497027964042421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001943618650815808226245 187864428497027964042421)
                    ·
                      rfl

theorem cell23_1097594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_1097594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097594 prefixEnd_1097594 := by exact prefixLift 1097594
  have htrace : WordTrace (prefixWord ++ tailWord_1097594) baseStart_1097594 baseEnd_1097594 := by
    simpa [prefixWord, tailWord_1097594, baseEnd_1097594] using wordTrace_append hprefix tailTrace_1097594
  have hstable : (prefixWord ++ tailWord_1097594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097594).length < 2 ^ (prefixWord ++ tailWord_1097594).sum := by decide
  have hdescent : baseEnd_1097594 < baseStart_1097594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097597 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1097597 : Nat := 118140960795 + 1097597 * 2 ^ 59
def prefixEnd_1097597 : Nat := 4983230072969 + 3 ^ 40 * 1097597 * 2
def baseEnd_1097597 : Nat := 563594825933047380389749

theorem tailTrace_1097597 : CollatzResearch.WordTrace tailWord_1097597 prefixEnd_1097597 563594825933047380389749 := by
  unfold tailWord_1097597
  simp only [CollatzResearch.WordTrace]
  refine ⟨40032651404600998488683045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26688434269733998992455363 40032651404600998488683045)
  ·
    refine ⟨7506122138362687216628071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40032651404600998488683045 7506122138362687216628071)
    ·
      refine ⟨11259183207544030824942107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7506122138362687216628071 11259183207544030824942107)
      ·
        refine ⟨16888774811316046237413161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11259183207544030824942107 16888774811316046237413161)
        ·
          refine ⟨12666581108487034678059871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16888774811316046237413161 12666581108487034678059871)
          ·
            refine ⟨18999871662730552017089807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12666581108487034678059871 18999871662730552017089807)
            ·
              refine ⟨28499807494095828025634711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18999871662730552017089807 28499807494095828025634711)
              ·
                refine ⟨42749711241143742038452067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28499807494095828025634711 42749711241143742038452067)
                ·
                  refine ⟨64124566861715613057678101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42749711241143742038452067 64124566861715613057678101)
                  ·
                    refine ⟨3005839071642919362078661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64124566861715613057678101 3005839071642919362078661)
                    ·
                      refine ⟨563594825933047380389749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3005839071642919362078661 563594825933047380389749)
                      ·
                        rfl

theorem cell23_1097597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1097597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097597 prefixEnd_1097597 := by exact prefixLift 1097597
  have htrace : WordTrace (prefixWord ++ tailWord_1097597) baseStart_1097597 baseEnd_1097597 := by
    simpa [prefixWord, tailWord_1097597, baseEnd_1097597] using wordTrace_append hprefix tailTrace_1097597
  have hstable : (prefixWord ++ tailWord_1097597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097597).length < 2 ^ (prefixWord ++ tailWord_1097597).sum := by decide
  have hdescent : baseEnd_1097597 < baseStart_1097597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097604 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1097604 : Nat := 118140960795 + 1097604 * 2 ^ 59
def prefixEnd_1097604 : Nat := 4983230072969 + 3 ^ 40 * 1097604 * 2
def baseEnd_1097604 : Nat := 563598420297628853002217

theorem tailTrace_1097604 : CollatzResearch.WordTrace tailWord_1097604 prefixEnd_1097604 563598420297628853002217 := by
  unfold tailWord_1097604
  simp only [CollatzResearch.WordTrace]
  refine ⟨20016453357787819342093933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26688604477050425789458577 20016453357787819342093933)
  ·
    refine ⟨7506170009170432253285225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20016453357787819342093933 7506170009170432253285225)
    ·
      refine ⟨5629627506877824189963919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7506170009170432253285225 5629627506877824189963919)
      ·
        refine ⟨8444441260316736284945879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5629627506877824189963919 8444441260316736284945879)
        ·
          refine ⟨12666661890475104427418819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8444441260316736284945879 12666661890475104427418819)
          ·
            refine ⟨18999992835712656641128229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12666661890475104427418819 18999992835712656641128229)
            ·
              refine ⟨3562498656696123120211543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18999992835712656641128229 3562498656696123120211543)
              ·
                refine ⟨5343747985044184680317315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562498656696123120211543 5343747985044184680317315)
                ·
                  refine ⟨8015621977566277020475973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5343747985044184680317315 8015621977566277020475973)
                  ·
                    refine ⟨1502929120793676941339245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8015621977566277020475973 1502929120793676941339245)
                    ·
                      refine ⟨563598420297628853002217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1502929120793676941339245 563598420297628853002217)
                      ·
                        rfl

theorem cell23_1097604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1097604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097604 prefixEnd_1097604 := by exact prefixLift 1097604
  have htrace : WordTrace (prefixWord ++ tailWord_1097604) baseStart_1097604 baseEnd_1097604 := by
    simpa [prefixWord, tailWord_1097604, baseEnd_1097604] using wordTrace_append hprefix tailTrace_1097604
  have hstable : (prefixWord ++ tailWord_1097604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097604).length < 2 ^ (prefixWord ++ tailWord_1097604).sum := by decide
  have hdescent : baseEnd_1097604 < baseStart_1097604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097628 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_1097628 : Nat := 118140960795 + 1097628 * 2 ^ 59
def prefixEnd_1097628 : Nat := 4983230072969 + 3 ^ 40 * 1097628 * 2
def baseEnd_1097628 : Nat := 187870247944445586367369

theorem tailTrace_1097628 : CollatzResearch.WordTrace tailWord_1097628 prefixEnd_1097628 187870247944445586367369 := by
  unfold tailWord_1097628
  simp only [CollatzResearch.WordTrace]
  refine ⟨20016891033744345391530769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26689188044992460522041025 20016891033744345391530769)
  ·
    refine ⟨15012668275308259043648077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20016891033744345391530769 15012668275308259043648077)
    ·
      refine ⟨5629750603240597141368029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15012668275308259043648077 5629750603240597141368029)
      ·
        refine ⟨2111156476215223928013011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5629750603240597141368029 2111156476215223928013011)
        ·
          refine ⟨3166734714322835892019517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111156476215223928013011 3166734714322835892019517)
          ·
            refine ⟨1187525517871063459507319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3166734714322835892019517 1187525517871063459507319)
            ·
              refine ⟨1781288276806595189260979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187525517871063459507319 1781288276806595189260979)
              ·
                refine ⟨2671932415209892783891469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781288276806595189260979 2671932415209892783891469)
                ·
                  refine ⟨1001974655703709793959301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2671932415209892783891469 1001974655703709793959301)
                  ·
                    refine ⟨187870247944445586367369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001974655703709793959301 187870247944445586367369)
                    ·
                      rfl

theorem cell23_1097628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_1097628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097628 prefixEnd_1097628 := by exact prefixLift 1097628
  have htrace : WordTrace (prefixWord ++ tailWord_1097628) baseStart_1097628 baseEnd_1097628 := by
    simpa [prefixWord, tailWord_1097628, baseEnd_1097628] using wordTrace_append hprefix tailTrace_1097628
  have hstable : (prefixWord ++ tailWord_1097628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097628).length < 2 ^ (prefixWord ++ tailWord_1097628).sum := by decide
  have hdescent : baseEnd_1097628 < baseStart_1097628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097684 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1097684 : Nat := 118140960795 + 1097684 * 2 ^ 59
def prefixEnd_1097684 : Nat := 4983230072969 + 3 ^ 40 * 1097684 * 2
def baseEnd_1097684 : Nat := 187879832916662846667283

theorem tailTrace_1097684 : CollatzResearch.WordTrace tailWord_1097684 prefixEnd_1097684 187879832916662846667283 := by
  unfold tailWord_1097684
  simp only [CollatzResearch.WordTrace]
  refine ⟨20017912277642906173550053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26690549703523874898066737 20017912277642906173550053)
  ·
    refine ⟨3753358552058044907540635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20017912277642906173550053 3753358552058044907540635)
    ·
      refine ⟨5630037828087067361310953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3753358552058044907540635 5630037828087067361310953)
      ·
        refine ⟨4222528371065300520983215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5630037828087067361310953 4222528371065300520983215)
        ·
          refine ⟨6333792556597950781474823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4222528371065300520983215 6333792556597950781474823)
          ·
            refine ⟨9500688834896926172212235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6333792556597950781474823 9500688834896926172212235)
            ·
              refine ⟨14251033252345389258318353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9500688834896926172212235 14251033252345389258318353)
              ·
                refine ⟨10688274939259041943738765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14251033252345389258318353 10688274939259041943738765)
                ·
                  refine ⟨4008103102222140728902037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10688274939259041943738765 4008103102222140728902037)
                  ·
                    refine ⟨187879832916662846667283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4008103102222140728902037 187879832916662846667283)
                    ·
                      rfl

theorem cell23_1097684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1097684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097684 prefixEnd_1097684 := by exact prefixLift 1097684
  have htrace : WordTrace (prefixWord ++ tailWord_1097684) baseStart_1097684 baseEnd_1097684 := by
    simpa [prefixWord, tailWord_1097684, baseEnd_1097684] using wordTrace_append hprefix tailTrace_1097684
  have hstable : (prefixWord ++ tailWord_1097684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097684).length < 2 ^ (prefixWord ++ tailWord_1097684).sum := by decide
  have hdescent : baseEnd_1097684 < baseStart_1097684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097685 : List Nat := [1, 3, 2, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_1097685 : Nat := 118140960795 + 1097685 * 2 ^ 59
def prefixEnd_1097685 : Nat := 4983230072969 + 3 ^ 40 * 1097685 * 2
def baseEnd_1097685 : Nat := 563640012230643036089345

theorem tailTrace_1097685 : CollatzResearch.WordTrace tailWord_1097685 prefixEnd_1097685 563640012230643036089345 := by
  unfold tailWord_1097685
  simp only [CollatzResearch.WordTrace]
  refine ⟨40035861028282189517886509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26690574018854793011924339 40035861028282189517886509)
  ·
    refine ⟨15013447885605821069207441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40035861028282189517886509 15013447885605821069207441)
    ·
      refine ⟨11260085914204365801905581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15013447885605821069207441 11260085914204365801905581)
      ·
        refine ⟨4222532217826637175714593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11260085914204365801905581 4222532217826637175714593)
        ·
          refine ⟨3166899163369977881785945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4222532217826637175714593 3166899163369977881785945)
          ·
            refine ⟨2375174372527483411339459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166899163369977881785945 2375174372527483411339459)
            ·
              refine ⟨3562761558791225117009189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2375174372527483411339459 3562761558791225117009189)
              ·
                refine ⟨668017792273354709439223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3562761558791225117009189 668017792273354709439223)
                ·
                  refine ⟨1002026688410032064158835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668017792273354709439223 1002026688410032064158835)
                  ·
                    refine ⟨1503040032615048096238253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1002026688410032064158835 1503040032615048096238253)
                    ·
                      refine ⟨563640012230643036089345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1503040032615048096238253 563640012230643036089345)
                      ·
                        rfl

theorem cell23_1097685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_1097685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097685 prefixEnd_1097685 := by exact prefixLift 1097685
  have htrace : WordTrace (prefixWord ++ tailWord_1097685) baseStart_1097685 baseEnd_1097685 := by
    simpa [prefixWord, tailWord_1097685, baseEnd_1097685] using wordTrace_append hprefix tailTrace_1097685
  have hstable : (prefixWord ++ tailWord_1097685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097685).length < 2 ^ (prefixWord ++ tailWord_1097685).sum := by decide
  have hdescent : baseEnd_1097685 < baseStart_1097685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097707 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7]
def baseStart_1097707 : Nat := 118140960795 + 1097707 * 2 ^ 59
def prefixEnd_1097707 : Nat := 4983230072969 + 3 ^ 40 * 1097707 * 2
def baseEnd_1097707 : Nat := 563651308805041950014243

theorem tailTrace_1097707 : CollatzResearch.WordTrace tailWord_1097707 prefixEnd_1097707 563651308805041950014243 := by
  unfold tailWord_1097707
  simp only [CollatzResearch.WordTrace]
  refine ⟨40036663434202487275187375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26691108956134991516791583 40036663434202487275187375)
  ·
    refine ⟨60054995151303730912781063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40036663434202487275187375 60054995151303730912781063)
    ·
      refine ⟨90082492726955596369171595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60054995151303730912781063 90082492726955596369171595)
      ·
        refine ⟨135123739090433394553757393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90082492726955596369171595 135123739090433394553757393)
        ·
          refine ⟨101342804317825045915318045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135123739090433394553757393 101342804317825045915318045)
          ·
            refine ⟨38003551619184392218244267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101342804317825045915318045 38003551619184392218244267)
            ·
              refine ⟨57005327428776588327366401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38003551619184392218244267 57005327428776588327366401)
              ·
                refine ⟨42753995571582441245524801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57005327428776588327366401 42753995571582441245524801)
                ·
                  refine ⟨32065496678686830934143601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42753995571582441245524801 32065496678686830934143601)
                  ·
                    refine ⟨24049122509015123200607701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32065496678686830934143601 24049122509015123200607701)
                    ·
                      refine ⟨563651308805041950014243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24049122509015123200607701 563651308805041950014243)
                      ·
                        rfl

theorem cell23_1097707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_1097707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097707 prefixEnd_1097707 := by exact prefixLift 1097707
  have htrace : WordTrace (prefixWord ++ tailWord_1097707) baseStart_1097707 baseEnd_1097707 := by
    simpa [prefixWord, tailWord_1097707, baseEnd_1097707] using wordTrace_append hprefix tailTrace_1097707
  have hstable : (prefixWord ++ tailWord_1097707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097707).length < 2 ^ (prefixWord ++ tailWord_1097707).sum := by decide
  have hdescent : baseEnd_1097707 < baseStart_1097707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097711 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 3]
def baseStart_1097711 : Nat := 118140960795 + 1097711 * 2 ^ 59
def prefixEnd_1097711 : Nat := 4983230072969 + 3 ^ 40 * 1097711 * 2
def baseEnd_1097711 : Nat := 563653362727659934364225

theorem tailTrace_1097711 : CollatzResearch.WordTrace tailWord_1097711 prefixEnd_1097711 563653362727659934364225 := by
  unfold tailWord_1097711
  simp only [CollatzResearch.WordTrace]
  refine ⟨40036809326187995958332987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26691206217458663972221991 40036809326187995958332987)
  ·
    refine ⟨60055213989281993937499481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40036809326187995958332987 60055213989281993937499481)
    ·
      refine ⟨45041410491961495453124611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60055213989281993937499481 45041410491961495453124611)
      ·
        refine ⟨67562115737942243179686917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45041410491961495453124611 67562115737942243179686917)
        ·
          refine ⟨12667896700864170596191297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67562115737942243179686917 12667896700864170596191297)
          ·
            refine ⟨9500922525648127947143473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12667896700864170596191297 9500922525648127947143473)
            ·
              refine ⟨7125691894236095960357605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9500922525648127947143473 7125691894236095960357605)
              ·
                refine ⟨1336067230169267992567051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7125691894236095960357605 1336067230169267992567051)
                ·
                  refine ⟨2004100845253901988850577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336067230169267992567051 2004100845253901988850577)
                  ·
                    refine ⟨1503075633940426491637933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2004100845253901988850577 1503075633940426491637933)
                    ·
                      refine ⟨563653362727659934364225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1503075633940426491637933 563653362727659934364225)
                      ·
                        rfl

theorem cell23_1097711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_1097711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097711 prefixEnd_1097711 := by exact prefixLift 1097711
  have htrace : WordTrace (prefixWord ++ tailWord_1097711) baseStart_1097711 baseEnd_1097711 := by
    simpa [prefixWord, tailWord_1097711, baseEnd_1097711] using wordTrace_append hprefix tailTrace_1097711
  have hstable : (prefixWord ++ tailWord_1097711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097711).length < 2 ^ (prefixWord ++ tailWord_1097711).sum := by decide
  have hdescent : baseEnd_1097711 < baseStart_1097711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097725 : List Nat := [1, 4, 1, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_1097725 : Nat := 118140960795 + 1097725 * 2 ^ 59
def prefixEnd_1097725 : Nat := 4983230072969 + 3 ^ 40 * 1097725 * 2
def baseEnd_1097725 : Nat := 563660551456822879589161

theorem tailTrace_1097725 : CollatzResearch.WordTrace tailWord_1097725 prefixEnd_1097725 563660551456822879589161 := by
  unfold tailWord_1097725
  simp only [CollatzResearch.WordTrace]
  refine ⟨40037319948137276349342629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26691546632091517566228419 40037319948137276349342629)
  ·
    refine ⟨7506997490275739315501743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40037319948137276349342629 7506997490275739315501743)
    ·
      refine ⟨11260496235413608973252615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7506997490275739315501743 11260496235413608973252615)
      ·
        refine ⟨16890744353120413459878923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11260496235413608973252615 16890744353120413459878923)
        ·
          refine ⟨25336116529680620189818385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16890744353120413459878923 25336116529680620189818385)
          ·
            refine ⟨19002087397260465142363789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25336116529680620189818385 19002087397260465142363789)
            ·
              refine ⟨7125782773972674428386421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19002087397260465142363789 7125782773972674428386421)
              ·
                refine ⟨668042135059938227661227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7125782773972674428386421 668042135059938227661227)
                ·
                  refine ⟨1002063202589907341491841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668042135059938227661227 1002063202589907341491841)
                  ·
                    refine ⟨751547401942430506118881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1002063202589907341491841 751547401942430506118881)
                    ·
                      refine ⟨563660551456822879589161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751547401942430506118881 563660551456822879589161)
                      ·
                        rfl

theorem cell23_1097725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_1097725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097725 prefixEnd_1097725 := by exact prefixLift 1097725
  have htrace : WordTrace (prefixWord ++ tailWord_1097725) baseStart_1097725 baseEnd_1097725 := by
    simpa [prefixWord, tailWord_1097725, baseEnd_1097725] using wordTrace_append hprefix tailTrace_1097725
  have hstable : (prefixWord ++ tailWord_1097725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097725).length < 2 ^ (prefixWord ++ tailWord_1097725).sum := by decide
  have hdescent : baseEnd_1097725 < baseStart_1097725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097798 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1097798 : Nat := 118140960795 + 1097798 * 2 ^ 59
def prefixEnd_1097798 : Nat := 4983230072969 + 3 ^ 40 * 1097798 * 2
def baseEnd_1097798 : Nat := 563698035544601093976325

theorem tailTrace_1097798 : CollatzResearch.WordTrace tailWord_1097798 prefixEnd_1097798 563698035544601093976325 := by
  unfold tailWord_1097798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251249452402275306773439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26693321651248539877833365 1251249452402275306773439)
  ·
    refine ⟨1876874178603412960160159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251249452402275306773439 1876874178603412960160159)
    ·
      refine ⟨2815311267905119440240239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1876874178603412960160159 2815311267905119440240239)
      ·
        refine ⟨4222966901857679160360359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815311267905119440240239 4222966901857679160360359)
        ·
          refine ⟨6334450352786518740540539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4222966901857679160360359 6334450352786518740540539)
          ·
            refine ⟨9501675529179778110810809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334450352786518740540539 9501675529179778110810809)
            ·
              refine ⟨7126256646884833583108107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9501675529179778110810809 7126256646884833583108107)
              ·
                refine ⟨10689384970327250374662161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126256646884833583108107 10689384970327250374662161)
                ·
                  refine ⟨8017038727745437780996621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10689384970327250374662161 8017038727745437780996621)
                  ·
                    refine ⟨3006389522904539167873733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8017038727745437780996621 3006389522904539167873733)
                    ·
                      refine ⟨563698035544601093976325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3006389522904539167873733 563698035544601093976325)
                      ·
                        rfl

theorem cell23_1097798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1097798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097798 prefixEnd_1097798 := by exact prefixLift 1097798
  have htrace : WordTrace (prefixWord ++ tailWord_1097798) baseStart_1097798 baseEnd_1097798 := by
    simpa [prefixWord, tailWord_1097798, baseEnd_1097798] using wordTrace_append hprefix tailTrace_1097798
  have hstable : (prefixWord ++ tailWord_1097798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097798).length < 2 ^ (prefixWord ++ tailWord_1097798).sum := by decide
  have hdescent : baseEnd_1097798 < baseStart_1097798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097838 : List Nat := [4, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_1097838 : Nat := 118140960795 + 1097838 * 2 ^ 59
def prefixEnd_1097838 : Nat := 4983230072969 + 3 ^ 40 * 1097838 * 2
def baseEnd_1097838 : Nat := 62635397196753437497349

theorem tailTrace_1097838 : CollatzResearch.WordTrace tailWord_1097838 prefixEnd_1097838 62635397196753437497349 := by
  unfold tailWord_1097838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5005180174590987081025771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26694294264485264432137445 5005180174590987081025771)
  ·
    refine ⟨7507770261886480621538657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5005180174590987081025771 7507770261886480621538657)
    ·
      refine ⟨5630827696414860466153993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7507770261886480621538657 5630827696414860466153993)
      ·
        refine ⟨4223120772311145349615495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5630827696414860466153993 4223120772311145349615495)
        ·
          refine ⟨6334681158466718024423243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4223120772311145349615495 6334681158466718024423243)
          ·
            refine ⟨9502021737700077036634865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334681158466718024423243 9502021737700077036634865)
            ·
              refine ⟨7126516303275057777476149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9502021737700077036634865 7126516303275057777476149)
              ·
                refine ⟨668110903432036666638389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7126516303275057777476149 668110903432036666638389)
                ·
                  refine ⟨62635397196753437497349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 668110903432036666638389 62635397196753437497349)
                  ·
                    rfl

theorem cell23_1097838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_1097838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097838 prefixEnd_1097838 := by exact prefixLift 1097838
  have htrace : WordTrace (prefixWord ++ tailWord_1097838) baseStart_1097838 baseEnd_1097838 := by
    simpa [prefixWord, tailWord_1097838, baseEnd_1097838] using wordTrace_append hprefix tailTrace_1097838
  have hstable : (prefixWord ++ tailWord_1097838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097838).length < 2 ^ (prefixWord ++ tailWord_1097838).sum := by decide
  have hdescent : baseEnd_1097838 < baseStart_1097838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097861 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_1097861 : Nat := 118140960795 + 1097861 * 2 ^ 59
def prefixEnd_1097861 : Nat := 4983230072969 + 3 ^ 40 * 1097861 * 2
def baseEnd_1097861 : Nat := 563730384825834347488535

theorem tailTrace_1097861 : CollatzResearch.WordTrace tailWord_1097861 prefixEnd_1097861 563730384825834347488535 := by
  unfold tailWord_1097861
  simp only [CollatzResearch.WordTrace]
  refine ⟨40042280275644571576293437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26694853517096381050862291 40042280275644571576293437)
  ·
    refine ⟨15015855103366714341110039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40042280275644571576293437 15015855103366714341110039)
    ·
      refine ⟨22523782655050071511665059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15015855103366714341110039 22523782655050071511665059)
      ·
        refine ⟨33785673982575107267497589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22523782655050071511665059 33785673982575107267497589)
        ·
          refine ⟨3167406935866416306327899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33785673982575107267497589 3167406935866416306327899)
          ·
            refine ⟨4751110403799624459491849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167406935866416306327899 4751110403799624459491849)
            ·
              refine ⟨3563332802849718344618887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4751110403799624459491849 3563332802849718344618887)
              ·
                refine ⟨5344999204274577516928331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563332802849718344618887 5344999204274577516928331)
                ·
                  refine ⟨8017498806411866275392497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344999204274577516928331 8017498806411866275392497)
                  ·
                    refine ⟨6013124104808899706544373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8017498806411866275392497 6013124104808899706544373)
                    ·
                      refine ⟨563730384825834347488535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6013124104808899706544373 563730384825834347488535)
                      ·
                        rfl

theorem cell23_1097861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_1097861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097861 prefixEnd_1097861 := by exact prefixLift 1097861
  have htrace : WordTrace (prefixWord ++ tailWord_1097861) baseStart_1097861 baseEnd_1097861 := by
    simpa [prefixWord, tailWord_1097861, baseEnd_1097861] using wordTrace_append hprefix tailTrace_1097861
  have hstable : (prefixWord ++ tailWord_1097861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097861).length < 2 ^ (prefixWord ++ tailWord_1097861).sum := by decide
  have hdescent : baseEnd_1097861 < baseStart_1097861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097888 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1097888 : Nat := 118140960795 + 1097888 * 2 ^ 59
def prefixEnd_1097888 : Nat := 4983230072969 + 3 ^ 40 * 1097888 * 2
def baseEnd_1097888 : Nat := 563744248803505741850911

theorem tailTrace_1097888 : CollatzResearch.WordTrace tailWord_1097888 prefixEnd_1097888 563744248803505741850911 := by
  unfold tailWord_1097888
  simp only [CollatzResearch.WordTrace]
  refine ⟨20021632523273377593763159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26695510031031170125017545 20021632523273377593763159)
  ·
    refine ⟨30032448784910066390644739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20021632523273377593763159 30032448784910066390644739)
    ·
      refine ⟨45048673177365099585967109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30032448784910066390644739 45048673177365099585967109)
      ·
        refine ⟨8446626220755956172368833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45048673177365099585967109 8446626220755956172368833)
        ·
          refine ⟨6334969665566967129276625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8446626220755956172368833 6334969665566967129276625)
          ·
            refine ⟨4751227249175225346957469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6334969665566967129276625 4751227249175225346957469)
            ·
              refine ⟨1781710218440709505109051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4751227249175225346957469 1781710218440709505109051)
              ·
                refine ⟨2672565327661064257663577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781710218440709505109051 2672565327661064257663577)
                ·
                  refine ⟨2004423995745798193247683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2672565327661064257663577 2004423995745798193247683)
                  ·
                    refine ⟨3006635993618697289871525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2004423995745798193247683 3006635993618697289871525)
                    ·
                      refine ⟨563744248803505741850911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3006635993618697289871525 563744248803505741850911)
                      ·
                        rfl

theorem cell23_1097888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1097888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097888 prefixEnd_1097888 := by exact prefixLift 1097888
  have htrace : WordTrace (prefixWord ++ tailWord_1097888) baseStart_1097888 baseEnd_1097888 := by
    simpa [prefixWord, tailWord_1097888, baseEnd_1097888] using wordTrace_append hprefix tailTrace_1097888
  have hstable : (prefixWord ++ tailWord_1097888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097888).length < 2 ^ (prefixWord ++ tailWord_1097888).sum := by decide
  have hdescent : baseEnd_1097888 < baseStart_1097888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097911 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 8]
def baseStart_1097911 : Nat := 118140960795 + 1097911 * 2 ^ 59
def prefixEnd_1097911 : Nat := 4983230072969 + 3 ^ 40 * 1097911 * 2
def baseEnd_1097911 : Nat := 62639562095395461318145

theorem tailTrace_1097911 : CollatzResearch.WordTrace tailWord_1097911 prefixEnd_1097911 62639562095395461318145 := by
  unfold tailWord_1097911
  simp only [CollatzResearch.WordTrace]
  refine ⟨40044103925463430115613587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26696069283642286743742391 40044103925463430115613587)
  ·
    refine ⟨60066155888195145173420381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40044103925463430115613587 60066155888195145173420381)
    ·
      refine ⟨22524808458073179440032643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60066155888195145173420381 22524808458073179440032643)
      ·
        refine ⟨33787212687109769160048965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22524808458073179440032643 33787212687109769160048965)
        ·
          refine ⟨6335102378833081717509181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33787212687109769160048965 6335102378833081717509181)
          ·
            refine ⟨2375663392062405644065943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6335102378833081717509181 2375663392062405644065943)
            ·
              refine ⟨3563495088093608466098915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2375663392062405644065943 3563495088093608466098915)
              ·
                refine ⟨5345242632140412699148373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563495088093608466098915 5345242632140412699148373)
                ·
                  refine ⟨62639562095395461318145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5345242632140412699148373 62639562095395461318145)
                  ·
                    rfl

theorem cell23_1097911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 8].length) (baseStart_1097911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097911 prefixEnd_1097911 := by exact prefixLift 1097911
  have htrace : WordTrace (prefixWord ++ tailWord_1097911) baseStart_1097911 baseEnd_1097911 := by
    simpa [prefixWord, tailWord_1097911, baseEnd_1097911] using wordTrace_append hprefix tailTrace_1097911
  have hstable : (prefixWord ++ tailWord_1097911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097911).length < 2 ^ (prefixWord ++ tailWord_1097911).sum := by decide
  have hdescent : baseEnd_1097911 < baseStart_1097911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097949 : List Nat := [1, 4, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1097949 : Nat := 118140960795 + 1097949 * 2 ^ 59
def prefixEnd_1097949 : Nat := 4983230072969 + 3 ^ 40 * 1097949 * 2
def baseEnd_1097949 : Nat := 187925190374476667729377

theorem tailTrace_1097949 : CollatzResearch.WordTrace tailWord_1097949 prefixEnd_1097949 187925190374476667729377 := by
  unfold tailWord_1097949
  simp only [CollatzResearch.WordTrace]
  refine ⟨40045489899325762605496901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26696993266217175070331267 40045489899325762605496901)
  ·
    refine ⟨7508529356123580488530669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40045489899325762605496901 7508529356123580488530669)
    ·
      refine ⟨2815698508546342683199001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7508529356123580488530669 2815698508546342683199001)
      ·
        refine ⟨2111773881409757012399251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2815698508546342683199001 2111773881409757012399251)
        ·
          refine ⟨3167660822114635518598877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111773881409757012399251 3167660822114635518598877)
          ·
            refine ⟨1187872808292988319474579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3167660822114635518598877 1187872808292988319474579)
            ·
              refine ⟨1781809212439482479211869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187872808292988319474579 1781809212439482479211869)
              ·
                refine ⟨668178454664805929704451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1781809212439482479211869 668178454664805929704451)
                ·
                  refine ⟨1002267681997208894556677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668178454664805929704451 1002267681997208894556677)
                  ·
                    refine ⟨187925190374476667729377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1002267681997208894556677 187925190374476667729377)
                    ·
                      rfl

theorem cell23_1097949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1097949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097949 prefixEnd_1097949 := by exact prefixLift 1097949
  have htrace : WordTrace (prefixWord ++ tailWord_1097949) baseStart_1097949 baseEnd_1097949 := by
    simpa [prefixWord, tailWord_1097949, baseEnd_1097949] using wordTrace_append hprefix tailTrace_1097949
  have hstable : (prefixWord ++ tailWord_1097949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097949).length < 2 ^ (prefixWord ++ tailWord_1097949).sum := by decide
  have hdescent : baseEnd_1097949 < baseStart_1097949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1097995 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 5, 2, 2]
def baseStart_1097995 : Nat := 118140960795 + 1097995 * 2 ^ 59
def prefixEnd_1097995 : Nat := 4983230072969 + 3 ^ 40 * 1097995 * 2
def baseEnd_1097995 : Nat := 563799191233536823212919

theorem tailTrace_1097995 : CollatzResearch.WordTrace tailWord_1097995 prefixEnd_1097995 563799191233536823212919 := by
  unfold tailWord_1097995
  simp only [CollatzResearch.WordTrace]
  refine ⟨40047167657159112461671439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26698111771439408307780959 40047167657159112461671439)
  ·
    refine ⟨60070751485738668692507159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40047167657159112461671439 60070751485738668692507159)
    ·
      refine ⟨90106127228608003038760739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60070751485738668692507159 90106127228608003038760739)
      ·
        refine ⟨135159190842912004558141109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90106127228608003038760739 135159190842912004558141109)
        ·
          refine ⟨12671174141523000427325729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135159190842912004558141109 12671174141523000427325729)
          ·
            refine ⟨9503380606142250320494297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12671174141523000427325729 9503380606142250320494297)
            ·
              refine ⟨7127535454606687740370723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9503380606142250320494297 7127535454606687740370723)
              ·
                refine ⟨10691303181910031610556085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7127535454606687740370723 10691303181910031610556085)
                ·
                  refine ⟨1002309673304065463489633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10691303181910031610556085 1002309673304065463489633)
                  ·
                    refine ⟨751732254978049097617225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1002309673304065463489633 751732254978049097617225)
                    ·
                      refine ⟨563799191233536823212919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751732254978049097617225 563799191233536823212919)
                      ·
                        rfl

theorem cell23_1097995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 2, 2].length) (baseStart_1097995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1097995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1097995 prefixEnd_1097995 := by exact prefixLift 1097995
  have htrace : WordTrace (prefixWord ++ tailWord_1097995) baseStart_1097995 baseEnd_1097995 := by
    simpa [prefixWord, tailWord_1097995, baseEnd_1097995] using wordTrace_append hprefix tailTrace_1097995
  have hstable : (prefixWord ++ tailWord_1097995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1097995).length < 2 ^ (prefixWord ++ tailWord_1097995).sum := by decide
  have hdescent : baseEnd_1097995 < baseStart_1097995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1097995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098001 : List Nat := [1, 2, 2, 1, 1, 5, 2, 9]
def baseStart_1098001 : Nat := 118140960795 + 1098001 * 2 ^ 59
def prefixEnd_1098001 : Nat := 4983230072969 + 3 ^ 40 * 1098001 * 2
def baseEnd_1098001 : Nat := 20881565633980140731033

theorem tailTrace_1098001 : CollatzResearch.WordTrace tailWord_1098001 prefixEnd_1098001 20881565633980140731033 := by
  unfold tailWord_1098001
  simp only [CollatzResearch.WordTrace]
  refine ⟨40047386495137375486389857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26698257663424916990926571 40047386495137375486389857)
  ·
    refine ⟨30035539871353031614792393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40047386495137375486389857 30035539871353031614792393)
    ·
      refine ⟨22526654903514773711094295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30035539871353031614792393 22526654903514773711094295)
      ·
        refine ⟨33789982355272160566641443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22526654903514773711094295 33789982355272160566641443)
        ·
          refine ⟨50684973532908240849962165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33789982355272160566641443 50684973532908240849962165)
          ·
            refine ⟨4751716268710147579683953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50684973532908240849962165 4751716268710147579683953)
            ·
              refine ⟨3563787201532610684762965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4751716268710147579683953 3563787201532610684762965)
              ·
                refine ⟨20881565633980140731033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3563787201532610684762965 20881565633980140731033)
                ·
                  rfl

theorem cell23_1098001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 9].length) (baseStart_1098001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098001 prefixEnd_1098001 := by exact prefixLift 1098001
  have htrace : WordTrace (prefixWord ++ tailWord_1098001) baseStart_1098001 baseEnd_1098001 := by
    simpa [prefixWord, tailWord_1098001, baseEnd_1098001] using wordTrace_append hprefix tailTrace_1098001
  have hstable : (prefixWord ++ tailWord_1098001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098001).length < 2 ^ (prefixWord ++ tailWord_1098001).sum := by decide
  have hdescent : baseEnd_1098001 < baseStart_1098001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098008 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1098008 : Nat := 118140960795 + 1098008 * 2 ^ 59
def prefixEnd_1098008 : Nat := 4983230072969 + 3 ^ 40 * 1098008 * 2
def baseEnd_1098008 : Nat := 563805866482045272350359

theorem tailTrace_1098008 : CollatzResearch.WordTrace tailWord_1098008 prefixEnd_1098008 563805866482045272350359 := by
  unfold tailWord_1098008
  simp only [CollatzResearch.WordTrace]
  refine ⟨20023820903056007840947339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26698427870741343787929785 20023820903056007840947339)
  ·
    refine ⟨30035731354584011761421009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20023820903056007840947339 30035731354584011761421009)
    ·
      refine ⟨22526798515938008821065757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30035731354584011761421009 22526798515938008821065757)
      ·
        refine ⟨8447549443476753307899659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22526798515938008821065757 8447549443476753307899659)
        ·
          refine ⟨12671324165215129961849489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8447549443476753307899659 12671324165215129961849489)
          ·
            refine ⟨9503493123911347471387117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12671324165215129961849489 9503493123911347471387117)
            ·
              refine ⟨3563809921466755301770169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9503493123911347471387117 3563809921466755301770169)
              ·
                refine ⟨2672857441100066476327627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3563809921466755301770169 2672857441100066476327627)
                ·
                  refine ⟨4009286161650099714491441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672857441100066476327627 4009286161650099714491441)
                  ·
                    refine ⟨3006964621237574785868581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009286161650099714491441 3006964621237574785868581)
                    ·
                      refine ⟨563805866482045272350359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3006964621237574785868581 563805866482045272350359)
                      ·
                        rfl

theorem cell23_1098008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1098008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098008 prefixEnd_1098008 := by exact prefixLift 1098008
  have htrace : WordTrace (prefixWord ++ tailWord_1098008) baseStart_1098008 baseEnd_1098008 := by
    simpa [prefixWord, tailWord_1098008, baseEnd_1098008] using wordTrace_append hprefix tailTrace_1098008
  have hstable : (prefixWord ++ tailWord_1098008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098008).length < 2 ^ (prefixWord ++ tailWord_1098008).sum := by decide
  have hdescent : baseEnd_1098008 < baseStart_1098008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098015 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 5]
def baseStart_1098015 : Nat := 118140960795 + 1098015 * 2 ^ 59
def prefixEnd_1098015 : Nat := 4983230072969 + 3 ^ 40 * 1098015 * 2
def baseEnd_1098015 : Nat := 563809460846626744962827

theorem tailTrace_1098015 : CollatzResearch.WordTrace tailWord_1098015 prefixEnd_1098015 563809460846626744962827 := by
  unfold tailWord_1098015
  simp only [CollatzResearch.WordTrace]
  refine ⟨40047897117086655877399499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26698598078057770584932999 40047897117086655877399499)
  ·
    refine ⟨60071845675629983816099249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40047897117086655877399499 60071845675629983816099249)
    ·
      refine ⟨45053884256722487862074437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60071845675629983816099249 45053884256722487862074437)
      ·
        refine ⟨8447603298135466474138957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45053884256722487862074437 8447603298135466474138957)
        ·
          refine ⟨3167851236800799927802109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8447603298135466474138957 3167851236800799927802109)
          ·
            refine ⟨1187944213800299972925791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3167851236800799927802109 1187944213800299972925791)
            ·
              refine ⟨1781916320700449959388687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187944213800299972925791 1781916320700449959388687)
              ·
                refine ⟨2672874481050674939083031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781916320700449959388687 2672874481050674939083031)
                ·
                  refine ⟨4009311721576012408624547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672874481050674939083031 4009311721576012408624547)
                  ·
                    refine ⟨6013967582364018612936821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4009311721576012408624547 6013967582364018612936821)
                    ·
                      refine ⟨563809460846626744962827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6013967582364018612936821 563809460846626744962827)
                      ·
                        rfl

theorem cell23_1098015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_1098015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098015 prefixEnd_1098015 := by exact prefixLift 1098015
  have htrace : WordTrace (prefixWord ++ tailWord_1098015) baseStart_1098015 baseEnd_1098015 := by
    simpa [prefixWord, tailWord_1098015, baseEnd_1098015] using wordTrace_append hprefix tailTrace_1098015
  have hstable : (prefixWord ++ tailWord_1098015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098015).length < 2 ^ (prefixWord ++ tailWord_1098015).sum := by decide
  have hdescent : baseEnd_1098015 < baseStart_1098015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098023 : List Nat := [1, 1, 8, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_1098023 : Nat := 118140960795 + 1098023 * 2 ^ 59
def prefixEnd_1098023 : Nat := 4983230072969 + 3 ^ 40 * 1098023 * 2
def baseEnd_1098023 : Nat := 563813568691862713662791

theorem tailTrace_1098023 : CollatzResearch.WordTrace tailWord_1098023 prefixEnd_1098023 563813568691862713662791 := by
  unfold tailWord_1098023
  simp only [CollatzResearch.WordTrace]
  refine ⟨40048188901057673243690723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26698792600705115495793815 40048188901057673243690723)
  ·
    refine ⟨60072283351586509865536085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40048188901057673243690723 60072283351586509865536085)
    ·
      refine ⟨703972070526404412486751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 60072283351586509865536085 703972070526404412486751)
      ·
        refine ⟨1055958105789606618730127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703972070526404412486751 1055958105789606618730127)
        ·
          refine ⟨1583937158684409928095191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055958105789606618730127 1583937158684409928095191)
          ·
            refine ⟨2375905738026614892142787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583937158684409928095191 2375905738026614892142787)
            ·
              refine ⟨3563858607039922338214181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2375905738026614892142787 3563858607039922338214181)
              ·
                refine ⟨668223488819985438415159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3563858607039922338214181 668223488819985438415159)
                ·
                  refine ⟨1002335233229978157622739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668223488819985438415159 1002335233229978157622739)
                  ·
                    refine ⟨1503502849844967236434109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1002335233229978157622739 1503502849844967236434109)
                    ·
                      refine ⟨563813568691862713662791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1503502849844967236434109 563813568691862713662791)
                      ·
                        rfl

theorem cell23_1098023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_1098023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098023 prefixEnd_1098023 := by exact prefixLift 1098023
  have htrace : WordTrace (prefixWord ++ tailWord_1098023) baseStart_1098023 baseEnd_1098023 := by
    simpa [prefixWord, tailWord_1098023, baseEnd_1098023] using wordTrace_append hprefix tailTrace_1098023
  have hstable : (prefixWord ++ tailWord_1098023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098023).length < 2 ^ (prefixWord ++ tailWord_1098023).sum := by decide
  have hdescent : baseEnd_1098023 < baseStart_1098023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098031 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 2, 7]
def baseStart_1098031 : Nat := 118140960795 + 1098031 * 2 ^ 59
def prefixEnd_1098031 : Nat := 4983230072969 + 3 ^ 40 * 1098031 * 2
def baseEnd_1098031 : Nat := 187939225512366227454251

theorem tailTrace_1098031 : CollatzResearch.WordTrace tailWord_1098031 prefixEnd_1098031 187939225512366227454251 := by
  unfold tailWord_1098031
  simp only [CollatzResearch.WordTrace]
  refine ⟨40048480685028690609981947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26698987123352460406654631 40048480685028690609981947)
  ·
    refine ⟨60072721027543035914972921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40048480685028690609981947 60072721027543035914972921)
    ·
      refine ⟨45054540770657276936229691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60072721027543035914972921 45054540770657276936229691)
      ·
        refine ⟨67581811155985915404344537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45054540770657276936229691 67581811155985915404344537)
        ·
          refine ⟨50686358366989436553258403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67581811155985915404344537 50686358366989436553258403)
          ·
            refine ⟨76029537550484154829887605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50686358366989436553258403 76029537550484154829887605)
            ·
              refine ⟨7127769145357889515301963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76029537550484154829887605 7127769145357889515301963)
              ·
                refine ⟨10691653718036834272952945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7127769145357889515301963 10691653718036834272952945)
                ·
                  refine ⟨8018740288527625704714709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10691653718036834272952945 8018740288527625704714709)
                  ·
                    refine ⟨187939225512366227454251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8018740288527625704714709 187939225512366227454251)
                    ·
                      rfl

theorem cell23_1098031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_1098031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098031 prefixEnd_1098031 := by exact prefixLift 1098031
  have htrace : WordTrace (prefixWord ++ tailWord_1098031) baseStart_1098031 baseEnd_1098031 := by
    simpa [prefixWord, tailWord_1098031, baseEnd_1098031] using wordTrace_append hprefix tailTrace_1098031
  have hstable : (prefixWord ++ tailWord_1098031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098031).length < 2 ^ (prefixWord ++ tailWord_1098031).sum := by decide
  have hdescent : baseEnd_1098031 < baseStart_1098031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098052 : List Nat := [2, 3, 4, 1, 2, 1, 3, 7]
def baseStart_1098052 : Nat := 118140960795 + 1098052 * 2 ^ 59
def prefixEnd_1098052 : Nat := 4983230072969 + 3 ^ 40 * 1098052 * 2
def baseEnd_1098052 : Nat := 20882535541883077785191

theorem tailTrace_1098052 : CollatzResearch.WordTrace tailWord_1098052 prefixEnd_1098052 20882535541883077785191 := by
  unfold tailWord_1098052
  simp only [CollatzResearch.WordTrace]
  refine ⟨20024623308976305598248205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26699497745301740797664273 20024623308976305598248205)
  ·
    refine ⟨7509233740866114599343077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20024623308976305598248205 7509233740866114599343077)
    ·
      refine ⟨1407981326412396487376827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7509233740866114599343077 1407981326412396487376827)
      ·
        refine ⟨2111971989618594731065241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407981326412396487376827 2111971989618594731065241)
        ·
          refine ⟨1583978992213946048298931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2111971989618594731065241 1583978992213946048298931)
          ·
            refine ⟨2375968488320919072448397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583978992213946048298931 2375968488320919072448397)
            ·
              refine ⟨890988183120344652168149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2375968488320919072448397 890988183120344652168149)
              ·
                refine ⟨20882535541883077785191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 890988183120344652168149 20882535541883077785191)
                ·
                  rfl

theorem cell23_1098052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 7].length) (baseStart_1098052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098052 prefixEnd_1098052 := by exact prefixLift 1098052
  have htrace : WordTrace (prefixWord ++ tailWord_1098052) baseStart_1098052 baseEnd_1098052 := by
    simpa [prefixWord, tailWord_1098052, baseEnd_1098052] using wordTrace_append hprefix tailTrace_1098052
  have hstable : (prefixWord ++ tailWord_1098052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098052).length < 2 ^ (prefixWord ++ tailWord_1098052).sum := by decide
  have hdescent : baseEnd_1098052 < baseStart_1098052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098055 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_1098055 : Nat := 118140960795 + 1098055 * 2 ^ 59
def prefixEnd_1098055 : Nat := 4983230072969 + 3 ^ 40 * 1098055 * 2
def baseEnd_1098055 : Nat := 563830000072806588462643

theorem tailTrace_1098055 : CollatzResearch.WordTrace tailWord_1098055 prefixEnd_1098055 563830000072806588462643 := by
  unfold tailWord_1098055
  simp only [CollatzResearch.WordTrace]
  refine ⟨40049356036941742708855619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26699570691294495139237079 40049356036941742708855619)
  ·
    refine ⟨60074034055412614063283429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40049356036941742708855619 60074034055412614063283429)
    ·
      refine ⟨11263881385389865136865643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60074034055412614063283429 11263881385389865136865643)
      ·
        refine ⟨16895822078084797705298465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11263881385389865136865643 16895822078084797705298465)
        ·
          refine ⟨12671866558563598278973849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16895822078084797705298465 12671866558563598278973849)
          ·
            refine ⟨9503899918922698709230387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12671866558563598278973849 9503899918922698709230387)
            ·
              refine ⟨14255849878384048063845581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9503899918922698709230387 14255849878384048063845581)
              ·
                refine ⟨5345943704394018023942093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14255849878384048063845581 5345943704394018023942093)
                ·
                  refine ⟨2004728889147756758978285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5345943704394018023942093 2004728889147756758978285)
                  ·
                    refine ⟨751773333430408784616857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2004728889147756758978285 751773333430408784616857)
                    ·
                      refine ⟨563830000072806588462643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751773333430408784616857 563830000072806588462643)
                      ·
                        rfl

theorem cell23_1098055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_1098055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098055 prefixEnd_1098055 := by exact prefixLift 1098055
  have htrace : WordTrace (prefixWord ++ tailWord_1098055) baseStart_1098055 baseEnd_1098055 := by
    simpa [prefixWord, tailWord_1098055, baseEnd_1098055] using wordTrace_append hprefix tailTrace_1098055
  have hstable : (prefixWord ++ tailWord_1098055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098055).length < 2 ^ (prefixWord ++ tailWord_1098055).sum := by decide
  have hdescent : baseEnd_1098055 < baseStart_1098055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098091 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 11]
def baseStart_1098091 : Nat := 118140960795 + 1098091 * 2 ^ 59
def prefixEnd_1098091 : Nat := 4983230072969 + 3 ^ 40 * 1098091 * 2
def baseEnd_1098091 : Nat := 62649831708485383068053

theorem tailTrace_1098091 : CollatzResearch.WordTrace tailWord_1098091 prefixEnd_1098091 62649831708485383068053 := by
  unfold tailWord_1098091
  simp only [CollatzResearch.WordTrace]
  refine ⟨40050669064811320857166127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26700446043207547238110751 40050669064811320857166127)
  ·
    refine ⟨60076003597216981285749191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40050669064811320857166127 60076003597216981285749191)
    ·
      refine ⟨90114005395825471928623787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60076003597216981285749191 90114005395825471928623787)
      ·
        refine ⟨135171008093738207892935681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90114005395825471928623787 135171008093738207892935681)
        ·
          refine ⟨101378256070303655919701761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135171008093738207892935681 101378256070303655919701761)
          ·
            refine ⟨76033692052727741939776321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101378256070303655919701761 76033692052727741939776321)
            ·
              refine ⟨57025269039545806454832241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76033692052727741939776321 57025269039545806454832241)
              ·
                refine ⟨42768951779659354841124181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57025269039545806454832241 42768951779659354841124181)
                ·
                  refine ⟨62649831708485383068053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 42768951779659354841124181 62649831708485383068053)
                  ·
                    rfl

theorem cell23_1098091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 11].length) (baseStart_1098091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098091 prefixEnd_1098091 := by exact prefixLift 1098091
  have htrace : WordTrace (prefixWord ++ tailWord_1098091) baseStart_1098091 baseEnd_1098091 := by
    simpa [prefixWord, tailWord_1098091, baseEnd_1098091] using wordTrace_append hprefix tailTrace_1098091
  have hstable : (prefixWord ++ tailWord_1098091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098091).length < 2 ^ (prefixWord ++ tailWord_1098091).sum := by decide
  have hdescent : baseEnd_1098091 < baseStart_1098091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098122 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1098122 : Nat := 118140960795 + 1098122 * 2 ^ 59
def prefixEnd_1098122 : Nat := 4983230072969 + 3 ^ 40 * 1098122 * 2
def baseEnd_1098122 : Nat := 563864403276657826324835

theorem tailTrace_1098122 : CollatzResearch.WordTrace tailWord_1098122 prefixEnd_1098122 563864403276657826324835 := by
  unfold tailWord_1098122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012949931924753287886155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26701199818466008767696413 10012949931924753287886155)
  ·
    refine ⟨15019424897887129931829233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10012949931924753287886155 15019424897887129931829233)
    ·
      refine ⟨11264568673415347448871925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15019424897887129931829233 11264568673415347448871925)
      ·
        refine ⟨1056053313132688823331743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11264568673415347448871925 1056053313132688823331743)
        ·
          refine ⟨1584079969699033234997615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056053313132688823331743 1584079969699033234997615)
          ·
            refine ⟨2376119954548549852496423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584079969699033234997615 2376119954548549852496423)
            ·
              refine ⟨3564179931822824778744635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376119954548549852496423 3564179931822824778744635)
              ·
                refine ⟨5346269897734237168116953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3564179931822824778744635 5346269897734237168116953)
                ·
                  refine ⟨4009702423300677876087715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5346269897734237168116953 4009702423300677876087715)
                  ·
                    refine ⟨6014553634951016814131573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4009702423300677876087715 6014553634951016814131573)
                    ·
                      refine ⟨563864403276657826324835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6014553634951016814131573 563864403276657826324835)
                      ·
                        rfl

theorem cell23_1098122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1098122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098122 prefixEnd_1098122 := by exact prefixLift 1098122
  have htrace : WordTrace (prefixWord ++ tailWord_1098122) baseStart_1098122 baseEnd_1098122 := by
    simpa [prefixWord, tailWord_1098122, baseEnd_1098122] using wordTrace_append hprefix tailTrace_1098122
  have hstable : (prefixWord ++ tailWord_1098122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098122).length < 2 ^ (prefixWord ++ tailWord_1098122).sum := by decide
  have hdescent : baseEnd_1098122 < baseStart_1098122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098142 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1098142 : Nat := 118140960795 + 1098142 * 2 ^ 59
def prefixEnd_1098142 : Nat := 4983230072969 + 3 ^ 40 * 1098142 * 2
def baseEnd_1098142 : Nat := 62652741432194194230527

theorem tailTrace_1098142 : CollatzResearch.WordTrace tailWord_1098142 prefixEnd_1098142 62652741432194194230527 := by
  unfold tailWord_1098142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006566148453319570909085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26701686125084371044848453 5006566148453319570909085)
  ·
    refine ⟨1877462305669994839090907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5006566148453319570909085 1877462305669994839090907)
    ·
      refine ⟨2816193458504992258636361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877462305669994839090907 2816193458504992258636361)
      ·
        refine ⟨2112145093878744193977271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2816193458504992258636361 2112145093878744193977271)
        ·
          refine ⟨3168217640818116290965907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112145093878744193977271 3168217640818116290965907)
          ·
            refine ⟨4752326461227174436448861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168217640818116290965907 4752326461227174436448861)
            ·
              refine ⟨1782122422960190413668323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4752326461227174436448861 1782122422960190413668323)
              ·
                refine ⟨2673183634440285620502485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782122422960190413668323 2673183634440285620502485)
                ·
                  refine ⟨62652741432194194230527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2673183634440285620502485 62652741432194194230527)
                  ·
                    rfl

theorem cell23_1098142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1098142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098142 prefixEnd_1098142 := by exact prefixLift 1098142
  have htrace : WordTrace (prefixWord ++ tailWord_1098142) baseStart_1098142 baseEnd_1098142 := by
    simpa [prefixWord, tailWord_1098142, baseEnd_1098142] using wordTrace_append hprefix tailTrace_1098142
  have hstable : (prefixWord ++ tailWord_1098142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098142).length < 2 ^ (prefixWord ++ tailWord_1098142).sum := by decide
  have hdescent : baseEnd_1098142 < baseStart_1098142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098148 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1098148 : Nat := 118140960795 + 1098148 * 2 ^ 59
def prefixEnd_1098148 : Nat := 4983230072969 + 3 ^ 40 * 1098148 * 2
def baseEnd_1098148 : Nat := 563877753773674724599715

theorem tailTrace_1098148 : CollatzResearch.WordTrace tailWord_1098148 prefixEnd_1098148 563877753773674724599715 := by
  unfold tailWord_1098148
  simp only [CollatzResearch.WordTrace]
  refine ⟨20026374012802409795995549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26701832017069879727994065 20026374012802409795995549)
  ·
    refine ⟨7509890254800903673498331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20026374012802409795995549 7509890254800903673498331)
    ·
      refine ⟨11264835382201355510247497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509890254800903673498331 11264835382201355510247497)
      ·
        refine ⟨8448626536651016632685623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11264835382201355510247497 8448626536651016632685623)
        ·
          refine ⟨12672939804976524949028435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8448626536651016632685623 12672939804976524949028435)
          ·
            refine ⟨19009409707464787423542653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12672939804976524949028435 19009409707464787423542653)
            ·
              refine ⟨7128528640299295283828495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19009409707464787423542653 7128528640299295283828495)
              ·
                refine ⟨10692792960448942925742743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128528640299295283828495 10692792960448942925742743)
                ·
                  refine ⟨16039189440673414388614115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10692792960448942925742743 16039189440673414388614115)
                  ·
                    refine ⟨24058784161010121582921173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16039189440673414388614115 24058784161010121582921173)
                    ·
                      refine ⟨563877753773674724599715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24058784161010121582921173 563877753773674724599715)
                      ·
                        rfl

theorem cell23_1098148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1098148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098148 prefixEnd_1098148 := by exact prefixLift 1098148
  have htrace : WordTrace (prefixWord ++ tailWord_1098148) baseStart_1098148 baseEnd_1098148 := by
    simpa [prefixWord, tailWord_1098148, baseEnd_1098148] using wordTrace_append hprefix tailTrace_1098148
  have hstable : (prefixWord ++ tailWord_1098148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098148).length < 2 ^ (prefixWord ++ tailWord_1098148).sum := by decide
  have hdescent : baseEnd_1098148 < baseStart_1098148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098172 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_1098172 : Nat := 118140960795 + 1098172 * 2 ^ 59
def prefixEnd_1098172 : Nat := 4983230072969 + 3 ^ 40 * 1098172 * 2
def baseEnd_1098172 : Nat := 187963359103127543566535

theorem tailTrace_1098172 : CollatzResearch.WordTrace tailWord_1098172 prefixEnd_1098172 187963359103127543566535 := by
  unfold tailWord_1098172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20026811688758935845432385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26702415585011914460576513 20026811688758935845432385)
  ·
    refine ⟨15020108766569201884074289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20026811688758935845432385 15020108766569201884074289)
    ·
      refine ⟨11265081574926901413055717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15020108766569201884074289 11265081574926901413055717)
      ·
        refine ⟨2112202795298794014947947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11265081574926901413055717 2112202795298794014947947)
        ·
          refine ⟨3168304192948191022421921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112202795298794014947947 3168304192948191022421921)
          ·
            refine ⟨2376228144711143266816441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3168304192948191022421921 2376228144711143266816441)
            ·
              refine ⟨1782171108533357450112331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2376228144711143266816441 1782171108533357450112331)
              ·
                refine ⟨2673256662800036175168497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782171108533357450112331 2673256662800036175168497)
                ·
                  refine ⟨2004942497100027131376373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2673256662800036175168497 2004942497100027131376373)
                  ·
                    refine ⟨187963359103127543566535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2004942497100027131376373 187963359103127543566535)
                    ·
                      rfl

theorem cell23_1098172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_1098172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098172 prefixEnd_1098172 := by exact prefixLift 1098172
  have htrace : WordTrace (prefixWord ++ tailWord_1098172) baseStart_1098172 baseEnd_1098172 := by
    simpa [prefixWord, tailWord_1098172, baseEnd_1098172] using wordTrace_append hprefix tailTrace_1098172
  have hstable : (prefixWord ++ tailWord_1098172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098172).length < 2 ^ (prefixWord ++ tailWord_1098172).sum := by decide
  have hdescent : baseEnd_1098172 < baseStart_1098172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098175 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 6, 4, 2]
def baseStart_1098175 : Nat := 118140960795 + 1098175 * 2 ^ 59
def prefixEnd_1098175 : Nat := 4983230072969 + 3 ^ 40 * 1098175 * 2
def baseEnd_1098175 : Nat := 563891617751346118962091

theorem tailTrace_1098175 : CollatzResearch.WordTrace tailWord_1098175 prefixEnd_1098175 563891617751346118962091 := by
  unfold tailWord_1098175
  simp only [CollatzResearch.WordTrace]
  refine ⟨40053732796507003203223979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26702488531004668802149319 40053732796507003203223979)
  ·
    refine ⟨60080599194760504804835969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40053732796507003203223979 60080599194760504804835969)
    ·
      refine ⟨45060449396070378603626977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60080599194760504804835969 45060449396070378603626977)
      ·
        refine ⟨33795337047052783952720233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45060449396070378603626977 33795337047052783952720233)
        ·
          refine ⟨25346502785289587964540175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33795337047052783952720233 25346502785289587964540175)
          ·
            refine ⟨38019754177934381946810263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25346502785289587964540175 38019754177934381946810263)
            ·
              refine ⟨57029631266901572920215395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38019754177934381946810263 57029631266901572920215395)
              ·
                refine ⟨85544446900352359380323093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57029631266901572920215395 85544446900352359380323093)
                ·
                  refine ⟨4009895948454016845952645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85544446900352359380323093 4009895948454016845952645)
                  ·
                    refine ⟨751855490335128158616121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009895948454016845952645 751855490335128158616121)
                    ·
                      refine ⟨563891617751346118962091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751855490335128158616121 563891617751346118962091)
                      ·
                        rfl

theorem cell23_1098175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_1098175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098175 prefixEnd_1098175 := by exact prefixLift 1098175
  have htrace : WordTrace (prefixWord ++ tailWord_1098175) baseStart_1098175 baseEnd_1098175 := by
    simpa [prefixWord, tailWord_1098175, baseEnd_1098175] using wordTrace_append hprefix tailTrace_1098175
  have hstable : (prefixWord ++ tailWord_1098175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098175).length < 2 ^ (prefixWord ++ tailWord_1098175).sum := by decide
  have hdescent : baseEnd_1098175 < baseStart_1098175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098215 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 6]
def baseStart_1098215 : Nat := 118140960795 + 1098215 * 2 ^ 59
def prefixEnd_1098215 : Nat := 4983230072969 + 3 ^ 40 * 1098215 * 2
def baseEnd_1098215 : Nat := 62656906330836218051323

theorem tailTrace_1098215 : CollatzResearch.WordTrace tailWord_1098215 prefixEnd_1098215 62656906330836218051323 := by
  unfold tailWord_1098215
  simp only [CollatzResearch.WordTrace]
  refine ⟨40055191716362090034680099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26703461144241393356453399 40055191716362090034680099)
  ·
    refine ⟨60082787574543135052020149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40055191716362090034680099 60082787574543135052020149)
    ·
      refine ⟨5632761335113418911126889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60082787574543135052020149 5632761335113418911126889)
      ·
        refine ⟨4224571001335064183345167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5632761335113418911126889 4224571001335064183345167)
        ·
          refine ⟨6336856502002596275017751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224571001335064183345167 6336856502002596275017751)
          ·
            refine ⟨9505284753003894412526627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336856502002596275017751 9505284753003894412526627)
            ·
              refine ⟨14257927129505841618789941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9505284753003894412526627 14257927129505841618789941)
              ·
                refine ⟨1336680668391172651761557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14257927129505841618789941 1336680668391172651761557)
                ·
                  refine ⟨62656906330836218051323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1336680668391172651761557 62656906330836218051323)
                  ·
                    rfl

theorem cell23_1098215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 6].length) (baseStart_1098215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098215 prefixEnd_1098215 := by exact prefixLift 1098215
  have htrace : WordTrace (prefixWord ++ tailWord_1098215) baseStart_1098215 baseEnd_1098215 := by
    simpa [prefixWord, tailWord_1098215, baseEnd_1098215] using wordTrace_append hprefix tailTrace_1098215
  have hstable : (prefixWord ++ tailWord_1098215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098215).length < 2 ^ (prefixWord ++ tailWord_1098215).sum := by decide
  have hdescent : baseEnd_1098215 < baseStart_1098215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098226 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1098226 : Nat := 118140960795 + 1098226 * 2 ^ 59
def prefixEnd_1098226 : Nat := 4983230072969 + 3 ^ 40 * 1098226 * 2
def baseEnd_1098226 : Nat := 563917805264725419424357

theorem tailTrace_1098226 : CollatzResearch.WordTrace tailWord_1098226 prefixEnd_1098226 563917805264725419424357 := by
  unfold tailWord_1098226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10013898229830559728332633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26703728612881492608887021 10013898229830559728332633)
  ·
    refine ⟨7510423672372919796249475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10013898229830559728332633 7510423672372919796249475)
    ·
      refine ⟨11265635508559379694374213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7510423672372919796249475 11265635508559379694374213)
      ·
        refine ⟨2112306657854883692695165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11265635508559379694374213 2112306657854883692695165)
        ·
          refine ⟨792114996695581384760687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2112306657854883692695165 792114996695581384760687)
          ·
            refine ⟨1188172495043372077141031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792114996695581384760687 1188172495043372077141031)
            ·
              refine ⟨1782258742565058115711547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188172495043372077141031 1782258742565058115711547)
              ·
                refine ⟨2673388113847587173567321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782258742565058115711547 2673388113847587173567321)
                ·
                  refine ⟨2005041085385690380175491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2673388113847587173567321 2005041085385690380175491)
                  ·
                    refine ⟨3007561628078535570263237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005041085385690380175491 3007561628078535570263237)
                    ·
                      refine ⟨563917805264725419424357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3007561628078535570263237 563917805264725419424357)
                      ·
                        rfl

theorem cell23_1098226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1098226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098226 prefixEnd_1098226 := by exact prefixLift 1098226
  have htrace : WordTrace (prefixWord ++ tailWord_1098226) baseStart_1098226 baseEnd_1098226 := by
    simpa [prefixWord, tailWord_1098226, baseEnd_1098226] using wordTrace_append hprefix tailTrace_1098226
  have hstable : (prefixWord ++ tailWord_1098226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098226).length < 2 ^ (prefixWord ++ tailWord_1098226).sum := by decide
  have hdescent : baseEnd_1098226 < baseStart_1098226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098229 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1098229 : Nat := 118140960795 + 1098229 * 2 ^ 59
def prefixEnd_1098229 : Nat := 4983230072969 + 3 ^ 40 * 1098229 * 2
def baseEnd_1098229 : Nat := 563919345706688907686843

theorem tailTrace_1098229 : CollatzResearch.WordTrace tailWord_1098229 prefixEnd_1098229 563919345706688907686843 := by
  unfold tailWord_1098229
  simp only [CollatzResearch.WordTrace]
  refine ⟨40055702338311370425689741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26703801558874246950459827 40055702338311370425689741)
  ·
    refine ⟨15020888376866763909633653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40055702338311370425689741 15020888376866763909633653)
    ·
      refine ⟨1408208285331259116528155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15020888376866763909633653 1408208285331259116528155)
      ·
        refine ⟨2112312427996888674792233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408208285331259116528155 2112312427996888674792233)
        ·
          refine ⟨1584234320997666506094175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2112312427996888674792233 1584234320997666506094175)
          ·
            refine ⟨2376351481496499759141263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584234320997666506094175 2376351481496499759141263)
            ·
              refine ⟨3564527222244749638711895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376351481496499759141263 3564527222244749638711895)
              ·
                refine ⟨5346790833367124458067843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3564527222244749638711895 5346790833367124458067843)
                ·
                  refine ⟨8020186250050686687101765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5346790833367124458067843 8020186250050686687101765)
                  ·
                    refine ⟨1503784921884503753831581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8020186250050686687101765 1503784921884503753831581)
                    ·
                      refine ⟨563919345706688907686843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1503784921884503753831581 563919345706688907686843)
                      ·
                        rfl

theorem cell23_1098229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1098229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098229 prefixEnd_1098229 := by exact prefixLift 1098229
  have htrace : WordTrace (prefixWord ++ tailWord_1098229) baseStart_1098229 baseEnd_1098229 := by
    simpa [prefixWord, tailWord_1098229, baseEnd_1098229] using wordTrace_append hprefix tailTrace_1098229
  have hstable : (prefixWord ++ tailWord_1098229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098229).length < 2 ^ (prefixWord ++ tailWord_1098229).sum := by decide
  have hdescent : baseEnd_1098229 < baseStart_1098229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098253 : List Nat := [1, 7, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1098253 : Nat := 118140960795 + 1098253 * 2 ^ 59
def prefixEnd_1098253 : Nat := 4983230072969 + 3 ^ 40 * 1098253 * 2
def baseEnd_1098253 : Nat := 187977223080798937928911

theorem tailTrace_1098253 : CollatzResearch.WordTrace tailWord_1098253 prefixEnd_1098253 187977223080798937928911 := by
  unfold tailWord_1098253
  simp only [CollatzResearch.WordTrace]
  refine ⟨40056577690224422524563413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26704385126816281683042275 40056577690224422524563413)
  ·
    refine ⟨938826039614634902919455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 40056577690224422524563413 938826039614634902919455)
    ·
      refine ⟨1408239059421952354379183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 938826039614634902919455 1408239059421952354379183)
      ·
        refine ⟨2112358589132928531568775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408239059421952354379183 2112358589132928531568775)
        ·
          refine ⟨3168537883699392797353163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112358589132928531568775 3168537883699392797353163)
          ·
            refine ⟨4752806825549089196029745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168537883699392797353163 4752806825549089196029745)
            ·
              refine ⟨3564605119161816897022309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4752806825549089196029745 3564605119161816897022309)
              ·
                refine ⟨668363459842840668191683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3564605119161816897022309 668363459842840668191683)
                ·
                  refine ⟨1002545189764261002287525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668363459842840668191683 1002545189764261002287525)
                  ·
                    refine ⟨187977223080798937928911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1002545189764261002287525 187977223080798937928911)
                    ·
                      rfl

theorem cell23_1098253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1098253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098253 prefixEnd_1098253 := by exact prefixLift 1098253
  have htrace : WordTrace (prefixWord ++ tailWord_1098253) baseStart_1098253 baseEnd_1098253 := by
    simpa [prefixWord, tailWord_1098253, baseEnd_1098253] using wordTrace_append hprefix tailTrace_1098253
  have hstable : (prefixWord ++ tailWord_1098253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098253).length < 2 ^ (prefixWord ++ tailWord_1098253).sum := by decide
  have hdescent : baseEnd_1098253 < baseStart_1098253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098259 : List Nat := [1, 1, 1, 2, 1, 5, 1, 6, 1, 1, 3]
def baseStart_1098259 : Nat := 118140960795 + 1098259 * 2 ^ 59
def prefixEnd_1098259 : Nat := 4983230072969 + 3 ^ 40 * 1098259 * 2
def baseEnd_1098259 : Nat := 563934750126323790311705

theorem tailTrace_1098259 : CollatzResearch.WordTrace tailWord_1098259 prefixEnd_1098259 563934750126323790311705 := by
  unfold tailWord_1098259
  simp only [CollatzResearch.WordTrace]
  refine ⟨40056796528202685549281831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26704531018801790366187887 40056796528202685549281831)
  ·
    refine ⟨60085194792304028323922747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40056796528202685549281831 60085194792304028323922747)
    ·
      refine ⟨90127792188456042485884121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60085194792304028323922747 90127792188456042485884121)
      ·
        refine ⟨67595844141342031864413091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90127792188456042485884121 67595844141342031864413091)
        ·
          refine ⟨101393766212013047796619637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67595844141342031864413091 101393766212013047796619637)
          ·
            refine ⟨9505665582376223230933091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101393766212013047796619637 9505665582376223230933091)
            ·
              refine ⟨14258498373564334846399637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9505665582376223230933091 14258498373564334846399637)
              ·
                refine ⟨668367111260828195924983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14258498373564334846399637 668367111260828195924983)
                ·
                  refine ⟨1002550666891242293887475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668367111260828195924983 1002550666891242293887475)
                  ·
                    refine ⟨1503826000336863440831213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1002550666891242293887475 1503826000336863440831213)
                    ·
                      refine ⟨563934750126323790311705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1503826000336863440831213 563934750126323790311705)
                      ·
                        rfl

theorem cell23_1098259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 1, 3].length) (baseStart_1098259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098259 prefixEnd_1098259 := by exact prefixLift 1098259
  have htrace : WordTrace (prefixWord ++ tailWord_1098259) baseStart_1098259 baseEnd_1098259 := by
    simpa [prefixWord, tailWord_1098259, baseEnd_1098259] using wordTrace_append hprefix tailTrace_1098259
  have hstable : (prefixWord ++ tailWord_1098259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098259).length < 2 ^ (prefixWord ++ tailWord_1098259).sum := by decide
  have hdescent : baseEnd_1098259 < baseStart_1098259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098295 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1098295 : Nat := 118140960795 + 1098295 * 2 ^ 59
def prefixEnd_1098295 : Nat := 4983230072969 + 3 ^ 40 * 1098295 * 2
def baseEnd_1098295 : Nat := 563953235429885649461539

theorem tailTrace_1098295 : CollatzResearch.WordTrace tailWord_1098295 prefixEnd_1098295 563953235429885649461539 := by
  unfold tailWord_1098295
  simp only [CollatzResearch.WordTrace]
  refine ⟨40058109556072263697592339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26705406370714842465061559 40058109556072263697592339)
  ·
    refine ⟨60087164334108395546388509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40058109556072263697592339 60087164334108395546388509)
    ·
      refine ⟨22532686625290648329895691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60087164334108395546388509 22532686625290648329895691)
      ·
        refine ⟨33799029937935972494843537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22532686625290648329895691 33799029937935972494843537)
        ·
          refine ⟨25349272453451979371132653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33799029937935972494843537 25349272453451979371132653)
          ·
            refine ⟨9505977170044492264174745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25349272453451979371132653 9505977170044492264174745)
            ·
              refine ⟨7129482877533369198131059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9505977170044492264174745 7129482877533369198131059)
              ·
                refine ⟨10694224316300053797196589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129482877533369198131059 10694224316300053797196589)
                ·
                  refine ⟨4010334118612520173948721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10694224316300053797196589 4010334118612520173948721)
                  ·
                    refine ⟨3007750588959390130461541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4010334118612520173948721 3007750588959390130461541)
                    ·
                      refine ⟨563953235429885649461539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3007750588959390130461541 563953235429885649461539)
                      ·
                        rfl

theorem cell23_1098295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1098295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098295 prefixEnd_1098295 := by exact prefixLift 1098295
  have htrace : WordTrace (prefixWord ++ tailWord_1098295) baseStart_1098295 baseEnd_1098295 := by
    simpa [prefixWord, tailWord_1098295, baseEnd_1098295] using wordTrace_append hprefix tailTrace_1098295
  have hstable : (prefixWord ++ tailWord_1098295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098295).length < 2 ^ (prefixWord ++ tailWord_1098295).sum := by decide
  have hdescent : baseEnd_1098295 < baseStart_1098295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098305 : List Nat := [1, 2, 5, 1, 1, 2, 11]
def baseStart_1098305 : Nat := 118140960795 + 1098305 * 2 ^ 59
def prefixEnd_1098305 : Nat := 4983230072969 + 3 ^ 40 * 1098305 * 2
def baseEnd_1098305 : Nat := 6962449015264575436253

theorem tailTrace_1098305 : CollatzResearch.WordTrace tailWord_1098305 prefixEnd_1098305 6962449015264575436253 := by
  unfold tailWord_1098305
  simp only [CollatzResearch.WordTrace]
  refine ⟨40058474286036035405456369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26705649524024023603637579 40058474286036035405456369)
  ·
    refine ⟨30043855714527026554092277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40058474286036035405456369 30043855714527026554092277)
    ·
      refine ⟨2816611473236908739446151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30043855714527026554092277 2816611473236908739446151)
      ·
        refine ⟨4224917209855363109169227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2816611473236908739446151 4224917209855363109169227)
        ·
          refine ⟨6337375814783044663753841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224917209855363109169227 6337375814783044663753841)
          ·
            refine ⟨4753031861087283497815381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6337375814783044663753841 4753031861087283497815381)
            ·
              refine ⟨6962449015264575436253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4753031861087283497815381 6962449015264575436253)
              ·
                rfl

theorem cell23_1098305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 11].length) (baseStart_1098305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098305 prefixEnd_1098305 := by exact prefixLift 1098305
  have htrace : WordTrace (prefixWord ++ tailWord_1098305) baseStart_1098305 baseEnd_1098305 := by
    simpa [prefixWord, tailWord_1098305, baseEnd_1098305] using wordTrace_append hprefix tailTrace_1098305
  have hstable : (prefixWord ++ tailWord_1098305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098305).length < 2 ^ (prefixWord ++ tailWord_1098305).sum := by decide
  have hdescent : baseEnd_1098305 < baseStart_1098305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098349 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1098349 : Nat := 118140960795 + 1098349 * 2 ^ 59
def prefixEnd_1098349 : Nat := 4983230072969 + 3 ^ 40 * 1098349 * 2
def baseEnd_1098349 : Nat := 563980963385228438186291

theorem tailTrace_1098349 : CollatzResearch.WordTrace tailWord_1098349 prefixEnd_1098349 563980963385228438186291 := by
  unfold tailWord_1098349
  simp only [CollatzResearch.WordTrace]
  refine ⟨40060079097876630920058101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26706719398584420613372067 40060079097876630920058101)
  ·
    refine ⟨3755632415425934148755447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40060079097876630920058101 3755632415425934148755447)
    ·
      refine ⟨5633448623138901223133171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3755632415425934148755447 5633448623138901223133171)
      ·
        refine ⟨8450172934708351834699757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5633448623138901223133171 8450172934708351834699757)
        ·
          refine ⟨3168814850515631938012409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8450172934708351834699757 3168814850515631938012409)
          ·
            refine ⟨2376611137886723953509307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3168814850515631938012409 2376611137886723953509307)
            ·
              refine ⟨3564916706830085930263961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376611137886723953509307 3564916706830085930263961)
              ·
                refine ⟨2673687530122564447697971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564916706830085930263961 2673687530122564447697971)
                ·
                  refine ⟨4010531295183846671546957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673687530122564447697971 4010531295183846671546957)
                  ·
                    refine ⟨1503949235693942501830109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4010531295183846671546957 1503949235693942501830109)
                    ·
                      refine ⟨563980963385228438186291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1503949235693942501830109 563980963385228438186291)
                      ·
                        rfl

theorem cell23_1098349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1098349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098349 prefixEnd_1098349 := by exact prefixLift 1098349
  have htrace : WordTrace (prefixWord ++ tailWord_1098349) baseStart_1098349 baseEnd_1098349 := by
    simpa [prefixWord, tailWord_1098349, baseEnd_1098349] using wordTrace_append hprefix tailTrace_1098349
  have hstable : (prefixWord ++ tailWord_1098349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098349).length < 2 ^ (prefixWord ++ tailWord_1098349).sum := by decide
  have hdescent : baseEnd_1098349 < baseStart_1098349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098359 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 1, 3, 2]
def baseStart_1098359 : Nat := 118140960795 + 1098359 * 2 ^ 59
def prefixEnd_1098359 : Nat := 4983230072969 + 3 ^ 40 * 1098359 * 2
def baseEnd_1098359 : Nat := 563986098191773399061245

theorem tailTrace_1098359 : CollatzResearch.WordTrace tailWord_1098359 prefixEnd_1098359 563986098191773399061245 := by
  unfold tailWord_1098359
  simp only [CollatzResearch.WordTrace]
  refine ⟨40060443827840402627922131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26706962551893601751948087 40060443827840402627922131)
  ·
    refine ⟨60090665741760603941883197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40060443827840402627922131 60090665741760603941883197)
    ·
      refine ⟨22533999653160226478206199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60090665741760603941883197 22533999653160226478206199)
      ·
        refine ⟨33800999479740339717309299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22533999653160226478206199 33800999479740339717309299)
        ·
          refine ⟨50701499219610509575963949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33800999479740339717309299 50701499219610509575963949)
          ·
            refine ⟨19013062207353941090986481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50701499219610509575963949 19013062207353941090986481)
            ·
              refine ⟨14259796655515455818239861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19013062207353941090986481 14259796655515455818239861)
              ·
                refine ⟨1336855936454573982959987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14259796655515455818239861 1336855936454573982959987)
                ·
                  refine ⟨2005283904681860974439981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336855936454573982959987 2005283904681860974439981)
                  ·
                    refine ⟨751981464255697865414993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005283904681860974439981 751981464255697865414993)
                    ·
                      refine ⟨563986098191773399061245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 751981464255697865414993 563986098191773399061245)
                      ·
                        rfl

theorem cell23_1098359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 3, 2].length) (baseStart_1098359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098359 prefixEnd_1098359 := by exact prefixLift 1098359
  have htrace : WordTrace (prefixWord ++ tailWord_1098359) baseStart_1098359 baseEnd_1098359 := by
    simpa [prefixWord, tailWord_1098359, baseEnd_1098359] using wordTrace_append hprefix tailTrace_1098359
  have hstable : (prefixWord ++ tailWord_1098359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098359).length < 2 ^ (prefixWord ++ tailWord_1098359).sum := by decide
  have hdescent : baseEnd_1098359 < baseStart_1098359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098372 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1098372 : Nat := 118140960795 + 1098372 * 2 ^ 59
def prefixEnd_1098372 : Nat := 4983230072969 + 3 ^ 40 * 1098372 * 2
def baseEnd_1098372 : Nat := 563992773440281848198685

theorem tailTrace_1098372 : CollatzResearch.WordTrace tailWord_1098372 prefixEnd_1098372 563992773440281848198685 := by
  unfold tailWord_1098372
  simp only [CollatzResearch.WordTrace]
  refine ⟨20030458988396652924072685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26707278651195537232096913 20030458988396652924072685)
  ·
    refine ⟨7511422120648744846527257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20030458988396652924072685 7511422120648744846527257)
    ·
      refine ⟨5633566590486558634895443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7511422120648744846527257 5633566590486558634895443)
      ·
        refine ⟨8450349885729837952343165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5633566590486558634895443 8450349885729837952343165)
        ·
          refine ⟨3168881207148689232128687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8450349885729837952343165 3168881207148689232128687)
          ·
            refine ⟨4753321810723033848193031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168881207148689232128687 4753321810723033848193031)
            ·
              refine ⟨7129982716084550772289547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753321810723033848193031 7129982716084550772289547)
              ·
                refine ⟨10694974074126826158434321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129982716084550772289547 10694974074126826158434321)
                ·
                  refine ⟨8021230555595119618825741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10694974074126826158434321 8021230555595119618825741)
                  ·
                    refine ⟨3007961458348169857059653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8021230555595119618825741 3007961458348169857059653)
                    ·
                      refine ⟨563992773440281848198685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3007961458348169857059653 563992773440281848198685)
                      ·
                        rfl

theorem cell23_1098372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1098372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098372 prefixEnd_1098372 := by exact prefixLift 1098372
  have htrace : WordTrace (prefixWord ++ tailWord_1098372) baseStart_1098372 baseEnd_1098372 := by
    simpa [prefixWord, tailWord_1098372, baseEnd_1098372] using wordTrace_append hprefix tailTrace_1098372
  have hstable : (prefixWord ++ tailWord_1098372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098372).length < 2 ^ (prefixWord ++ tailWord_1098372).sum := by decide
  have hdescent : baseEnd_1098372 < baseStart_1098372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098382 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1098382 : Nat := 118140960795 + 1098382 * 2 ^ 59
def prefixEnd_1098382 : Nat := 4983230072969 + 3 ^ 40 * 1098382 * 2
def baseEnd_1098382 : Nat := 187999302748942269691213

theorem tailTrace_1098382 : CollatzResearch.WordTrace tailWord_1098382 prefixEnd_1098382 187999302748942269691213 := by
  unfold tailWord_1098382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007660338344634694501175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26707521804504718370672933 5007660338344634694501175)
  ·
    refine ⟨7511490507516952041751763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5007660338344634694501175 7511490507516952041751763)
    ·
      refine ⟨11267235761275428062627645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7511490507516952041751763 11267235761275428062627645)
      ·
        refine ⟨4225213410478285523485367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11267235761275428062627645 4225213410478285523485367)
        ·
          refine ⟨6337820115717428285228051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225213410478285523485367 6337820115717428285228051)
          ·
            refine ⟨9506730173576142427842077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6337820115717428285228051 9506730173576142427842077)
            ·
              refine ⟨3565023815091053410440779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9506730173576142427842077 3565023815091053410440779)
              ·
                refine ⟨5347535722636580115661169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565023815091053410440779 5347535722636580115661169)
                ·
                  refine ⟨4010651791977435086745877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5347535722636580115661169 4010651791977435086745877)
                  ·
                    refine ⟨187999302748942269691213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4010651791977435086745877 187999302748942269691213)
                    ·
                      rfl

theorem cell23_1098382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1098382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098382 prefixEnd_1098382 := by exact prefixLift 1098382
  have htrace : WordTrace (prefixWord ++ tailWord_1098382) baseStart_1098382 baseEnd_1098382 := by
    simpa [prefixWord, tailWord_1098382, baseEnd_1098382] using wordTrace_append hprefix tailTrace_1098382
  have hstable : (prefixWord ++ tailWord_1098382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098382).length < 2 ^ (prefixWord ++ tailWord_1098382).sum := by decide
  have hdescent : baseEnd_1098382 < baseStart_1098382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098389 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_1098389 : Nat := 118140960795 + 1098389 * 2 ^ 59
def prefixEnd_1098389 : Nat := 4983230072969 + 3 ^ 40 * 1098389 * 2
def baseEnd_1098389 : Nat := 564001502611408281686107

theorem tailTrace_1098389 : CollatzResearch.WordTrace tailWord_1098389 prefixEnd_1098389 564001502611408281686107 := by
  unfold tailWord_1098389
  simp only [CollatzResearch.WordTrace]
  refine ⟨40061538017731717751514221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26707692011821145167676147 40061538017731717751514221)
  ·
    refine ⟨15023076756649394156817833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40061538017731717751514221 15023076756649394156817833)
    ·
      refine ⟨11267307567487045617613375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15023076756649394156817833 11267307567487045617613375)
      ·
        refine ⟨16900961351230568426420063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11267307567487045617613375 16900961351230568426420063)
        ·
          refine ⟨25351442026845852639630095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16900961351230568426420063 25351442026845852639630095)
          ·
            refine ⟨38027163040268778959445143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25351442026845852639630095 38027163040268778959445143)
            ·
              refine ⟨57040744560403168439167715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38027163040268778959445143 57040744560403168439167715)
              ·
                refine ⟨85561116840604752658751573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57040744560403168439167715 85561116840604752658751573)
                ·
                  refine ⟨1002669337975836945219745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 85561116840604752658751573 1002669337975836945219745)
                  ·
                    refine ⟨752002003481877708914809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1002669337975836945219745 752002003481877708914809)
                    ·
                      refine ⟨564001502611408281686107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752002003481877708914809 564001502611408281686107)
                      ·
                        rfl

theorem cell23_1098389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_1098389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098389 prefixEnd_1098389 := by exact prefixLift 1098389
  have htrace : WordTrace (prefixWord ++ tailWord_1098389) baseStart_1098389 baseEnd_1098389 := by
    simpa [prefixWord, tailWord_1098389, baseEnd_1098389] using wordTrace_append hprefix tailTrace_1098389
  have hstable : (prefixWord ++ tailWord_1098389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098389).length < 2 ^ (prefixWord ++ tailWord_1098389).sum := by decide
  have hdescent : baseEnd_1098389 < baseStart_1098389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098392 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1098392 : Nat := 118140960795 + 1098392 * 2 ^ 59
def prefixEnd_1098392 : Nat := 4983230072969 + 3 ^ 40 * 1098392 * 2
def baseEnd_1098392 : Nat := 564003043053371769948593

theorem tailTrace_1098392 : CollatzResearch.WordTrace tailWord_1098392 prefixEnd_1098392 564003043053371769948593 := by
  unfold tailWord_1098392
  simp only [CollatzResearch.WordTrace]
  refine ⟨20030823718360424631936715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26707764957813899509248953 20030823718360424631936715)
  ·
    refine ⟨30046235577540636947905073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20030823718360424631936715 30046235577540636947905073)
    ·
      refine ⟨22534676683155477710928805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30046235577540636947905073 22534676683155477710928805)
      ·
        refine ⟨4225251878091652070799151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22534676683155477710928805 4225251878091652070799151)
        ·
          refine ⟨6337877817137478106198727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225251878091652070799151 6337877817137478106198727)
          ·
            refine ⟨9506816725706217159298091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6337877817137478106198727 9506816725706217159298091)
            ·
              refine ⟨14260225088559325738947137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9506816725706217159298091 14260225088559325738947137)
              ·
                refine ⟨10695168816419494304210353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14260225088559325738947137 10695168816419494304210353)
                ·
                  refine ⟨8021376612314620728157765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10695168816419494304210353 8021376612314620728157765)
                  ·
                    refine ⟨1504008114808991386529581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8021376612314620728157765 1504008114808991386529581)
                    ·
                      refine ⟨564003043053371769948593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1504008114808991386529581 564003043053371769948593)
                      ·
                        rfl

theorem cell23_1098392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1098392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098392 prefixEnd_1098392 := by exact prefixLift 1098392
  have htrace : WordTrace (prefixWord ++ tailWord_1098392) baseStart_1098392 baseEnd_1098392 := by
    simpa [prefixWord, tailWord_1098392, baseEnd_1098392] using wordTrace_append hprefix tailTrace_1098392
  have hstable : (prefixWord ++ tailWord_1098392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098392).length < 2 ^ (prefixWord ++ tailWord_1098392).sum := by decide
  have hdescent : baseEnd_1098392 < baseStart_1098392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098405 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1098405 : Nat := 118140960795 + 1098405 * 2 ^ 59
def prefixEnd_1098405 : Nat := 4983230072969 + 3 ^ 40 * 1098405 * 2
def baseEnd_1098405 : Nat := 564009718301880219086033

theorem tailTrace_1098405 : CollatzResearch.WordTrace tailWord_1098405 prefixEnd_1098405 564009718301880219086033 := by
  unfold tailWord_1098405
  simp only [CollatzResearch.WordTrace]
  refine ⟨40062121585673752484096669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26708081057115834989397779 40062121585673752484096669)
  ·
    refine ⟨15023295594627657181536251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40062121585673752484096669 15023295594627657181536251)
    ·
      refine ⟨22534943391941485772304377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15023295594627657181536251 22534943391941485772304377)
      ·
        refine ⟨16901207543956114329228283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22534943391941485772304377 16901207543956114329228283)
        ·
          refine ⟨25351811315934171493842425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16901207543956114329228283 25351811315934171493842425)
          ·
            refine ⟨19013858486950628620381819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25351811315934171493842425 19013858486950628620381819)
            ·
              refine ⟨28520787730425942930572729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19013858486950628620381819 28520787730425942930572729)
              ·
                refine ⟨21390590797819457197929547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28520787730425942930572729 21390590797819457197929547)
                ·
                  refine ⟨32085886196729185796894321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21390590797819457197929547 32085886196729185796894321)
                  ·
                    refine ⟨24064414647546889347670741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32085886196729185796894321 24064414647546889347670741)
                    ·
                      refine ⟨564009718301880219086033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24064414647546889347670741 564009718301880219086033)
                      ·
                        rfl

theorem cell23_1098405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1098405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098405 prefixEnd_1098405 := by exact prefixLift 1098405
  have htrace : WordTrace (prefixWord ++ tailWord_1098405) baseStart_1098405 baseEnd_1098405 := by
    simpa [prefixWord, tailWord_1098405, baseEnd_1098405] using wordTrace_append hprefix tailTrace_1098405
  have hstable : (prefixWord ++ tailWord_1098405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098405).length < 2 ^ (prefixWord ++ tailWord_1098405).sum := by decide
  have hdescent : baseEnd_1098405 < baseStart_1098405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098410 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1098410 : Nat := 118140960795 + 1098410 * 2 ^ 59
def prefixEnd_1098410 : Nat := 4983230072969 + 3 ^ 40 * 1098410 * 2
def baseEnd_1098410 : Nat := 564012285705152699523511

theorem tailTrace_1098410 : CollatzResearch.WordTrace tailWord_1098410 prefixEnd_1098410 564012285705152699523511 := by
  unfold tailWord_1098410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015575987663909584507171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26708202633770425558685789 10015575987663909584507171)
  ·
    refine ⟨15023363981495864376760757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10015575987663909584507171 15023363981495864376760757)
    ·
      refine ⟨1408440373265237285321321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15023363981495864376760757 1408440373265237285321321)
      ·
        refine ⟨1056330279948927963990991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1408440373265237285321321 1056330279948927963990991)
        ·
          refine ⟨1584495419923391945986487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056330279948927963990991 1584495419923391945986487)
          ·
            refine ⟨2376743129885087918979731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584495419923391945986487 2376743129885087918979731)
            ·
              refine ⟨3565114694827631878469597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376743129885087918979731 3565114694827631878469597)
              ·
                refine ⟨1336918010560361954426099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3565114694827631878469597 1336918010560361954426099)
                ·
                  refine ⟨2005377015840542931639149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336918010560361954426099 2005377015840542931639149)
                  ·
                    refine ⟨752016380940203599364681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005377015840542931639149 752016380940203599364681)
                    ·
                      refine ⟨564012285705152699523511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752016380940203599364681 564012285705152699523511)
                      ·
                        rfl

theorem cell23_1098410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1098410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098410 prefixEnd_1098410 := by exact prefixLift 1098410
  have htrace : WordTrace (prefixWord ++ tailWord_1098410) baseStart_1098410 baseEnd_1098410 := by
    simpa [prefixWord, tailWord_1098410, baseEnd_1098410] using wordTrace_append hprefix tailTrace_1098410
  have hstable : (prefixWord ++ tailWord_1098410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098410).length < 2 ^ (prefixWord ++ tailWord_1098410).sum := by decide
  have hdescent : baseEnd_1098410 < baseStart_1098410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098429 : List Nat := [1, 4, 1, 2, 1, 3, 2, 4, 5]
def baseStart_1098429 : Nat := 118140960795 + 1098429 * 2 ^ 59
def prefixEnd_1098429 : Nat := 4983230072969 + 3 ^ 40 * 1098429 * 2
def baseEnd_1098429 : Nat := 62669115759732013909547

theorem tailTrace_1098429 : CollatzResearch.WordTrace tailWord_1098429 prefixEnd_1098429 62669115759732013909547 := by
  unfold tailWord_1098429
  simp only [CollatzResearch.WordTrace]
  refine ⟨40062996937586804582970341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26708664625057869721980227 40062996937586804582970341)
  ·
    refine ⟨7511811925797525859306939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40062996937586804582970341 7511811925797525859306939)
    ·
      refine ⟨11267717888696288788960409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7511811925797525859306939 11267717888696288788960409)
      ·
        refine ⟨8450788416522216591720307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11267717888696288788960409 8450788416522216591720307)
        ·
          refine ⟨12676182624783324887580461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8450788416522216591720307 12676182624783324887580461)
          ·
            refine ⟨4753568484293746832842673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12676182624783324887580461 4753568484293746832842673)
            ·
              refine ⟨3565176363220310124632005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4753568484293746832842673 3565176363220310124632005)
              ·
                refine ⟨668470568103808148368501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3565176363220310124632005 668470568103808148368501)
                ·
                  refine ⟨62669115759732013909547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 668470568103808148368501 62669115759732013909547)
                  ·
                    rfl

theorem cell23_1098429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_1098429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098429 prefixEnd_1098429 := by exact prefixLift 1098429
  have htrace : WordTrace (prefixWord ++ tailWord_1098429) baseStart_1098429 baseEnd_1098429 := by
    simpa [prefixWord, tailWord_1098429, baseEnd_1098429] using wordTrace_append hprefix tailTrace_1098429
  have hstable : (prefixWord ++ tailWord_1098429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098429).length < 2 ^ (prefixWord ++ tailWord_1098429).sum := by decide
  have hdescent : baseEnd_1098429 < baseStart_1098429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098442 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_1098442 : Nat := 118140960795 + 1098442 * 2 ^ 59
def prefixEnd_1098442 : Nat := 4983230072969 + 3 ^ 40 * 1098442 * 2
def baseEnd_1098442 : Nat := 188009572362032191441121

theorem tailTrace_1098442 : CollatzResearch.WordTrace tailWord_1098442 prefixEnd_1098442 188009572362032191441121 := by
  unfold tailWord_1098442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015867771634926950798395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26708980724359805202129053 10015867771634926950798395)
  ·
    refine ⟨15023801657452390426197593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10015867771634926950798395 15023801657452390426197593)
    ·
      refine ⟨11267851243089292819648195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15023801657452390426197593 11267851243089292819648195)
      ·
        refine ⟨16901776864633939229472293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11267851243089292819648195 16901776864633939229472293)
        ·
          refine ⟨3169083162118863605526055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16901776864633939229472293 3169083162118863605526055)
          ·
            refine ⟨4753624743178295408289083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169083162118863605526055 4753624743178295408289083)
            ·
              refine ⟨7130437114767443112433625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753624743178295408289083 7130437114767443112433625)
              ·
                refine ⟨5347827836075582334325219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7130437114767443112433625 5347827836075582334325219)
                ·
                  refine ⟨8021741754113373501487829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5347827836075582334325219 8021741754113373501487829)
                  ·
                    refine ⟨188009572362032191441121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8021741754113373501487829 188009572362032191441121)
                    ·
                      rfl

theorem cell23_1098442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_1098442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098442 prefixEnd_1098442 := by exact prefixLift 1098442
  have htrace : WordTrace (prefixWord ++ tailWord_1098442) baseStart_1098442 baseEnd_1098442 := by
    simpa [prefixWord, tailWord_1098442, baseEnd_1098442] using wordTrace_append hprefix tailTrace_1098442
  have hstable : (prefixWord ++ tailWord_1098442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098442).length < 2 ^ (prefixWord ++ tailWord_1098442).sum := by decide
  have hdescent : baseEnd_1098442 < baseStart_1098442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098479 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_1098479 : Nat := 118140960795 + 1098479 * 2 ^ 59
def prefixEnd_1098479 : Nat := 4983230072969 + 3 ^ 40 * 1098479 * 2
def baseEnd_1098479 : Nat := 564047715870312929560693

theorem tailTrace_1098479 : CollatzResearch.WordTrace tailWord_1098479 prefixEnd_1098479 564047715870312929560693 := by
  unfold tailWord_1098479
  simp only [CollatzResearch.WordTrace]
  refine ⟨40064820587405663122290491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26709880391603775414860327 40064820587405663122290491)
  ·
    refine ⟨60097230881108494683435737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40064820587405663122290491 60097230881108494683435737)
    ·
      refine ⟨45072923160831371012576803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60097230881108494683435737 45072923160831371012576803)
      ·
        refine ⟨67609384741247056518865205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45072923160831371012576803 67609384741247056518865205)
        ·
          refine ⟨6338379819491911548643613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67609384741247056518865205 6338379819491911548643613)
          ·
            refine ⟨2376892432309466830741355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6338379819491911548643613 2376892432309466830741355)
            ·
              refine ⟨3565338648464200246112033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376892432309466830741355 3565338648464200246112033)
              ·
                refine ⟨2674003986348150184584025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3565338648464200246112033 2674003986348150184584025)
                ·
                  refine ⟨2005502989761112638438019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2674003986348150184584025 2005502989761112638438019)
                  ·
                    refine ⟨3008254484641668957657029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005502989761112638438019 3008254484641668957657029)
                    ·
                      refine ⟨564047715870312929560693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3008254484641668957657029 564047715870312929560693)
                      ·
                        rfl

theorem cell23_1098479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_1098479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098479 prefixEnd_1098479 := by exact prefixLift 1098479
  have htrace : WordTrace (prefixWord ++ tailWord_1098479) baseStart_1098479 baseEnd_1098479 := by
    simpa [prefixWord, tailWord_1098479, baseEnd_1098479] using wordTrace_append hprefix tailTrace_1098479
  have hstable : (prefixWord ++ tailWord_1098479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098479).length < 2 ^ (prefixWord ++ tailWord_1098479).sum := by decide
  have hdescent : baseEnd_1098479 < baseStart_1098479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098546 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_1098546 : Nat := 118140960795 + 1098546 * 2 ^ 59
def prefixEnd_1098546 : Nat := 4983230072969 + 3 ^ 40 * 1098546 * 2
def baseEnd_1098546 : Nat := 564082119074164167422885

theorem tailTrace_1098546 : CollatzResearch.WordTrace tailWord_1098546 prefixEnd_1098546 564082119074164167422885 := by
  unfold tailWord_1098546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10016816069540733391244873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26711509518775289043319661 10016816069540733391244873)
  ·
    refine ⟨7512612052155550043433655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10016816069540733391244873 7512612052155550043433655)
    ·
      refine ⟨11268918078233325065150483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7512612052155550043433655 11268918078233325065150483)
      ·
        refine ⟨16903377117349987597725725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11268918078233325065150483 16903377117349987597725725)
        ·
          refine ⟨6338766419006245349147147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16903377117349987597725725 6338766419006245349147147)
          ·
            refine ⟨9508149628509368023720721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338766419006245349147147 9508149628509368023720721)
            ·
              refine ⟨7131112221382026017790541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9508149628509368023720721 7131112221382026017790541)
              ·
                refine ⟨2674167083018259756671453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7131112221382026017790541 2674167083018259756671453)
                ·
                  refine ⟨1002812656131847408751795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2674167083018259756671453 1002812656131847408751795)
                  ·
                    refine ⟨1504218984197771113127693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1002812656131847408751795 1504218984197771113127693)
                    ·
                      refine ⟨564082119074164167422885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1504218984197771113127693 564082119074164167422885)
                      ·
                        rfl

theorem cell23_1098546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_1098546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098546 prefixEnd_1098546 := by exact prefixLift 1098546
  have htrace : WordTrace (prefixWord ++ tailWord_1098546) baseStart_1098546 baseEnd_1098546 := by
    simpa [prefixWord, tailWord_1098546, baseEnd_1098546] using wordTrace_append hprefix tailTrace_1098546
  have hstable : (prefixWord ++ tailWord_1098546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098546).length < 2 ^ (prefixWord ++ tailWord_1098546).sum := by decide
  have hdescent : baseEnd_1098546 < baseStart_1098546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098549 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1098549 : Nat := 118140960795 + 1098549 * 2 ^ 59
def prefixEnd_1098549 : Nat := 4983230072969 + 3 ^ 40 * 1098549 * 2
def baseEnd_1098549 : Nat := 188027886505375885228457

theorem tailTrace_1098549 : CollatzResearch.WordTrace tailWord_1098549 prefixEnd_1098549 188027886505375885228457 := by
  unfold tailWord_1098549
  simp only [CollatzResearch.WordTrace]
  refine ⟨40067373697152065077338701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26711582464768043384892467 40067373697152065077338701)
  ·
    refine ⟨15025265136432024404002013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40067373697152065077338701 15025265136432024404002013)
    ·
      refine ⟨5634474426162009151500755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15025265136432024404002013 5634474426162009151500755)
      ·
        refine ⟨8451711639243013727251133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5634474426162009151500755 8451711639243013727251133)
        ·
          refine ⟨3169391864716130147719175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8451711639243013727251133 3169391864716130147719175)
          ·
            refine ⟨4754087797074195221578763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169391864716130147719175 4754087797074195221578763)
            ·
              refine ⟨7131131695611292832368145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754087797074195221578763 7131131695611292832368145)
              ·
                refine ⟨5348348771708469624276109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7131131695611292832368145 5348348771708469624276109)
                ·
                  refine ⟨2005630789390676109103541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5348348771708469624276109 2005630789390676109103541)
                  ·
                    refine ⟨188027886505375885228457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2005630789390676109103541 188027886505375885228457)
                    ·
                      rfl

theorem cell23_1098549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1098549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098549 prefixEnd_1098549 := by exact prefixLift 1098549
  have htrace : WordTrace (prefixWord ++ tailWord_1098549) baseStart_1098549 baseEnd_1098549 := by
    simpa [prefixWord, tailWord_1098549, baseEnd_1098549] using wordTrace_append hprefix tailTrace_1098549
  have hstable : (prefixWord ++ tailWord_1098549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098549).length < 2 ^ (prefixWord ++ tailWord_1098549).sum := by decide
  have hdescent : baseEnd_1098549 < baseStart_1098549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098569 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_1098569 : Nat := 118140960795 + 1098569 * 2 ^ 59
def prefixEnd_1098569 : Nat := 4983230072969 + 3 ^ 40 * 1098569 * 2
def baseEnd_1098569 : Nat := 564093929129217577435279

theorem tailTrace_1098569 : CollatzResearch.WordTrace tailWord_1098569 prefixEnd_1098569 564093929129217577435279 := by
  unfold tailWord_1098569
  simp only [CollatzResearch.WordTrace]
  refine ⟨40068103157079608493066761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26712068771386405662044507 40068103157079608493066761)
  ·
    refine ⟨30051077367809706369800071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40068103157079608493066761 30051077367809706369800071)
    ·
      refine ⟨45076616051714559554700107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30051077367809706369800071 45076616051714559554700107)
      ·
        refine ⟨67614924077571839332050161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45076616051714559554700107 67614924077571839332050161)
        ·
          refine ⟨50711193058178879499037621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67614924077571839332050161 50711193058178879499037621)
          ·
            refine ⟨4754174349204269953034777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50711193058178879499037621 4754174349204269953034777)
            ·
              refine ⟨3565630761903202464776083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4754174349204269953034777 3565630761903202464776083)
              ·
                refine ⟨5348446142854803697164125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565630761903202464776083 5348446142854803697164125)
                ·
                  refine ⟨2005667303570551386436547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5348446142854803697164125 2005667303570551386436547)
                  ·
                    refine ⟨3008500955355827079654821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005667303570551386436547 3008500955355827079654821)
                    ·
                      refine ⟨564093929129217577435279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3008500955355827079654821 564093929129217577435279)
                      ·
                        rfl

theorem cell23_1098569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_1098569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098569 prefixEnd_1098569 := by exact prefixLift 1098569
  have htrace : WordTrace (prefixWord ++ tailWord_1098569) baseStart_1098569 baseEnd_1098569 := by
    simpa [prefixWord, tailWord_1098569, baseEnd_1098569] using wordTrace_append hprefix tailTrace_1098569
  have hstable : (prefixWord ++ tailWord_1098569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098569).length < 2 ^ (prefixWord ++ tailWord_1098569).sum := by decide
  have hdescent : baseEnd_1098569 < baseStart_1098569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098583 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 1, 5]
def baseStart_1098583 : Nat := 118140960795 + 1098583 * 2 ^ 59
def prefixEnd_1098583 : Nat := 4983230072969 + 3 ^ 40 * 1098583 * 2
def baseEnd_1098583 : Nat := 188033705952793507553405

theorem tailTrace_1098583 : CollatzResearch.WordTrace tailWord_1098583 prefixEnd_1098583 188033705952793507553405 := by
  unfold tailWord_1098583
  simp only [CollatzResearch.WordTrace]
  refine ⟨40068613779028888884076403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26712409186019259256050935 40068613779028888884076403)
  ·
    refine ⟨60102920668543333326114605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40068613779028888884076403 60102920668543333326114605)
    ·
      refine ⟨22538595250703749997292977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60102920668543333326114605 22538595250703749997292977)
      ·
        refine ⟨16903946438027812497969733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22538595250703749997292977 16903946438027812497969733)
        ·
          refine ⟨3169489957130214843369325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16903946438027812497969733 3169489957130214843369325)
          ·
            refine ⟨1188558733923830566263497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3169489957130214843369325 1188558733923830566263497)
            ·
              refine ⟨891419050442872924697623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188558733923830566263497 891419050442872924697623)
              ·
                refine ⟨1337128575664309387046435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891419050442872924697623 1337128575664309387046435)
                ·
                  refine ⟨2005692863496464080569653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337128575664309387046435 2005692863496464080569653)
                  ·
                    refine ⟨188033705952793507553405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2005692863496464080569653 188033705952793507553405)
                    ·
                      rfl

theorem cell23_1098583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_1098583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098583 prefixEnd_1098583 := by exact prefixLift 1098583
  have htrace : WordTrace (prefixWord ++ tailWord_1098583) baseStart_1098583 baseEnd_1098583 := by
    simpa [prefixWord, tailWord_1098583, baseEnd_1098583] using wordTrace_append hprefix tailTrace_1098583
  have hstable : (prefixWord ++ tailWord_1098583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098583).length < 2 ^ (prefixWord ++ tailWord_1098583).sum := by decide
  have hdescent : baseEnd_1098583 < baseStart_1098583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098586 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_1098586 : Nat := 118140960795 + 1098586 * 2 ^ 59
def prefixEnd_1098586 : Nat := 4983230072969 + 3 ^ 40 * 1098586 * 2
def baseEnd_1098586 : Nat := 564102658300344010922701

theorem tailTrace_1098586 : CollatzResearch.WordTrace tailWord_1098586 prefixEnd_1098586 564102658300344010922701 := by
  unfold tailWord_1098586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017180799504505099108903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26712482132012013597623741 10017180799504505099108903)
  ·
    refine ⟨15025771199256757648663355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10017180799504505099108903 15025771199256757648663355)
    ·
      refine ⟨22538656798885136472995033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15025771199256757648663355 22538656798885136472995033)
      ·
        refine ⟨16903992599163852354746275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22538656798885136472995033 16903992599163852354746275)
        ·
          refine ⟨25355988898745778532119413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16903992599163852354746275 25355988898745778532119413)
          ·
            refine ⟨2377123959257416737386195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25355988898745778532119413 2377123959257416737386195)
            ·
              refine ⟨3565685938886125106079293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377123959257416737386195 3565685938886125106079293)
              ·
                refine ⟨1337132227082296914779735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3565685938886125106079293 1337132227082296914779735)
                ·
                  refine ⟨2005698340623445372169603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337132227082296914779735 2005698340623445372169603)
                  ·
                    refine ⟨3008547510935168058254405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005698340623445372169603 3008547510935168058254405)
                    ·
                      refine ⟨564102658300344010922701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3008547510935168058254405 564102658300344010922701)
                      ·
                        rfl

theorem cell23_1098586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_1098586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098586 prefixEnd_1098586 := by exact prefixLift 1098586
  have htrace : WordTrace (prefixWord ++ tailWord_1098586) baseStart_1098586 baseEnd_1098586 := by
    simpa [prefixWord, tailWord_1098586, baseEnd_1098586] using wordTrace_append hprefix tailTrace_1098586
  have hstable : (prefixWord ++ tailWord_1098586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098586).length < 2 ^ (prefixWord ++ tailWord_1098586).sum := by decide
  have hdescent : baseEnd_1098586 < baseStart_1098586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098592 : List Nat := [2, 1, 1, 3, 3, 1, 12]
def baseStart_1098592 : Nat := 118140960795 + 1098592 * 2 ^ 59
def prefixEnd_1098592 : Nat := 4983230072969 + 3 ^ 40 * 1098592 * 2
def baseEnd_1098592 : Nat := 6964268384990999845033

theorem tailTrace_1098592 : CollatzResearch.WordTrace tailWord_1098592 prefixEnd_1098592 6964268384990999845033 := by
  unfold tailWord_1098592
  simp only [CollatzResearch.WordTrace]
  refine ⟨20034471017998141710577015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26712628023997522280769353 20034471017998141710577015)
  ·
    refine ⟨30051706526997212565865523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20034471017998141710577015 30051706526997212565865523)
    ·
      refine ⟨45077559790495818848798285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30051706526997212565865523 45077559790495818848798285)
      ·
        refine ⟨16904084921435932068299357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45077559790495818848798285 16904084921435932068299357)
        ·
          refine ⟨6339031845538474525612259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16904084921435932068299357 6339031845538474525612259)
          ·
            refine ⟨9508547768307711788418389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6339031845538474525612259 9508547768307711788418389)
            ·
              refine ⟨6964268384990999845033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 9508547768307711788418389 6964268384990999845033)
              ·
                rfl

theorem cell23_1098592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 12].length) (baseStart_1098592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098592 prefixEnd_1098592 := by exact prefixLift 1098592
  have htrace : WordTrace (prefixWord ++ tailWord_1098592) baseStart_1098592 baseEnd_1098592 := by
    simpa [prefixWord, tailWord_1098592, baseEnd_1098592] using wordTrace_append hprefix tailTrace_1098592
  have hstable : (prefixWord ++ tailWord_1098592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098592).length < 2 ^ (prefixWord ++ tailWord_1098592).sum := by decide
  have hdescent : baseEnd_1098592 < baseStart_1098592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098596 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_1098596 : Nat := 118140960795 + 1098596 * 2 ^ 59
def prefixEnd_1098596 : Nat := 4983230072969 + 3 ^ 40 * 1098596 * 2
def baseEnd_1098596 : Nat := 188035931035629657265885

theorem tailTrace_1098596 : CollatzResearch.WordTrace tailWord_1098596 prefixEnd_1098596 188035931035629657265885 := by
  unfold tailWord_1098596
  simp only [CollatzResearch.WordTrace]
  refine ⟨20034543963990896052149821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26712725285321194736199761 20034543963990896052149821)
  ·
    refine ⟨7512953986496586019556183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20034543963990896052149821 7512953986496586019556183)
    ·
      refine ⟨11269430979744879029334275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7512953986496586019556183 11269430979744879029334275)
      ·
        refine ⟨16904146469617318544001413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11269430979744879029334275 16904146469617318544001413)
        ·
          refine ⟨3169527463053247227000265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16904146469617318544001413 3169527463053247227000265)
          ·
            refine ⟨2377145597289935420250199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3169527463053247227000265 2377145597289935420250199)
            ·
              refine ⟨3565718395934903130375299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377145597289935420250199 3565718395934903130375299)
              ·
                refine ⟨5348577593902354695562949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565718395934903130375299 5348577593902354695562949)
                ·
                  refine ⟨1002858298856691505418053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5348577593902354695562949 1002858298856691505418053)
                  ·
                    refine ⟨188035931035629657265885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1002858298856691505418053 188035931035629657265885)
                    ·
                      rfl

theorem cell23_1098596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_1098596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098596 prefixEnd_1098596 := by exact prefixLift 1098596
  have htrace : WordTrace (prefixWord ++ tailWord_1098596) baseStart_1098596 baseEnd_1098596 := by
    simpa [prefixWord, tailWord_1098596, baseEnd_1098596] using wordTrace_append hprefix tailTrace_1098596
  have hstable : (prefixWord ++ tailWord_1098596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098596).length < 2 ^ (prefixWord ++ tailWord_1098596).sum := by decide
  have hdescent : baseEnd_1098596 < baseStart_1098596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098636 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_1098636 : Nat := 118140960795 + 1098636 * 2 ^ 59
def prefixEnd_1098636 : Nat := 4983230072969 + 3 ^ 40 * 1098636 * 2
def baseEnd_1098636 : Nat := 564128332333068815297471

theorem tailTrace_1098636 : CollatzResearch.WordTrace tailWord_1098636 prefixEnd_1098636 564128332333068815297471 := by
  unfold tailWord_1098636
  simp only [CollatzResearch.WordTrace]
  refine ⟨20035273423918439467877881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26713697898557919290503841 20035273423918439467877881)
  ·
    refine ⟨15026455067938829600908411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20035273423918439467877881 15026455067938829600908411)
    ·
      refine ⟨22539682601908244401362617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15026455067938829600908411 22539682601908244401362617)
      ·
        refine ⟨16904761951431183301021963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22539682601908244401362617 16904761951431183301021963)
        ·
          refine ⟨25357142927146774951532945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16904761951431183301021963 25357142927146774951532945)
          ·
            refine ⟨19017857195360081213649709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25357142927146774951532945 19017857195360081213649709)
            ·
              refine ⟨7131696448260030455118641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19017857195360081213649709 7131696448260030455118641)
              ·
                refine ⟨5348772336195022841338981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7131696448260030455118641 5348772336195022841338981)
                ·
                  refine ⟨1002894813036566782751059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5348772336195022841338981 1002894813036566782751059)
                  ·
                    refine ⟨1504342219554850174126589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1002894813036566782751059 1504342219554850174126589)
                    ·
                      refine ⟨564128332333068815297471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1504342219554850174126589 564128332333068815297471)
                      ·
                        rfl

theorem cell23_1098636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_1098636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098636 prefixEnd_1098636 := by exact prefixLift 1098636
  have htrace : WordTrace (prefixWord ++ tailWord_1098636) baseStart_1098636 baseEnd_1098636 := by
    simpa [prefixWord, tailWord_1098636, baseEnd_1098636] using wordTrace_append hprefix tailTrace_1098636
  have hstable : (prefixWord ++ tailWord_1098636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098636).length < 2 ^ (prefixWord ++ tailWord_1098636).sum := by decide
  have hdescent : baseEnd_1098636 < baseStart_1098636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098653 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1098653 : Nat := 118140960795 + 1098653 * 2 ^ 59
def prefixEnd_1098653 : Nat := 4983230072969 + 3 ^ 40 * 1098653 * 2
def baseEnd_1098653 : Nat := 564137061504195248784893

theorem tailTrace_1098653 : CollatzResearch.WordTrace tailWord_1098653 prefixEnd_1098653 564137061504195248784893 := by
  unfold tailWord_1098653
  simp only [CollatzResearch.WordTrace]
  refine ⟨40071166888775290839124613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26714111259183527226083075 40071166888775290839124613)
  ·
    refine ⟨7513343791645367032335865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40071166888775290839124613 7513343791645367032335865)
    ·
      refine ⟨5635007843734025274251899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7513343791645367032335865 5635007843734025274251899)
      ·
        refine ⟨8452511765601037911377849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5635007843734025274251899 8452511765601037911377849)
        ·
          refine ⟨6339383824200778433533387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8452511765601037911377849 6339383824200778433533387)
          ·
            refine ⟨9509075736301167650300081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6339383824200778433533387 9509075736301167650300081)
            ·
              refine ⟨7131806802225875737725061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9509075736301167650300081 7131806802225875737725061)
              ·
                refine ⟨1337213775417351700823449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7131806802225875737725061 1337213775417351700823449)
                ·
                  refine ⟨1002910331563013775617587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1337213775417351700823449 1002910331563013775617587)
                  ·
                    refine ⟨1504365497344520663426381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1002910331563013775617587 1504365497344520663426381)
                    ·
                      refine ⟨564137061504195248784893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1504365497344520663426381 564137061504195248784893)
                      ·
                        rfl

theorem cell23_1098653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1098653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098653 prefixEnd_1098653 := by exact prefixLift 1098653
  have htrace : WordTrace (prefixWord ++ tailWord_1098653) baseStart_1098653 baseEnd_1098653 := by
    simpa [prefixWord, tailWord_1098653, baseEnd_1098653] using wordTrace_append hprefix tailTrace_1098653
  have hstable : (prefixWord ++ tailWord_1098653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098653).length < 2 ^ (prefixWord ++ tailWord_1098653).sum := by decide
  have hdescent : baseEnd_1098653 < baseStart_1098653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098679 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1098679 : Nat := 118140960795 + 1098679 * 2 ^ 59
def prefixEnd_1098679 : Nat := 4983230072969 + 3 ^ 40 * 1098679 * 2
def baseEnd_1098679 : Nat := 564150412001212147059773

theorem tailTrace_1098679 : CollatzResearch.WordTrace tailWord_1098679 prefixEnd_1098679 564150412001212147059773 := by
  unfold tailWord_1098679
  simp only [CollatzResearch.WordTrace]
  refine ⟨40072115186681097279571091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26714743457787398186380727 40072115186681097279571091)
  ·
    refine ⟨60108172780021645919356637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40072115186681097279571091 60108172780021645919356637)
    ·
      refine ⟨22540564792508117219758739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60108172780021645919356637 22540564792508117219758739)
      ·
        refine ⟨33810847188762175829638109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22540564792508117219758739 33810847188762175829638109)
        ·
          refine ⟨12679067695785815936114291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33810847188762175829638109 12679067695785815936114291)
          ·
            refine ⟨19018601543678723904171437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12679067695785815936114291 19018601543678723904171437)
            ·
              refine ⟨7131975578879521464064289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19018601543678723904171437 7131975578879521464064289)
              ·
                refine ⟨5348981684159641098048217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7131975578879521464064289 5348981684159641098048217)
                ·
                  refine ⟨4011736263119730823536163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5348981684159641098048217 4011736263119730823536163)
                  ·
                    refine ⟨6017604394679596235304245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4011736263119730823536163 6017604394679596235304245)
                    ·
                      refine ⟨564150412001212147059773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6017604394679596235304245 564150412001212147059773)
                      ·
                        rfl

theorem cell23_1098679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1098679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098679 prefixEnd_1098679 := by exact prefixLift 1098679
  have htrace : WordTrace (prefixWord ++ tailWord_1098679) baseStart_1098679 baseEnd_1098679 := by
    simpa [prefixWord, tailWord_1098679, baseEnd_1098679] using wordTrace_append hprefix tailTrace_1098679
  have hstable : (prefixWord ++ tailWord_1098679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098679).length < 2 ^ (prefixWord ++ tailWord_1098679).sum := by decide
  have hdescent : baseEnd_1098679 < baseStart_1098679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098680 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 1, 3, 2]
def baseStart_1098680 : Nat := 118140960795 + 1098680 * 2 ^ 59
def prefixEnd_1098680 : Nat := 4983230072969 + 3 ^ 40 * 1098680 * 2
def baseEnd_1098680 : Nat := 564150925481866643147269

theorem tailTrace_1098680 : CollatzResearch.WordTrace tailWord_1098680 prefixEnd_1098680 564150925481866643147269 := by
  unfold tailWord_1098680
  simp only [CollatzResearch.WordTrace]
  refine ⟨20036075829838737225178747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26714767773118316300238329 20036075829838737225178747)
  ·
    refine ⟨30054113744758105837768121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20036075829838737225178747 30054113744758105837768121)
    ·
      refine ⟨22540585308568579378326091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30054113744758105837768121 22540585308568579378326091)
      ·
        refine ⟨33810877962852869067489137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22540585308568579378326091 33810877962852869067489137)
        ·
          refine ⟨25358158472139651800616853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33810877962852869067489137 25358158472139651800616853)
          ·
            refine ⟨1188663678381546178153915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25358158472139651800616853 1188663678381546178153915)
            ·
              refine ⟨1782995517572319267230873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188663678381546178153915 1782995517572319267230873)
              ·
                refine ⟨1337246638179239450423155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782995517572319267230873 1337246638179239450423155)
                ·
                  refine ⟨2005869957268859175634733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337246638179239450423155 2005869957268859175634733)
                  ·
                    refine ⟨752201233975822190863025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2005869957268859175634733 752201233975822190863025)
                    ·
                      refine ⟨564150925481866643147269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752201233975822190863025 564150925481866643147269)
                      ·
                        rfl

theorem cell23_1098680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_1098680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098680 prefixEnd_1098680 := by exact prefixLift 1098680
  have htrace : WordTrace (prefixWord ++ tailWord_1098680) baseStart_1098680 baseEnd_1098680 := by
    simpa [prefixWord, tailWord_1098680, baseEnd_1098680] using wordTrace_append hprefix tailTrace_1098680
  have hstable : (prefixWord ++ tailWord_1098680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098680).length < 2 ^ (prefixWord ++ tailWord_1098680).sum := by decide
  have hdescent : baseEnd_1098680 < baseStart_1098680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098736 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 4, 5, 2]
def baseStart_1098736 : Nat := 118140960795 + 1098736 * 2 ^ 59
def prefixEnd_1098736 : Nat := 4983230072969 + 3 ^ 40 * 1098736 * 2
def baseEnd_1098736 : Nat := 564179680398518424047011

theorem tailTrace_1098736 : CollatzResearch.WordTrace tailWord_1098736 prefixEnd_1098736 564179680398518424047011 := by
  unfold tailWord_1098736
  simp only [CollatzResearch.WordTrace]
  refine ⟨20037097073737298007198031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26716129431649730676264041 20037097073737298007198031)
  ·
    refine ⟨30055645610605947010797047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20037097073737298007198031 30055645610605947010797047)
    ·
      refine ⟨45083468415908920516195571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30055645610605947010797047 45083468415908920516195571)
      ·
        refine ⟨67625202623863380774293357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45083468415908920516195571 67625202623863380774293357)
        ·
          refine ⟨25359450983948767790360009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67625202623863380774293357 25359450983948767790360009)
          ·
            refine ⟨19019588237961575842770007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25359450983948767790360009 19019588237961575842770007)
            ·
              refine ⟨28529382356942363764155011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19019588237961575842770007 28529382356942363764155011)
              ·
                refine ⟨42794073535413545646232517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28529382356942363764155011 42794073535413545646232517)
                ·
                  refine ⟨8023888787890039808668597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42794073535413545646232517 8023888787890039808668597)
                  ·
                    refine ⟨752239573864691232062681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8023888787890039808668597 752239573864691232062681)
                    ·
                      refine ⟨564179680398518424047011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752239573864691232062681 564179680398518424047011)
                      ·
                        rfl

theorem cell23_1098736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 5, 2].length) (baseStart_1098736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098736 prefixEnd_1098736 := by exact prefixLift 1098736
  have htrace : WordTrace (prefixWord ++ tailWord_1098736) baseStart_1098736 baseEnd_1098736 := by
    simpa [prefixWord, tailWord_1098736, baseEnd_1098736] using wordTrace_append hprefix tailTrace_1098736
  have hstable : (prefixWord ++ tailWord_1098736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098736).length < 2 ^ (prefixWord ++ tailWord_1098736).sum := by decide
  have hdescent : baseEnd_1098736 < baseStart_1098736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098769 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_1098769 : Nat := 118140960795 + 1098769 * 2 ^ 59
def prefixEnd_1098769 : Nat := 4983230072969 + 3 ^ 40 * 1098769 * 2
def baseEnd_1098769 : Nat := 564196625260116794934359

theorem tailTrace_1098769 : CollatzResearch.WordTrace tailWord_1098769 prefixEnd_1098769 564196625260116794934359 := by
  unfold tailWord_1098769
  simp only [CollatzResearch.WordTrace]
  refine ⟨40075397756355042650347361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26716931837570028433564907 40075397756355042650347361)
  ·
    refine ⟨30056548317266281987760521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40075397756355042650347361 30056548317266281987760521)
    ·
      refine ⟨22542411237949711490820391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30056548317266281987760521 22542411237949711490820391)
      ·
        refine ⟨33813616856924567236230587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22542411237949711490820391 33813616856924567236230587)
        ·
          refine ⟨50720425285386850854345881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33813616856924567236230587 50720425285386850854345881)
          ·
            refine ⟨38040318964040138140759411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50720425285386850854345881 38040318964040138140759411)
            ·
              refine ⟨57060478446060207211139117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38040318964040138140759411 57060478446060207211139117)
              ·
                refine ⟨21397679417272577704177169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57060478446060207211139117 21397679417272577704177169)
                ·
                  refine ⟨16048259562954433278132877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21397679417272577704177169 16048259562954433278132877)
                  ·
                    refine ⟨6018097336107912479299829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16048259562954433278132877 6018097336107912479299829)
                    ·
                      refine ⟨564196625260116794934359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6018097336107912479299829 564196625260116794934359)
                      ·
                        rfl

theorem cell23_1098769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_1098769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098769 prefixEnd_1098769 := by exact prefixLift 1098769
  have htrace : WordTrace (prefixWord ++ tailWord_1098769) baseStart_1098769 baseEnd_1098769 := by
    simpa [prefixWord, tailWord_1098769, baseEnd_1098769] using wordTrace_append hprefix tailTrace_1098769
  have hstable : (prefixWord ++ tailWord_1098769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098769).length < 2 ^ (prefixWord ++ tailWord_1098769).sum := by decide
  have hdescent : baseEnd_1098769 < baseStart_1098769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098783 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 2, 4, 2]
def baseStart_1098783 : Nat := 118140960795 + 1098783 * 2 ^ 59
def prefixEnd_1098783 : Nat := 4983230072969 + 3 ^ 40 * 1098783 * 2
def baseEnd_1098783 : Nat := 564203813989279740159295

theorem tailTrace_1098783 : CollatzResearch.WordTrace tailWord_1098783 prefixEnd_1098783 564203813989279740159295 := by
  unfold tailWord_1098783
  simp only [CollatzResearch.WordTrace]
  refine ⟨40075908378304323041357003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26717272252202882027571335 40075908378304323041357003)
  ·
    refine ⟨60113862567456484562035505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40075908378304323041357003 60113862567456484562035505)
    ·
      refine ⟨45085396925592363421526629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60113862567456484562035505 45085396925592363421526629)
      ·
        refine ⟨8453511923548568141536243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45085396925592363421526629 8453511923548568141536243)
        ·
          refine ⟨12680267885322852212304365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8453511923548568141536243 12680267885322852212304365)
          ·
            refine ⟨4755100456996069579614137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12680267885322852212304365 4755100456996069579614137)
            ·
              refine ⟨3566325342747052184710603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4755100456996069579614137 3566325342747052184710603)
              ·
                refine ⟨5349488014120578277065905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566325342747052184710603 5349488014120578277065905)
                ·
                  refine ⟨4012116010590433707799429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5349488014120578277065905 4012116010590433707799429)
                  ·
                    refine ⟨752271751985706320212393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012116010590433707799429 752271751985706320212393)
                    ·
                      refine ⟨564203813989279740159295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752271751985706320212393 564203813989279740159295)
                      ·
                        rfl

theorem cell23_1098783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_1098783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098783 prefixEnd_1098783 := by exact prefixLift 1098783
  have htrace : WordTrace (prefixWord ++ tailWord_1098783) baseStart_1098783 baseEnd_1098783 := by
    simpa [prefixWord, tailWord_1098783, baseEnd_1098783] using wordTrace_append hprefix tailTrace_1098783
  have hstable : (prefixWord ++ tailWord_1098783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098783).length < 2 ^ (prefixWord ++ tailWord_1098783).sum := by decide
  have hdescent : baseEnd_1098783 < baseStart_1098783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098810 : List Nat := [3, 1, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_1098810 : Nat := 118140960795 + 1098810 * 2 ^ 59
def prefixEnd_1098810 : Nat := 4983230072969 + 3 ^ 40 * 1098810 * 2
def baseEnd_1098810 : Nat := 188072559322317044840557

theorem tailTrace_1098810 : CollatzResearch.WordTrace tailWord_1098810 prefixEnd_1098810 188072559322317044840557 := by
  unfold tailWord_1098810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10019223287301626663147471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26717928766137671101726589 10019223287301626663147471)
  ·
    refine ⟨15028834930952439994721207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10019223287301626663147471 15028834930952439994721207)
    ·
      refine ⟨22543252396428659992081811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15028834930952439994721207 22543252396428659992081811)
      ·
        refine ⟨33814878594642989988122717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22543252396428659992081811 33814878594642989988122717)
        ·
          refine ⟨12680579472991121245546019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33814878594642989988122717 12680579472991121245546019)
          ·
            refine ⟨19020869209486681868319029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12680579472991121245546019 19020869209486681868319029)
            ·
              refine ⟨1783206488389376425154909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19020869209486681868319029 1783206488389376425154909)
              ·
                refine ⟨668702433146016159433091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783206488389376425154909 668702433146016159433091)
                ·
                  refine ⟨1003053649719024239149637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668702433146016159433091 1003053649719024239149637)
                  ·
                    refine ⟨188072559322317044840557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003053649719024239149637 188072559322317044840557)
                    ·
                      rfl

theorem cell23_1098810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_1098810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098810 prefixEnd_1098810 := by exact prefixLift 1098810
  have htrace : WordTrace (prefixWord ++ tailWord_1098810) baseStart_1098810 baseEnd_1098810 := by
    simpa [prefixWord, tailWord_1098810, baseEnd_1098810] using wordTrace_append hprefix tailTrace_1098810
  have hstable : (prefixWord ++ tailWord_1098810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098810).length < 2 ^ (prefixWord ++ tailWord_1098810).sum := by decide
  have hdescent : baseEnd_1098810 < baseStart_1098810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098860 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 2, 3, 2]
def baseStart_1098860 : Nat := 118140960795 + 1098860 * 2 ^ 59
def prefixEnd_1098860 : Nat := 4983230072969 + 3 ^ 40 * 1098860 * 2
def baseEnd_1098860 : Nat := 564243351999675938896441

theorem tailTrace_1098860 : CollatzResearch.WordTrace tailWord_1098860 prefixEnd_1098860 564243351999675938896441 := by
  unfold tailWord_1098860
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039358399512682595955017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26719144532683576794606689 20039358399512682595955017)
  ·
    refine ⟨15029518799634511946966263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20039358399512682595955017 15029518799634511946966263)
    ·
      refine ⟨22544278199451767920449395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15029518799634511946966263 22544278199451767920449395)
      ·
        refine ⟨33816417299177651880674093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22544278199451767920449395 33816417299177651880674093)
        ·
          refine ⟨12681156487191619455252785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33816417299177651880674093 12681156487191619455252785)
          ·
            refine ⟨9510867365393714591439589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12681156487191619455252785 9510867365393714591439589)
            ·
              refine ⟨1783287631011321485894923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9510867365393714591439589 1783287631011321485894923)
              ·
                refine ⟨2674931446516982228842385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783287631011321485894923 2674931446516982228842385)
                ·
                  refine ⟨2006198584887736671631789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2674931446516982228842385 2006198584887736671631789)
                  ·
                    refine ⟨752324469332901251861921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006198584887736671631789 752324469332901251861921)
                    ·
                      refine ⟨564243351999675938896441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752324469332901251861921 564243351999675938896441)
                      ·
                        rfl

theorem cell23_1098860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_1098860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098860 prefixEnd_1098860 := by exact prefixLift 1098860
  have htrace : WordTrace (prefixWord ++ tailWord_1098860) baseStart_1098860 baseEnd_1098860 := by
    simpa [prefixWord, tailWord_1098860, baseEnd_1098860] using wordTrace_append hprefix tailTrace_1098860
  have hstable : (prefixWord ++ tailWord_1098860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098860).length < 2 ^ (prefixWord ++ tailWord_1098860).sum := by decide
  have hdescent : baseEnd_1098860 < baseStart_1098860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098884 : List Nat := [2, 3, 2, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_1098884 : Nat := 118140960795 + 1098884 * 2 ^ 59
def prefixEnd_1098884 : Nat := 4983230072969 + 3 ^ 40 * 1098884 * 2
def baseEnd_1098884 : Nat := 564255675535383844996331

theorem tailTrace_1098884 : CollatzResearch.WordTrace tailWord_1098884 prefixEnd_1098884 564255675535383844996331 := by
  unfold tailWord_1098884
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039796075469208645391853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26719728100625611527189137 20039796075469208645391853)
  ·
    refine ⟨7514923528300953242021945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20039796075469208645391853 7514923528300953242021945)
    ·
      refine ⟨5636192646225714931516459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7514923528300953242021945 5636192646225714931516459)
      ·
        refine ⟨8454288969338572397274689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5636192646225714931516459 8454288969338572397274689)
        ·
          refine ⟨6340716727003929297956017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8454288969338572397274689 6340716727003929297956017)
          ·
            refine ⟨4755537545252946973467013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6340716727003929297956017 4755537545252946973467013)
            ·
              refine ⟨891663289734927557525065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4755537545252946973467013 891663289734927557525065)
              ·
                refine ⟨668747467301195668143799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891663289734927557525065 668747467301195668143799)
                ·
                  refine ⟨1003121200951793502215699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668747467301195668143799 1003121200951793502215699)
                  ·
                    refine ⟨1504681801427690253323549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1003121200951793502215699 1504681801427690253323549)
                    ·
                      refine ⟨564255675535383844996331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1504681801427690253323549 564255675535383844996331)
                      ·
                        rfl

theorem cell23_1098884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_1098884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098884 prefixEnd_1098884 := by exact prefixLift 1098884
  have htrace : WordTrace (prefixWord ++ tailWord_1098884) baseStart_1098884 baseEnd_1098884 := by
    simpa [prefixWord, tailWord_1098884, baseEnd_1098884] using wordTrace_append hprefix tailTrace_1098884
  have hstable : (prefixWord ++ tailWord_1098884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098884).length < 2 ^ (prefixWord ++ tailWord_1098884).sum := by decide
  have hdescent : baseEnd_1098884 < baseStart_1098884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098903 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1098903 : Nat := 118140960795 + 1098903 * 2 ^ 59
def prefixEnd_1098903 : Nat := 4983230072969 + 3 ^ 40 * 1098903 * 2
def baseEnd_1098903 : Nat := 564265431667819270658743

theorem tailTrace_1098903 : CollatzResearch.WordTrace tailWord_1098903 prefixEnd_1098903 564265431667819270658743 := by
  unfold tailWord_1098903
  simp only [CollatzResearch.WordTrace]
  refine ⟨40080285137869583535725363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26720190091913055690483575 40080285137869583535725363)
  ·
    refine ⟨60120427706804375303588045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40080285137869583535725363 60120427706804375303588045)
    ·
      refine ⟨22545160390051640738845517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60120427706804375303588045 22545160390051640738845517)
      ·
        refine ⟨8454435146269365277067069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22545160390051640738845517 8454435146269365277067069)
        ·
          refine ⟨3170413179851011978900151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8454435146269365277067069 3170413179851011978900151)
          ·
            refine ⟨4755619769776517968350227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170413179851011978900151 4755619769776517968350227)
            ·
              refine ⟨7133429654664776952525341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755619769776517968350227 7133429654664776952525341)
              ·
                refine ⟨2675036120499291357197003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7133429654664776952525341 2675036120499291357197003)
                ·
                  refine ⟨4012554180748937035795505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675036120499291357197003 4012554180748937035795505)
                  ·
                    refine ⟨3009415635561702776846629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4012554180748937035795505 3009415635561702776846629)
                    ·
                      refine ⟨564265431667819270658743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3009415635561702776846629 564265431667819270658743)
                      ·
                        rfl

theorem cell23_1098903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1098903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098903 prefixEnd_1098903 := by exact prefixLift 1098903
  have htrace : WordTrace (prefixWord ++ tailWord_1098903) baseStart_1098903 baseEnd_1098903 := by
    simpa [prefixWord, tailWord_1098903, baseEnd_1098903] using wordTrace_append hprefix tailTrace_1098903
  have hstable : (prefixWord ++ tailWord_1098903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098903).length < 2 ^ (prefixWord ++ tailWord_1098903).sum := by decide
  have hdescent : baseEnd_1098903 < baseStart_1098903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098913 : List Nat := [1, 2, 3, 3, 1, 1, 5, 7]
def baseStart_1098913 : Nat := 118140960795 + 1098913 * 2 ^ 59
def prefixEnd_1098913 : Nat := 4983230072969 + 3 ^ 40 * 1098913 * 2
def baseEnd_1098913 : Nat := 20898909869420897464211

theorem tailTrace_1098913 : CollatzResearch.WordTrace tailWord_1098913 prefixEnd_1098913 20898909869420897464211 := by
  unfold tailWord_1098913
  simp only [CollatzResearch.WordTrace]
  refine ⟨40080649867833355243589393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26720433245222236829059595 40080649867833355243589393)
  ·
    refine ⟨30060487400875016432692045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40080649867833355243589393 30060487400875016432692045)
    ·
      refine ⟨11272682775328131162259517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30060487400875016432692045 11272682775328131162259517)
      ·
        refine ⟨4227256040748049185847319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11272682775328131162259517 4227256040748049185847319)
        ·
          refine ⟨6340884061122073778770979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4227256040748049185847319 6340884061122073778770979)
          ·
            refine ⟨9511326091683110668156469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6340884061122073778770979 9511326091683110668156469)
            ·
              refine ⟨891686821095291625139669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9511326091683110668156469 891686821095291625139669)
              ·
                refine ⟨20898909869420897464211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 891686821095291625139669 20898909869420897464211)
                ·
                  rfl

theorem cell23_1098913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 7].length) (baseStart_1098913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098913 prefixEnd_1098913 := by exact prefixLift 1098913
  have htrace : WordTrace (prefixWord ++ tailWord_1098913) baseStart_1098913 baseEnd_1098913 := by
    simpa [prefixWord, tailWord_1098913, baseEnd_1098913] using wordTrace_append hprefix tailTrace_1098913
  have hstable : (prefixWord ++ tailWord_1098913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098913).length < 2 ^ (prefixWord ++ tailWord_1098913).sum := by decide
  have hdescent : baseEnd_1098913 < baseStart_1098913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098934 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1098934 : Nat := 118140960795 + 1098934 * 2 ^ 59
def prefixEnd_1098934 : Nat := 4983230072969 + 3 ^ 40 * 1098934 * 2
def baseEnd_1098934 : Nat := 188093783189369549790367

theorem tailTrace_1098934 : CollatzResearch.WordTrace tailWord_1098934 prefixEnd_1098934 188093783189369549790367 := by
  unfold tailWord_1098934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505088487547329739381491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26720943867171517220069237 2505088487547329739381491)
  ·
    refine ⟨3757632731320994609072237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2505088487547329739381491 3757632731320994609072237)
    ·
      refine ⟨1409112274245372978402089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3757632731320994609072237 1409112274245372978402089)
      ·
        refine ⟨1056834205684029733801567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1409112274245372978402089 1056834205684029733801567)
        ·
          refine ⟨1585251308526044600702351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056834205684029733801567 1585251308526044600702351)
          ·
            refine ⟨2377876962789066901053527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585251308526044600702351 2377876962789066901053527)
            ·
              refine ⟨3566815444183600351580291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377876962789066901053527 3566815444183600351580291)
              ·
                refine ⟨5350223166275400527370437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566815444183600351580291 5350223166275400527370437)
                ·
                  refine ⟨1003166843676637598881957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5350223166275400527370437 1003166843676637598881957)
                  ·
                    refine ⟨188093783189369549790367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003166843676637598881957 188093783189369549790367)
                    ·
                      rfl

theorem cell23_1098934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1098934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098934 prefixEnd_1098934 := by exact prefixLift 1098934
  have htrace : WordTrace (prefixWord ++ tailWord_1098934) baseStart_1098934 baseEnd_1098934 := by
    simpa [prefixWord, tailWord_1098934, baseEnd_1098934] using wordTrace_append hprefix tailTrace_1098934
  have hstable : (prefixWord ++ tailWord_1098934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098934).length < 2 ^ (prefixWord ++ tailWord_1098934).sum := by decide
  have hdescent : baseEnd_1098934 < baseStart_1098934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098936 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_1098936 : Nat := 118140960795 + 1098936 * 2 ^ 59
def prefixEnd_1098936 : Nat := 4983230072969 + 3 ^ 40 * 1098936 * 2
def baseEnd_1098936 : Nat := 564282376529417641546091

theorem tailTrace_1098936 : CollatzResearch.WordTrace tailWord_1098936 prefixEnd_1098936 564282376529417641546091 := by
  unfold tailWord_1098936
  simp only [CollatzResearch.WordTrace]
  refine ⟨20040744373375015085838331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26720992497833353447784441 20040744373375015085838331)
  ·
    refine ⟨30061116560062522628757497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20040744373375015085838331 30061116560062522628757497)
    ·
      refine ⟨22545837420046891971568123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30061116560062522628757497 22545837420046891971568123)
      ·
        refine ⟨33818756130070337957352185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22545837420046891971568123 33818756130070337957352185)
        ·
          refine ⟨25364067097552753468014139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33818756130070337957352185 25364067097552753468014139)
          ·
            refine ⟨38046100646329130202021209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25364067097552753468014139 38046100646329130202021209)
            ·
              refine ⟨28534575484746847651515907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38046100646329130202021209 28534575484746847651515907)
              ·
                refine ⟨42801863227120271477273861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28534575484746847651515907 42801863227120271477273861)
                ·
                  refine ⟨8025349355085050901988849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42801863227120271477273861 8025349355085050901988849)
                  ·
                    refine ⟨6019012016313788176491637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8025349355085050901988849 6019012016313788176491637)
                    ·
                      refine ⟨564282376529417641546091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6019012016313788176491637 564282376529417641546091)
                      ·
                        rfl

theorem cell23_1098936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_1098936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098936 prefixEnd_1098936 := by exact prefixLift 1098936
  have htrace : WordTrace (prefixWord ++ tailWord_1098936) baseStart_1098936 baseEnd_1098936 := by
    simpa [prefixWord, tailWord_1098936, baseEnd_1098936] using wordTrace_append hprefix tailTrace_1098936
  have hstable : (prefixWord ++ tailWord_1098936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098936).length < 2 ^ (prefixWord ++ tailWord_1098936).sum := by decide
  have hdescent : baseEnd_1098936 < baseStart_1098936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098964 : List Nat := [2, 4, 1, 4, 2, 1, 2, 7]
def baseStart_1098964 : Nat := 118140960795 + 1098964 * 2 ^ 59
def prefixEnd_1098964 : Nat := 4983230072969 + 3 ^ 40 * 1098964 * 2
def baseEnd_1098964 : Nat := 20899879777323834518369

theorem tailTrace_1098964 : CollatzResearch.WordTrace tailWord_1098964 prefixEnd_1098964 20899879777323834518369 := by
  unfold tailWord_1098964
  simp only [CollatzResearch.WordTrace]
  refine ⟨20041254995324295476847973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26721673327099060635797297 20041254995324295476847973)
  ·
    refine ⟨3757735311623305401908995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20041254995324295476847973 3757735311623305401908995)
    ·
      refine ⟨5636602967434958102863493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757735311623305401908995 5636602967434958102863493)
      ·
        refine ⟨1056863056394054644286905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5636602967434958102863493 1056863056394054644286905)
        ·
          refine ⟨792647292295540983215179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1056863056394054644286905 792647292295540983215179)
          ·
            refine ⟨1188970938443311474822769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792647292295540983215179 1188970938443311474822769)
            ·
              refine ⟨891728203832483606117077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188970938443311474822769 891728203832483606117077)
              ·
                refine ⟨20899879777323834518369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 891728203832483606117077 20899879777323834518369)
                ·
                  rfl

theorem cell23_1098964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 7].length) (baseStart_1098964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098964 prefixEnd_1098964 := by exact prefixLift 1098964
  have htrace : WordTrace (prefixWord ++ tailWord_1098964) baseStart_1098964 baseEnd_1098964 := by
    simpa [prefixWord, tailWord_1098964, baseEnd_1098964] using wordTrace_append hprefix tailTrace_1098964
  have hstable : (prefixWord ++ tailWord_1098964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098964).length < 2 ^ (prefixWord ++ tailWord_1098964).sum := by decide
  have hdescent : baseEnd_1098964 < baseStart_1098964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1098980 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_1098980 : Nat := 118140960795 + 1098980 * 2 ^ 59
def prefixEnd_1098980 : Nat := 4983230072969 + 3 ^ 40 * 1098980 * 2
def baseEnd_1098980 : Nat := 564304969678215469395889

theorem tailTrace_1098980 : CollatzResearch.WordTrace tailWord_1098980 prefixEnd_1098980 564304969678215469395889 := by
  unfold tailWord_1098980
  simp only [CollatzResearch.WordTrace]
  refine ⟨20041546779295312843139197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26722062372393750457518929 20041546779295312843139197)
  ·
    refine ⟨7515580042235742316177199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20041546779295312843139197 7515580042235742316177199)
    ·
      refine ⟨11273370063353613474265799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7515580042235742316177199 11273370063353613474265799)
      ·
        refine ⟨16910055095030420211398699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11273370063353613474265799 16910055095030420211398699)
        ·
          refine ⟨25365082642545630317098049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16910055095030420211398699 25365082642545630317098049)
          ·
            refine ⟨19023811981909222737823537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25365082642545630317098049 19023811981909222737823537)
            ·
              refine ⟨14267858986431917053367653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19023811981909222737823537 14267858986431917053367653)
              ·
                refine ⟨2675223559955984447506435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14267858986431917053367653 2675223559955984447506435)
                ·
                  refine ⟨4012835339933976671259653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675223559955984447506435 4012835339933976671259653)
                  ·
                    refine ⟨752406626237620625861185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4012835339933976671259653 752406626237620625861185)
                    ·
                      refine ⟨564304969678215469395889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752406626237620625861185 564304969678215469395889)
                      ·
                        rfl

theorem cell23_1098980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_1098980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1098980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1098980 prefixEnd_1098980 := by exact prefixLift 1098980
  have htrace : WordTrace (prefixWord ++ tailWord_1098980) baseStart_1098980 baseEnd_1098980 := by
    simpa [prefixWord, tailWord_1098980, baseEnd_1098980] using wordTrace_append hprefix tailTrace_1098980
  have hstable : (prefixWord ++ tailWord_1098980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1098980).length < 2 ^ (prefixWord ++ tailWord_1098980).sum := by decide
  have hdescent : baseEnd_1098980 < baseStart_1098980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1098980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099013 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_1099013 : Nat := 118140960795 + 1099013 * 2 ^ 59
def prefixEnd_1099013 : Nat := 4983230072969 + 3 ^ 40 * 1099013 * 2
def baseEnd_1099013 : Nat := 564321914539813840283237

theorem tailTrace_1099013 : CollatzResearch.WordTrace tailWord_1099013 prefixEnd_1099013 564321914539813840283237 := by
  unfold tailWord_1099013
  simp only [CollatzResearch.WordTrace]
  refine ⟨40084297167471072322229693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26722864778314048214819795 40084297167471072322229693)
  ·
    refine ⟨15031611437801652120836135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40084297167471072322229693 15031611437801652120836135)
    ·
      refine ⟨22547417156702478181254203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15031611437801652120836135 22547417156702478181254203)
      ·
        refine ⟨33821125735053717271881305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22547417156702478181254203 33821125735053717271881305)
        ·
          refine ⟨25365844301290287953910979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33821125735053717271881305 25365844301290287953910979)
          ·
            refine ⟨38048766451935431930866469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25365844301290287953910979 38048766451935431930866469)
            ·
              refine ⟨7134143709737893487037463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38048766451935431930866469 7134143709737893487037463)
              ·
                refine ⟨10701215564606840230556195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7134143709737893487037463 10701215564606840230556195)
                ·
                  refine ⟨16051823346910260345834293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10701215564606840230556195 16051823346910260345834293)
                  ·
                    refine ⟨1504858438772836907421965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16051823346910260345834293 1504858438772836907421965)
                    ·
                      refine ⟨564321914539813840283237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1504858438772836907421965 564321914539813840283237)
                      ·
                        rfl

theorem cell23_1099013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_1099013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099013 prefixEnd_1099013 := by exact prefixLift 1099013
  have htrace : WordTrace (prefixWord ++ tailWord_1099013) baseStart_1099013 baseEnd_1099013 := by
    simpa [prefixWord, tailWord_1099013, baseEnd_1099013] using wordTrace_append hprefix tailTrace_1099013
  have hstable : (prefixWord ++ tailWord_1099013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099013).length < 2 ^ (prefixWord ++ tailWord_1099013).sum := by decide
  have hdescent : baseEnd_1099013 < baseStart_1099013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099043 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1099043 : Nat := 118140960795 + 1099043 * 2 ^ 59
def prefixEnd_1099043 : Nat := 4983230072969 + 3 ^ 40 * 1099043 * 2
def baseEnd_1099043 : Nat := 564337318959448722908099

theorem tailTrace_1099043 : CollatzResearch.WordTrace tailWord_1099043 prefixEnd_1099043 564337318959448722908099 := by
  unfold tailWord_1099043
  simp only [CollatzResearch.WordTrace]
  refine ⟨40085391357362387445821783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26723594238241591630547855 40085391357362387445821783)
  ·
    refine ⟨60128087036043581168732675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40085391357362387445821783 60128087036043581168732675)
    ·
      refine ⟨90192130554065371753099013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60128087036043581168732675 90192130554065371753099013)
      ·
        refine ⟨16911024478887257203706065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90192130554065371753099013 16911024478887257203706065)
        ·
          refine ⟨12683268359165442902779549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16911024478887257203706065 12683268359165442902779549)
          ·
            refine ⟨4756225634687041088542331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12683268359165442902779549 4756225634687041088542331)
            ·
              refine ⟨7134338452030561632813497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4756225634687041088542331 7134338452030561632813497)
              ·
                refine ⟨5350753839022921224610123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7134338452030561632813497 5350753839022921224610123)
                ·
                  refine ⟨8026130758534381836915185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5350753839022921224610123 8026130758534381836915185)
                  ·
                    refine ⟨6019598068900786377686389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8026130758534381836915185 6019598068900786377686389)
                    ·
                      refine ⟨564337318959448722908099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6019598068900786377686389 564337318959448722908099)
                      ·
                        rfl

theorem cell23_1099043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1099043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099043 prefixEnd_1099043 := by exact prefixLift 1099043
  have htrace : WordTrace (prefixWord ++ tailWord_1099043) baseStart_1099043 baseEnd_1099043 := by
    simpa [prefixWord, tailWord_1099043, baseEnd_1099043] using wordTrace_append hprefix tailTrace_1099043
  have hstable : (prefixWord ++ tailWord_1099043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099043).length < 2 ^ (prefixWord ++ tailWord_1099043).sum := by decide
  have hdescent : baseEnd_1099043 < baseStart_1099043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099060 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1099060 : Nat := 118140960795 + 1099060 * 2 ^ 59
def prefixEnd_1099060 : Nat := 4983230072969 + 3 ^ 40 * 1099060 * 2
def baseEnd_1099060 : Nat := 564346048130575156395521

theorem tailTrace_1099060 : CollatzResearch.WordTrace tailWord_1099060 prefixEnd_1099060 564346048130575156395521 := by
  unfold tailWord_1099060
  simp only [CollatzResearch.WordTrace]
  refine ⟨20043005699150399674595317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26724007598867199566127089 20043005699150399674595317)
  ·
    refine ⟨1879031784295349969493311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20043005699150399674595317 1879031784295349969493311)
    ·
      refine ⟨2818547676443024954239967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879031784295349969493311 2818547676443024954239967)
      ·
        refine ⟨4227821514664537431359951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2818547676443024954239967 4227821514664537431359951)
        ·
          refine ⟨6341732271996806147039927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4227821514664537431359951 6341732271996806147039927)
          ·
            refine ⟨9512598407995209220559891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6341732271996806147039927 9512598407995209220559891)
            ·
              refine ⟨14268897611992813830839837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9512598407995209220559891 14268897611992813830839837)
              ·
                refine ⟨5350836604497305186564939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14268897611992813830839837 5350836604497305186564939)
                ·
                  refine ⟨8026254906745957779847409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5350836604497305186564939 8026254906745957779847409)
                  ·
                    refine ⟨6019691180059468334885557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8026254906745957779847409 6019691180059468334885557)
                    ·
                      refine ⟨564346048130575156395521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6019691180059468334885557 564346048130575156395521)
                      ·
                        rfl

theorem cell23_1099060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1099060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099060 prefixEnd_1099060 := by exact prefixLift 1099060
  have htrace : WordTrace (prefixWord ++ tailWord_1099060) baseStart_1099060 baseEnd_1099060 := by
    simpa [prefixWord, tailWord_1099060, baseEnd_1099060] using wordTrace_append hprefix tailTrace_1099060
  have hstable : (prefixWord ++ tailWord_1099060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099060).length < 2 ^ (prefixWord ++ tailWord_1099060).sum := by decide
  have hdescent : baseEnd_1099060 < baseStart_1099060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099070 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1099070 : Nat := 118140960795 + 1099070 * 2 ^ 59
def prefixEnd_1099070 : Nat := 4983230072969 + 3 ^ 40 * 1099070 * 2
def baseEnd_1099070 : Nat := 564351182937120117270475

theorem tailTrace_1099070 : CollatzResearch.WordTrace tailWord_1099070 prefixEnd_1099070 564351182937120117270475 := by
  unfold tailWord_1099070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010797016033071382131833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26724250752176380704703109 5010797016033071382131833)
  ·
    refine ⟨3758097762024803536598875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5010797016033071382131833 3758097762024803536598875)
    ·
      refine ⟨5637146643037205304898313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758097762024803536598875 5637146643037205304898313)
      ·
        refine ⟨4227859982277903978673735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5637146643037205304898313 4227859982277903978673735)
        ·
          refine ⟨6341789973416855968010603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4227859982277903978673735 6341789973416855968010603)
          ·
            refine ⟨9512684960125283952015905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6341789973416855968010603 9512684960125283952015905)
            ·
              refine ⟨7134513720093962964011929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9512684960125283952015905 7134513720093962964011929)
              ·
                refine ⟨5350885290070472223008947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7134513720093962964011929 5350885290070472223008947)
                ·
                  refine ⟨8026327935105708334513421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5350885290070472223008947 8026327935105708334513421)
                  ·
                    refine ⟨3009872975664640625442533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8026327935105708334513421 3009872975664640625442533)
                    ·
                      refine ⟨564351182937120117270475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3009872975664640625442533 564351182937120117270475)
                      ·
                        rfl

theorem cell23_1099070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1099070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099070 prefixEnd_1099070 := by exact prefixLift 1099070
  have htrace : WordTrace (prefixWord ++ tailWord_1099070) baseStart_1099070 baseEnd_1099070 := by
    simpa [prefixWord, tailWord_1099070, baseEnd_1099070] using wordTrace_append hprefix tailTrace_1099070
  have hstable : (prefixWord ++ tailWord_1099070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099070).length < 2 ^ (prefixWord ++ tailWord_1099070).sum := by decide
  have hdescent : baseEnd_1099070 < baseStart_1099070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099097 : List Nat := [1, 2, 1, 2, 2, 2, 3, 5, 1, 4]
def baseStart_1099097 : Nat := 118140960795 + 1099097 * 2 ^ 59
def prefixEnd_1099097 : Nat := 4983230072969 + 3 ^ 40 * 1099097 * 2
def baseEnd_1099097 : Nat := 188121682304930503877617

theorem tailTrace_1099097 : CollatzResearch.WordTrace tailWord_1099097 prefixEnd_1099097 188121682304930503877617 := by
  unfold tailWord_1099097
  simp only [CollatzResearch.WordTrace]
  refine ⟨40087360899166754668287545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26724907266111169778858363 40087360899166754668287545)
  ·
    refine ⟨30065520674375066001215659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40087360899166754668287545 30065520674375066001215659)
    ·
      refine ⟨45098281011562599001823489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30065520674375066001215659 45098281011562599001823489)
      ·
        refine ⟨33823710758671949251367617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45098281011562599001823489 33823710758671949251367617)
        ·
          refine ⟨25367783069003961938525713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33823710758671949251367617 25367783069003961938525713)
          ·
            refine ⟨19025837301752971453894285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25367783069003961938525713 19025837301752971453894285)
            ·
              refine ⟨7134688988157364295210357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19025837301752971453894285 7134688988157364295210357)
              ·
                refine ⟨668877092639752902675971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7134688988157364295210357 668877092639752902675971)
                ·
                  refine ⟨1003315638959629354013957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668877092639752902675971 1003315638959629354013957)
                  ·
                    refine ⟨188121682304930503877617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003315638959629354013957 188121682304930503877617)
                    ·
                      rfl

theorem cell23_1099097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 4].length) (baseStart_1099097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099097 prefixEnd_1099097 := by exact prefixLift 1099097
  have htrace : WordTrace (prefixWord ++ tailWord_1099097) baseStart_1099097 baseEnd_1099097 := by
    simpa [prefixWord, tailWord_1099097, baseEnd_1099097] using wordTrace_append hprefix tailTrace_1099097
  have hstable : (prefixWord ++ tailWord_1099097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099097).length < 2 ^ (prefixWord ++ tailWord_1099097).sum := by decide
  have hdescent : baseEnd_1099097 < baseStart_1099097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099114 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1099114 : Nat := 118140960795 + 1099114 * 2 ^ 59
def prefixEnd_1099114 : Nat := 4983230072969 + 3 ^ 40 * 1099114 * 2
def baseEnd_1099114 : Nat := 188124592028639315040091

theorem tailTrace_1099114 : CollatzResearch.WordTrace tailWord_1099114 prefixEnd_1099114 188124592028639315040091 := by
  unfold tailWord_1099114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10021995235026291642914099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26725320626736777714437597 10021995235026291642914099)
  ·
    refine ⟨15032992852539437464371149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10021995235026291642914099 15032992852539437464371149)
    ·
      refine ⟨5637372319702289049139181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15032992852539437464371149 5637372319702289049139181)
      ·
        refine ⟨2114014619888358393427193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5637372319702289049139181 2114014619888358393427193)
        ·
          refine ⟨1585510964916268795070395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2114014619888358393427193 1585510964916268795070395)
          ·
            refine ⟨2378266447374403192605593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585510964916268795070395 2378266447374403192605593)
            ·
              refine ⟨1783699835530802394454195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2378266447374403192605593 1783699835530802394454195)
              ·
                refine ⟨2675549753296203591681293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783699835530802394454195 2675549753296203591681293)
                ·
                  refine ⟨1003331157486076346880485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2675549753296203591681293 1003331157486076346880485)
                  ·
                    refine ⟨188124592028639315040091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003331157486076346880485 188124592028639315040091)
                    ·
                      rfl

theorem cell23_1099114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1099114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099114 prefixEnd_1099114 := by exact prefixLift 1099114
  have htrace : WordTrace (prefixWord ++ tailWord_1099114) baseStart_1099114 baseEnd_1099114 := by
    simpa [prefixWord, tailWord_1099114, baseEnd_1099114] using wordTrace_append hprefix tailTrace_1099114
  have hstable : (prefixWord ++ tailWord_1099114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099114).length < 2 ^ (prefixWord ++ tailWord_1099114).sum := by decide
  have hdescent : baseEnd_1099114 < baseStart_1099114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099147 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 2, 3, 2]
def baseStart_1099147 : Nat := 118140960795 + 1099147 * 2 ^ 59
def prefixEnd_1099147 : Nat := 4983230072969 + 3 ^ 40 * 1099147 * 2
def baseEnd_1099147 : Nat := 564390720947516316007621

theorem tailTrace_1099147 : CollatzResearch.WordTrace tailWord_1099147 prefixEnd_1099147 564390720947516316007621 := by
  unfold tailWord_1099147
  simp only [CollatzResearch.WordTrace]
  refine ⟨40089184548985613207607695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26726123032657075471738463 40089184548985613207607695)
  ·
    refine ⟨60133776823478419811411543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40089184548985613207607695 60133776823478419811411543)
    ·
      refine ⟨90200665235217629717117315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60133776823478419811411543 90200665235217629717117315)
      ·
        refine ⟨135300997852826444575675973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90200665235217629717117315 135300997852826444575675973)
        ·
          refine ⟨25368937097404958357939245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135300997852826444575675973 25368937097404958357939245)
          ·
            refine ⟨9513351411526859384227217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25368937097404958357939245 9513351411526859384227217)
            ·
              refine ⟨7135013558645144538170413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9513351411526859384227217 7135013558645144538170413)
              ·
                refine ⟨2675630084491929201813905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7135013558645144538170413 2675630084491929201813905)
                ·
                  refine ⟨2006722563368946901360429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2675630084491929201813905 2006722563368946901360429)
                  ·
                    refine ⟨752520961263355088010161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006722563368946901360429 752520961263355088010161)
                    ·
                      refine ⟨564390720947516316007621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752520961263355088010161 564390720947516316007621)
                      ·
                        rfl

theorem cell23_1099147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3, 2].length) (baseStart_1099147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099147 prefixEnd_1099147 := by exact prefixLift 1099147
  have htrace : WordTrace (prefixWord ++ tailWord_1099147) baseStart_1099147 baseEnd_1099147 := by
    simpa [prefixWord, tailWord_1099147, baseEnd_1099147] using wordTrace_append hprefix tailTrace_1099147
  have hstable : (prefixWord ++ tailWord_1099147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099147).length < 2 ^ (prefixWord ++ tailWord_1099147).sum := by decide
  have hdescent : baseEnd_1099147 < baseStart_1099147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099171 : List Nat := [1, 1, 1, 4, 1, 3, 5, 2, 1, 1, 3]
def baseStart_1099171 : Nat := 118140960795 + 1099171 * 2 ^ 59
def prefixEnd_1099171 : Nat := 4983230072969 + 3 ^ 40 * 1099171 * 2
def baseEnd_1099171 : Nat := 564403044483224222107511

theorem tailTrace_1099171 : CollatzResearch.WordTrace tailWord_1099171 prefixEnd_1099171 564403044483224222107511 := by
  unfold tailWord_1099171
  simp only [CollatzResearch.WordTrace]
  refine ⟨40090059900898665306481367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26726706600599110204320911 40090059900898665306481367)
  ·
    refine ⟨60135089851347997959722051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40090059900898665306481367 60135089851347997959722051)
    ·
      refine ⟨90202634777021996939583077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60135089851347997959722051 90202634777021996939583077)
      ·
        refine ⟨16912994020691624426171827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90202634777021996939583077 16912994020691624426171827)
        ·
          refine ⟨25369491031037436639257741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16912994020691624426171827 25369491031037436639257741)
          ·
            refine ⟨9513559136639038739721653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25369491031037436639257741 9513559136639038739721653)
            ·
              refine ⟨891896169059909881848905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9513559136639038739721653 891896169059909881848905)
              ·
                refine ⟨668922126794932411386679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891896169059909881848905 668922126794932411386679)
                ·
                  refine ⟨1003383190192398617080019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668922126794932411386679 1003383190192398617080019)
                  ·
                    refine ⟨1505074785288597925620029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1003383190192398617080019 1505074785288597925620029)
                    ·
                      refine ⟨564403044483224222107511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1505074785288597925620029 564403044483224222107511)
                      ·
                        rfl

theorem cell23_1099171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_1099171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099171 prefixEnd_1099171 := by exact prefixLift 1099171
  have htrace : WordTrace (prefixWord ++ tailWord_1099171) baseStart_1099171 baseEnd_1099171 := by
    simpa [prefixWord, tailWord_1099171, baseEnd_1099171] using wordTrace_append hprefix tailTrace_1099171
  have hstable : (prefixWord ++ tailWord_1099171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099171).length < 2 ^ (prefixWord ++ tailWord_1099171).sum := by decide
  have hdescent : baseEnd_1099171 < baseStart_1099171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099180 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_1099180 : Nat := 118140960795 + 1099180 * 2 ^ 59
def prefixEnd_1099180 : Nat := 4983230072969 + 3 ^ 40 * 1099180 * 2
def baseEnd_1099180 : Nat := 564407665809114686894969

theorem tailTrace_1099180 : CollatzResearch.WordTrace tailWord_1099180 prefixEnd_1099180 564407665809114686894969 := by
  unfold tailWord_1099180
  simp only [CollatzResearch.WordTrace]
  refine ⟨20045194078933029921779497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26726925438577373229039329 20045194078933029921779497)
  ·
    refine ⟨15033895559199772441334623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20045194078933029921779497 15033895559199772441334623)
    ·
      refine ⟨22550843338799658662001935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15033895559199772441334623 22550843338799658662001935)
      ·
        refine ⟨33826265008199487993002903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22550843338799658662001935 33826265008199487993002903)
        ·
          refine ⟨50739397512299231989504355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33826265008199487993002903 50739397512299231989504355)
          ·
            refine ⟨76109096268448847984256533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50739397512299231989504355 76109096268448847984256533)
            ·
              refine ⟨3567613887583539749262025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76109096268448847984256533 3567613887583539749262025)
              ·
                refine ⟨2675710415687654811946519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3567613887583539749262025 2675710415687654811946519)
                ·
                  refine ⟨4013565623531482217919779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2675710415687654811946519 4013565623531482217919779)
                  ·
                    refine ⟨6020348435297223326879669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4013565623531482217919779 6020348435297223326879669)
                    ·
                      refine ⟨564407665809114686894969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6020348435297223326879669 564407665809114686894969)
                      ·
                        rfl

theorem cell23_1099180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_1099180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099180 prefixEnd_1099180 := by exact prefixLift 1099180
  have htrace : WordTrace (prefixWord ++ tailWord_1099180) baseStart_1099180 baseEnd_1099180 := by
    simpa [prefixWord, tailWord_1099180, baseEnd_1099180] using wordTrace_append hprefix tailTrace_1099180
  have hstable : (prefixWord ++ tailWord_1099180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099180).length < 2 ^ (prefixWord ++ tailWord_1099180).sum := by decide
  have hdescent : baseEnd_1099180 < baseStart_1099180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099197 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_1099197 : Nat := 118140960795 + 1099197 * 2 ^ 59
def prefixEnd_1099197 : Nat := 4983230072969 + 3 ^ 40 * 1099197 * 2
def baseEnd_1099197 : Nat := 564416394980241120382391

theorem tailTrace_1099197 : CollatzResearch.WordTrace tailWord_1099197 prefixEnd_1099197 564416394980241120382391 := by
  unfold tailWord_1099197
  simp only [CollatzResearch.WordTrace]
  refine ⟨40091008198804471746927845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26727338799202981164618563 40091008198804471746927845)
  ·
    refine ⟨7517064037275838452548971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40091008198804471746927845 7517064037275838452548971)
    ·
      refine ⟨11275596055913757678823457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517064037275838452548971 11275596055913757678823457)
      ·
        refine ⟨8456697041935318259117593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11275596055913757678823457 8456697041935318259117593)
        ·
          refine ⟨6342522781451488694338195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8456697041935318259117593 6342522781451488694338195)
          ·
            refine ⟨9513784172177233041507293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6342522781451488694338195 9513784172177233041507293)
            ·
              refine ⟨3567669064566462390565235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9513784172177233041507293 3567669064566462390565235)
              ·
                refine ⟨5351503596849693585847853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567669064566462390565235 5351503596849693585847853)
                ·
                  refine ⟨2006813848818635094692945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5351503596849693585847853 2006813848818635094692945)
                  ·
                    refine ⟨1505110386613976321019709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2006813848818635094692945 1505110386613976321019709)
                    ·
                      refine ⟨564416394980241120382391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1505110386613976321019709 564416394980241120382391)
                      ·
                        rfl

theorem cell23_1099197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_1099197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099197 prefixEnd_1099197 := by exact prefixLift 1099197
  have htrace : WordTrace (prefixWord ++ tailWord_1099197) baseStart_1099197 baseEnd_1099197 := by
    simpa [prefixWord, tailWord_1099197, baseEnd_1099197] using wordTrace_append hprefix tailTrace_1099197
  have hstable : (prefixWord ++ tailWord_1099197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099197).length < 2 ^ (prefixWord ++ tailWord_1099197).sum := by decide
  have hdescent : baseEnd_1099197 < baseStart_1099197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099262 : List Nat := [4, 2, 2, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1099262 : Nat := 118140960795 + 1099262 * 2 ^ 59
def prefixEnd_1099262 : Nat := 4983230072969 + 3 ^ 40 * 1099262 * 2
def baseEnd_1099262 : Nat := 564449771222783366069593

theorem tailTrace_1099262 : CollatzResearch.WordTrace tailWord_1099262 prefixEnd_1099262 564449771222783366069593 := by
  unfold tailWord_1099262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011672367946123481005505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26728919295712658565362693 5011672367946123481005505)
  ·
    refine ⟨3758754275959592610754129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5011672367946123481005505 3758754275959592610754129)
    ·
      refine ⟨2819065706969694458065597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3758754275959592610754129 2819065706969694458065597)
      ·
        refine ⟨1057149640113635421774599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2819065706969694458065597 1057149640113635421774599)
        ·
          refine ⟨1585724460170453132661899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057149640113635421774599 1585724460170453132661899)
          ·
            refine ⟨2378586690255679698992849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585724460170453132661899 2378586690255679698992849)
            ·
              refine ⟨1783940017691759774244637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2378586690255679698992849 1783940017691759774244637)
              ·
                refine ⟨668977506634409915341739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783940017691759774244637 668977506634409915341739)
                ·
                  refine ⟨1003466259951614873012609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668977506634409915341739 1003466259951614873012609)
                  ·
                    refine ⟨752599694963711154759457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1003466259951614873012609 752599694963711154759457)
                    ·
                      refine ⟨564449771222783366069593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752599694963711154759457 564449771222783366069593)
                      ·
                        rfl

theorem cell23_1099262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1099262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099262 prefixEnd_1099262 := by exact prefixLift 1099262
  have htrace : WordTrace (prefixWord ++ tailWord_1099262) baseStart_1099262 baseEnd_1099262 := by
    simpa [prefixWord, tailWord_1099262, baseEnd_1099262] using wordTrace_append hprefix tailTrace_1099262
  have hstable : (prefixWord ++ tailWord_1099262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099262).length < 2 ^ (prefixWord ++ tailWord_1099262).sum := by decide
  have hdescent : baseEnd_1099262 < baseStart_1099262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099267 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 3, 4, 2]
def baseStart_1099267 : Nat := 118140960795 + 1099267 * 2 ^ 59
def prefixEnd_1099267 : Nat := 4983230072969 + 3 ^ 40 * 1099267 * 2
def baseEnd_1099267 : Nat := 564452338626055846507069

theorem tailTrace_1099267 : CollatzResearch.WordTrace tailWord_1099267 prefixEnd_1099267 564452338626055846507069 := by
  unfold tailWord_1099267
  simp only [CollatzResearch.WordTrace]
  refine ⟨40093561308550873701976055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26729040872367249134650703 40093561308550873701976055)
  ·
    refine ⟨60140341962826310552964083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40093561308550873701976055 60140341962826310552964083)
    ·
      refine ⟨90210512944239465829446125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60140341962826310552964083 90210512944239465829446125)
      ·
        refine ⟨33828942354089799686042297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90210512944239465829446125 33828942354089799686042297)
        ·
          refine ⟨25371706765567349764531723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33828942354089799686042297 25371706765567349764531723)
          ·
            refine ⟨38057560148351024646797585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25371706765567349764531723 38057560148351024646797585)
            ·
              refine ⟨28543170111263268485098189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38057560148351024646797585 28543170111263268485098189)
              ·
                refine ⟨10703688791723725681911821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28543170111263268485098189 10703688791723725681911821)
                ·
                  refine ⟨4013883296896397130716933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10703688791723725681911821 4013883296896397130716933)
                  ·
                    refine ⟨752603118168074462009425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4013883296896397130716933 752603118168074462009425)
                    ·
                      refine ⟨564452338626055846507069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752603118168074462009425 564452338626055846507069)
                      ·
                        rfl

theorem cell23_1099267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_1099267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099267 prefixEnd_1099267 := by exact prefixLift 1099267
  have htrace : WordTrace (prefixWord ++ tailWord_1099267) baseStart_1099267 baseEnd_1099267 := by
    simpa [prefixWord, tailWord_1099267, baseEnd_1099267] using wordTrace_append hprefix tailTrace_1099267
  have hstable : (prefixWord ++ tailWord_1099267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099267).length < 2 ^ (prefixWord ++ tailWord_1099267).sum := by decide
  have hdescent : baseEnd_1099267 < baseStart_1099267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099271 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_1099271 : Nat := 118140960795 + 1099271 * 2 ^ 59
def prefixEnd_1099271 : Nat := 4983230072969 + 3 ^ 40 * 1099271 * 2
def baseEnd_1099271 : Nat := 564454392548673830857051

theorem tailTrace_1099271 : CollatzResearch.WordTrace tailWord_1099271 prefixEnd_1099271 564454392548673830857051 := by
  unfold tailWord_1099271
  simp only [CollatzResearch.WordTrace]
  refine ⟨40093707200536382385121667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26729138133690921590081111 40093707200536382385121667)
  ·
    refine ⟨60140560800804573577682501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40093707200536382385121667 60140560800804573577682501)
    ·
      refine ⟨11276355150150857545815469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60140560800804573577682501 11276355150150857545815469)
      ·
        refine ⟨4228633181306571579680801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11276355150150857545815469 4228633181306571579680801)
        ·
          refine ⟨3171474885979928684760601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4228633181306571579680801 3171474885979928684760601)
          ·
            refine ⟨2378606164484946513570451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3171474885979928684760601 2378606164484946513570451)
            ·
              refine ⟨3567909246727419770355677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378606164484946513570451 3567909246727419770355677)
              ·
                refine ⟨1337965967522782413883379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3567909246727419770355677 1337965967522782413883379)
                ·
                  refine ⟨2006948951284173620825069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337965967522782413883379 2006948951284173620825069)
                  ·
                    refine ⟨752605856731565107809401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006948951284173620825069 752605856731565107809401)
                    ·
                      refine ⟨564454392548673830857051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752605856731565107809401 564454392548673830857051)
                      ·
                        rfl

theorem cell23_1099271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_1099271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099271 prefixEnd_1099271 := by exact prefixLift 1099271
  have htrace : WordTrace (prefixWord ++ tailWord_1099271) baseStart_1099271 baseEnd_1099271 := by
    simpa [prefixWord, tailWord_1099271, baseEnd_1099271] using wordTrace_append hprefix tailTrace_1099271
  have hstable : (prefixWord ++ tailWord_1099271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099271).length < 2 ^ (prefixWord ++ tailWord_1099271).sum := by decide
  have hdescent : baseEnd_1099271 < baseStart_1099271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099278 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_1099278 : Nat := 118140960795 + 1099278 * 2 ^ 59
def prefixEnd_1099278 : Nat := 4983230072969 + 3 ^ 40 * 1099278 * 2
def baseEnd_1099278 : Nat := 564457986913255303469519

theorem tailTrace_1099278 : CollatzResearch.WordTrace tailWord_1099278 prefixEnd_1099278 564457986913255303469519 := by
  unfold tailWord_1099278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011745313938877822578311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26729308341007348387084325 5011745313938877822578311)
  ·
    refine ⟨7517617970908316733867467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5011745313938877822578311 7517617970908316733867467)
    ·
      refine ⟨11276426956362475100801201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517617970908316733867467 11276426956362475100801201)
      ·
        refine ⟨8457320217271856325600901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11276426956362475100801201 8457320217271856325600901)
        ·
          refine ⟨1585747540738473061050169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8457320217271856325600901 1585747540738473061050169)
          ·
            refine ⟨1189310655553854795787627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585747540738473061050169 1189310655553854795787627)
            ·
              refine ⟨1783965983330782193681441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189310655553854795787627 1783965983330782193681441)
              ·
                refine ⟨1337974487498086645261081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1783965983330782193681441 1337974487498086645261081)
                ·
                  refine ⟨1003480865623564983945811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1337974487498086645261081 1003480865623564983945811)
                  ·
                    refine ⟨1505221298435347475918717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1003480865623564983945811 1505221298435347475918717)
                    ·
                      refine ⟨564457986913255303469519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1505221298435347475918717 564457986913255303469519)
                      ·
                        rfl

theorem cell23_1099278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_1099278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099278 prefixEnd_1099278 := by exact prefixLift 1099278
  have htrace : WordTrace (prefixWord ++ tailWord_1099278) baseStart_1099278 baseEnd_1099278 := by
    simpa [prefixWord, tailWord_1099278, baseEnd_1099278] using wordTrace_append hprefix tailTrace_1099278
  have hstable : (prefixWord ++ tailWord_1099278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099278).length < 2 ^ (prefixWord ++ tailWord_1099278).sum := by decide
  have hdescent : baseEnd_1099278 < baseStart_1099278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099297 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1099297 : Nat := 118140960795 + 1099297 * 2 ^ 59
def prefixEnd_1099297 : Nat := 4983230072969 + 3 ^ 40 * 1099297 * 2
def baseEnd_1099297 : Nat := 564467743045690729131931

theorem tailTrace_1099297 : CollatzResearch.WordTrace tailWord_1099297 prefixEnd_1099297 564467743045690729131931 := by
  unfold tailWord_1099297
  simp only [CollatzResearch.WordTrace]
  refine ⟨40094655498442188825568145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26729770332294792550378763 40094655498442188825568145)
  ·
    refine ⟨30070991623831641619176109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40094655498442188825568145 30070991623831641619176109)
    ·
      refine ⟨11276621858936865607191041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30070991623831641619176109 11276621858936865607191041)
      ·
        refine ⟨8457466394202649205393281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11276621858936865607191041 8457466394202649205393281)
        ·
          refine ⟨6343099795651986904044961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8457466394202649205393281 6343099795651986904044961)
          ·
            refine ⟨4757324846738990178033721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6343099795651986904044961 4757324846738990178033721)
            ·
              refine ⟨3567993635054242633525291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4757324846738990178033721 3567993635054242633525291)
              ·
                refine ⟨5351990452581363950287937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567993635054242633525291 5351990452581363950287937)
                ·
                  refine ⟨4013992839436022962715953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5351990452581363950287937 4013992839436022962715953)
                  ·
                    refine ⟨3010494629577017222036965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4013992839436022962715953 3010494629577017222036965)
                    ·
                      refine ⟨564467743045690729131931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3010494629577017222036965 564467743045690729131931)
                      ·
                        rfl

theorem cell23_1099297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1099297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099297 prefixEnd_1099297 := by exact prefixLift 1099297
  have htrace : WordTrace (prefixWord ++ tailWord_1099297) baseStart_1099297 baseEnd_1099297 := by
    simpa [prefixWord, tailWord_1099297, baseEnd_1099297] using wordTrace_append hprefix tailTrace_1099297
  have hstable : (prefixWord ++ tailWord_1099297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099297).length < 2 ^ (prefixWord ++ tailWord_1099297).sum := by decide
  have hdescent : baseEnd_1099297 < baseStart_1099297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099341 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1099341 : Nat := 118140960795 + 1099341 * 2 ^ 59
def prefixEnd_1099341 : Nat := 4983230072969 + 3 ^ 40 * 1099341 * 2
def baseEnd_1099341 : Nat := 62721148466054284109081

theorem tailTrace_1099341 : CollatzResearch.WordTrace tailWord_1099341 prefixEnd_1099341 62721148466054284109081 := by
  unfold tailWord_1099341
  simp only [CollatzResearch.WordTrace]
  refine ⟨40096260310282784340169877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26730840206855189560113251 40096260310282784340169877)
  ·
    refine ⟨1879512202044505515945463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40096260310282784340169877 1879512202044505515945463)
    ·
      refine ⟨2819268303066758273918195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879512202044505515945463 2819268303066758273918195)
      ·
        refine ⟨4228902454600137410877293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819268303066758273918195 4228902454600137410877293)
        ·
          refine ⟨1585838420475051529078985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4228902454600137410877293 1585838420475051529078985)
          ·
            refine ⟨1189378815356288646809239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585838420475051529078985 1189378815356288646809239)
            ·
              refine ⟨1784068223034432970213859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189378815356288646809239 1784068223034432970213859)
              ·
                refine ⟨2676102334551649455320789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784068223034432970213859 2676102334551649455320789)
                ·
                  refine ⟨62721148466054284109081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2676102334551649455320789 62721148466054284109081)
                  ·
                    rfl

theorem cell23_1099341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1099341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099341 prefixEnd_1099341 := by exact prefixLift 1099341
  have htrace : WordTrace (prefixWord ++ tailWord_1099341) baseStart_1099341 baseEnd_1099341 := by
    simpa [prefixWord, tailWord_1099341, baseEnd_1099341] using wordTrace_append hprefix tailTrace_1099341
  have hstable : (prefixWord ++ tailWord_1099341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099341).length < 2 ^ (prefixWord ++ tailWord_1099341).sum := by decide
  have hdescent : baseEnd_1099341 < baseStart_1099341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099377 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_1099377 : Nat := 118140960795 + 1099377 * 2 ^ 59
def prefixEnd_1099377 : Nat := 4983230072969 + 3 ^ 40 * 1099377 * 2
def baseEnd_1099377 : Nat := 564508821498050416131563

theorem tailTrace_1099377 : CollatzResearch.WordTrace tailWord_1099377 prefixEnd_1099377 564508821498050416131563 := by
  unfold tailWord_1099377
  simp only [CollatzResearch.WordTrace]
  refine ⟨40097573338152362488480385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26731715558768241658986923 40097573338152362488480385)
  ·
    refine ⟨30073180003614271866360289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40097573338152362488480385 30073180003614271866360289)
    ·
      refine ⟨22554885002710703899770217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30073180003614271866360289 22554885002710703899770217)
      ·
        refine ⟨16916163752033027924827663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22554885002710703899770217 16916163752033027924827663)
        ·
          refine ⟨25374245628049541887241495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16916163752033027924827663 25374245628049541887241495)
          ·
            refine ⟨38061368442074312830862243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25374245628049541887241495 38061368442074312830862243)
            ·
              refine ⟨57092052663111469246293365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38061368442074312830862243 57092052663111469246293365)
              ·
                refine ⟨5352379937166700241840003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57092052663111469246293365 5352379937166700241840003)
                ·
                  refine ⟨8028569905750050362760005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352379937166700241840003 8028569905750050362760005)
                  ·
                    refine ⟨1505356857328134443017501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8028569905750050362760005 1505356857328134443017501)
                    ·
                      refine ⟨564508821498050416131563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1505356857328134443017501 564508821498050416131563)
                      ·
                        rfl

theorem cell23_1099377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_1099377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099377 prefixEnd_1099377 := by exact prefixLift 1099377
  have htrace : WordTrace (prefixWord ++ tailWord_1099377) baseStart_1099377 baseEnd_1099377 := by
    simpa [prefixWord, tailWord_1099377, baseEnd_1099377] using wordTrace_append hprefix tailTrace_1099377
  have hstable : (prefixWord ++ tailWord_1099377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099377).length < 2 ^ (prefixWord ++ tailWord_1099377).sum := by decide
  have hdescent : baseEnd_1099377 < baseStart_1099377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099427 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 3, 5]
def baseStart_1099427 : Nat := 118140960795 + 1099427 * 2 ^ 59
def prefixEnd_1099427 : Nat := 4983230072969 + 3 ^ 40 * 1099427 * 2
def baseEnd_1099427 : Nat := 188178165176925073502111

theorem tailTrace_1099427 : CollatzResearch.WordTrace tailWord_1099427 prefixEnd_1099427 188178165176925073502111 := by
  unfold tailWord_1099427
  simp only [CollatzResearch.WordTrace]
  refine ⟨40099396987971221027800535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26732931325314147351867023 40099396987971221027800535)
  ·
    refine ⟨60149095481956831541700803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40099396987971221027800535 60149095481956831541700803)
    ·
      refine ⟨90223643222935247312551205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60149095481956831541700803 90223643222935247312551205)
      ·
        refine ⟨16916933104300358871103351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90223643222935247312551205 16916933104300358871103351)
        ·
          refine ⟨25375399656450538306655027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16916933104300358871103351 25375399656450538306655027)
          ·
            refine ⟨38063099484675807459982541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25375399656450538306655027 38063099484675807459982541)
            ·
              refine ⟨14273662306753427797493453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38063099484675807459982541 14273662306753427797493453)
              ·
                refine ⟨5352623365032535424060045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14273662306753427797493453 5352623365032535424060045)
                ·
                  refine ⟨2007233761887200784022517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5352623365032535424060045 2007233761887200784022517)
                  ·
                    refine ⟨188178165176925073502111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2007233761887200784022517 188178165176925073502111)
                    ·
                      rfl

theorem cell23_1099427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 5].length) (baseStart_1099427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099427 prefixEnd_1099427 := by exact prefixLift 1099427
  have htrace : WordTrace (prefixWord ++ tailWord_1099427) baseStart_1099427 baseEnd_1099427 := by
    simpa [prefixWord, tailWord_1099427, baseEnd_1099427] using wordTrace_append hprefix tailTrace_1099427
  have hstable : (prefixWord ++ tailWord_1099427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099427).length < 2 ^ (prefixWord ++ tailWord_1099427).sum := by decide
  have hdescent : baseEnd_1099427 < baseStart_1099427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099481 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 4]
def baseStart_1099481 : Nat := 118140960795 + 1099481 * 2 ^ 59
def prefixEnd_1099481 : Nat := 4983230072969 + 3 ^ 40 * 1099481 * 2
def baseEnd_1099481 : Nat := 564562223486118009231085

theorem tailTrace_1099481 : CollatzResearch.WordTrace tailWord_1099481 prefixEnd_1099481 564562223486118009231085 := by
  unfold tailWord_1099481
  simp only [CollatzResearch.WordTrace]
  refine ⟨40101366529775588250266297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26734244353183725500177531 40101366529775588250266297)
  ·
    refine ⟨30076024897331691187699723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40101366529775588250266297 30076024897331691187699723)
    ·
      refine ⟨45114037345997536781549585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30076024897331691187699723 45114037345997536781549585)
      ·
        refine ⟨33835528009498152586162189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45114037345997536781549585 33835528009498152586162189)
        ·
          refine ⟨12688323003561807219810821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33835528009498152586162189 12688323003561807219810821)
          ·
            refine ⟨2379060563167838853714529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12688323003561807219810821 2379060563167838853714529)
            ·
              refine ⟨1784295422375879140285897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379060563167838853714529 1784295422375879140285897)
              ·
                refine ⟨1338221566781909355214423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784295422375879140285897 1338221566781909355214423)
                ·
                  refine ⟨2007332350172864032821635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338221566781909355214423 2007332350172864032821635)
                  ·
                    refine ⟨3010998525259296049232453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2007332350172864032821635 3010998525259296049232453)
                    ·
                      refine ⟨564562223486118009231085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3010998525259296049232453 564562223486118009231085)
                      ·
                        rfl

theorem cell23_1099481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_1099481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099481 prefixEnd_1099481 := by exact prefixLift 1099481
  have htrace : WordTrace (prefixWord ++ tailWord_1099481) baseStart_1099481 baseEnd_1099481 := by
    simpa [prefixWord, tailWord_1099481, baseEnd_1099481] using wordTrace_append hprefix tailTrace_1099481
  have hstable : (prefixWord ++ tailWord_1099481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099481).length < 2 ^ (prefixWord ++ tailWord_1099481).sum := by decide
  have hdescent : baseEnd_1099481 < baseStart_1099481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099487 : List Nat := [1, 1, 2, 3, 2, 2, 3, 9]
def baseStart_1099487 : Nat := 118140960795 + 1099487 * 2 ^ 59
def prefixEnd_1099487 : Nat := 4983230072969 + 3 ^ 40 * 1099487 * 2
def baseEnd_1099487 : Nat := 20909826087779443916891

theorem tailTrace_1099487 : CollatzResearch.WordTrace tailWord_1099487 prefixEnd_1099487 20909826087779443916891 := by
  unfold tailWord_1099487
  simp only [CollatzResearch.WordTrace]
  refine ⟨40101585367753851274984715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26734390245169234183323143 40101585367753851274984715)
  ·
    refine ⟨60152378051630776912477073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40101585367753851274984715 60152378051630776912477073)
    ·
      refine ⟨45114283538723082684357805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60152378051630776912477073 45114283538723082684357805)
      ·
        refine ⟨16917856327021156006634177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45114283538723082684357805 16917856327021156006634177)
        ·
          refine ⟨12688392245265867004975633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16917856327021156006634177 12688392245265867004975633)
          ·
            refine ⟨9516294183949400253731725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12688392245265867004975633 9516294183949400253731725)
            ·
              refine ⟨3568610318981025095149397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9516294183949400253731725 3568610318981025095149397)
              ·
                refine ⟨20909826087779443916891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3568610318981025095149397 20909826087779443916891)
                ·
                  rfl

theorem cell23_1099487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 9].length) (baseStart_1099487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099487 prefixEnd_1099487 := by exact prefixLift 1099487
  have htrace : WordTrace (prefixWord ++ tailWord_1099487) baseStart_1099487 baseEnd_1099487 := by
    simpa [prefixWord, tailWord_1099487, baseEnd_1099487] using wordTrace_append hprefix tailTrace_1099487
  have hstable : (prefixWord ++ tailWord_1099487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099487).length < 2 ^ (prefixWord ++ tailWord_1099487).sum := by decide
  have hdescent : baseEnd_1099487 < baseStart_1099487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099501 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1099501 : Nat := 118140960795 + 1099501 * 2 ^ 59
def prefixEnd_1099501 : Nat := 4983230072969 + 3 ^ 40 * 1099501 * 2
def baseEnd_1099501 : Nat := 564572493099207930980993

theorem tailTrace_1099501 : CollatzResearch.WordTrace tailWord_1099501 prefixEnd_1099501 564572493099207930980993 := by
  unfold tailWord_1099501
  simp only [CollatzResearch.WordTrace]
  refine ⟨40102095989703131665994357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26734730659802087777329571 40102095989703131665994357)
  ·
    refine ⟨3759571499034668593686971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40102095989703131665994357 3759571499034668593686971)
    ·
      refine ⟨5639357248552002890530457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3759571499034668593686971 5639357248552002890530457)
      ·
        refine ⟨4229517936414002167897843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5639357248552002890530457 4229517936414002167897843)
        ·
          refine ⟨6344276904621003251846765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4229517936414002167897843 6344276904621003251846765)
          ·
            refine ⟨2379103839232876219442537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6344276904621003251846765 2379103839232876219442537)
            ·
              refine ⟨1784327879424657164581903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379103839232876219442537 1784327879424657164581903)
              ·
                refine ⟨2676491819136985746872855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784327879424657164581903 2676491819136985746872855)
                ·
                  refine ⟨4014737728705478620309283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676491819136985746872855 4014737728705478620309283)
                  ·
                    refine ⟨6022106593058217930463925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4014737728705478620309283 6022106593058217930463925)
                    ·
                      refine ⟨564572493099207930980993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6022106593058217930463925 564572493099207930980993)
                      ·
                        rfl

theorem cell23_1099501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1099501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099501 prefixEnd_1099501 := by exact prefixLift 1099501
  have htrace : WordTrace (prefixWord ++ tailWord_1099501) baseStart_1099501 baseEnd_1099501 := by
    simpa [prefixWord, tailWord_1099501, baseEnd_1099501] using wordTrace_append hprefix tailTrace_1099501
  have hstable : (prefixWord ++ tailWord_1099501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099501).length < 2 ^ (prefixWord ++ tailWord_1099501).sum := by decide
  have hdescent : baseEnd_1099501 < baseStart_1099501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099537 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_1099537 : Nat := 118140960795 + 1099537 * 2 ^ 59
def prefixEnd_1099537 : Nat := 4983230072969 + 3 ^ 40 * 1099537 * 2
def baseEnd_1099537 : Nat := 564590978402769790130827

theorem tailTrace_1099537 : CollatzResearch.WordTrace tailWord_1099537 prefixEnd_1099537 564590978402769790130827 := by
  unfold tailWord_1099537
  simp only [CollatzResearch.WordTrace]
  refine ⟨40103409017572709814304865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26735606011715139876203243 40103409017572709814304865)
  ·
    refine ⟨30077556763179532360728649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40103409017572709814304865 30077556763179532360728649)
    ·
      refine ⟨22558167572384649270546487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30077556763179532360728649 22558167572384649270546487)
      ·
        refine ⟨33837251358576973905819731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22558167572384649270546487 33837251358576973905819731)
        ·
          refine ⟨50755877037865460858729597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33837251358576973905819731 50755877037865460858729597)
          ·
            refine ⟨19033453889199547822023599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50755877037865460858729597 19033453889199547822023599)
            ·
              refine ⟨28550180833799321733035399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19033453889199547822023599 28550180833799321733035399)
              ·
                refine ⟨42825271250698982599553099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28550180833799321733035399 42825271250698982599553099)
                ·
                  refine ⟨64237906876048473899329649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42825271250698982599553099 64237906876048473899329649)
                  ·
                    refine ⟨48178430157036355424497237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64237906876048473899329649 48178430157036355424497237)
                    ·
                      refine ⟨564590978402769790130827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 48178430157036355424497237 564590978402769790130827)
                      ·
                        rfl

theorem cell23_1099537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_1099537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099537 prefixEnd_1099537 := by exact prefixLift 1099537
  have htrace : WordTrace (prefixWord ++ tailWord_1099537) baseStart_1099537 baseEnd_1099537 := by
    simpa [prefixWord, tailWord_1099537, baseEnd_1099537] using wordTrace_append hprefix tailTrace_1099537
  have hstable : (prefixWord ++ tailWord_1099537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099537).length < 2 ^ (prefixWord ++ tailWord_1099537).sum := by decide
  have hdescent : baseEnd_1099537 < baseStart_1099537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099547 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 1, 8]
def baseStart_1099547 : Nat := 118140960795 + 1099547 * 2 ^ 59
def prefixEnd_1099547 : Nat := 4983230072969 + 3 ^ 40 * 1099547 * 2
def baseEnd_1099547 : Nat := 188198704403104917001927

theorem tailTrace_1099547 : CollatzResearch.WordTrace tailWord_1099547 prefixEnd_1099547 188198704403104917001927 := by
  unfold tailWord_1099547
  simp only [CollatzResearch.WordTrace]
  refine ⟨40103773747536481522168895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26735849165024321014779263 40103773747536481522168895)
  ·
    refine ⟨60155660621304722283253343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40103773747536481522168895 60155660621304722283253343)
    ·
      refine ⟨90233490931957083424880015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60155660621304722283253343 90233490931957083424880015)
      ·
        refine ⟨135350236397935625137320023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90233490931957083424880015 135350236397935625137320023)
        ·
          refine ⟨203025354596903437705980035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135350236397935625137320023 203025354596903437705980035)
          ·
            refine ⟨304538031895355156558970053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203025354596903437705980035 304538031895355156558970053)
            ·
              refine ⟨57100880980379091854806885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304538031895355156558970053 57100880980379091854806885)
              ·
                refine ⟨10706415183821079722776291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57100880980379091854806885 10706415183821079722776291)
                ·
                  refine ⟨16059622775731619584164437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10706415183821079722776291 16059622775731619584164437)
                  ·
                    refine ⟨188198704403104917001927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16059622775731619584164437 188198704403104917001927)
                    ·
                      rfl

theorem cell23_1099547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_1099547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099547 prefixEnd_1099547 := by exact prefixLift 1099547
  have htrace : WordTrace (prefixWord ++ tailWord_1099547) baseStart_1099547 baseEnd_1099547 := by
    simpa [prefixWord, tailWord_1099547, baseEnd_1099547] using wordTrace_append hprefix tailTrace_1099547
  have hstable : (prefixWord ++ tailWord_1099547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099547).length < 2 ^ (prefixWord ++ tailWord_1099547).sum := by decide
  have hdescent : baseEnd_1099547 < baseStart_1099547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099566 : List Nat := [4, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1099566 : Nat := 118140960795 + 1099566 * 2 ^ 59
def prefixEnd_1099566 : Nat := 4983230072969 + 3 ^ 40 * 1099566 * 2
def baseEnd_1099566 : Nat := 564605869341750176668195

theorem tailTrace_1099566 : CollatzResearch.WordTrace tailWord_1099566 prefixEnd_1099566 564605869341750176668195 := by
  unfold tailWord_1099566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013058341808455970888819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26736311156311765178073701 5013058341808455970888819)
  ·
    refine ⟨7519587512712683956333229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5013058341808455970888819 7519587512712683956333229)
    ·
      refine ⟨2819845317267256483624961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7519587512712683956333229 2819845317267256483624961)
      ·
        refine ⟨2114883987950442362718721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2819845317267256483624961 2114883987950442362718721)
        ·
          refine ⟨1586162990962831772039041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2114883987950442362718721 1586162990962831772039041)
          ·
            refine ⟨1189622243222123829029281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1586162990962831772039041 1189622243222123829029281)
            ·
              refine ⟨892216682416592871771961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189622243222123829029281 892216682416592871771961)
              ·
                refine ⟨669162511812444653828971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892216682416592871771961 669162511812444653828971)
                ·
                  refine ⟨1003743767718666980743457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669162511812444653828971 1003743767718666980743457)
                  ·
                    refine ⟨752807825789000235557593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1003743767718666980743457 752807825789000235557593)
                    ·
                      refine ⟨564605869341750176668195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752807825789000235557593 564605869341750176668195)
                      ·
                        rfl

theorem cell23_1099566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1099566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099566 prefixEnd_1099566 := by exact prefixLift 1099566
  have htrace : WordTrace (prefixWord ++ tailWord_1099566) baseStart_1099566 baseEnd_1099566 := by
    simpa [prefixWord, tailWord_1099566, baseEnd_1099566] using wordTrace_append hprefix tailTrace_1099566
  have hstable : (prefixWord ++ tailWord_1099566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099566).length < 2 ^ (prefixWord ++ tailWord_1099566).sum := by decide
  have hdescent : baseEnd_1099566 < baseStart_1099566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099581 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_1099581 : Nat := 118140960795 + 1099581 * 2 ^ 59
def prefixEnd_1099581 : Nat := 4983230072969 + 3 ^ 40 * 1099581 * 2
def baseEnd_1099581 : Nat := 188204523850522539326875

theorem tailTrace_1099581 : CollatzResearch.WordTrace tailWord_1099581 prefixEnd_1099581 188204523850522539326875 := by
  unfold tailWord_1099581
  simp only [CollatzResearch.WordTrace]
  refine ⟨40105013829413305328906597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26736675886275536885937731 40105013829413305328906597)
  ·
    refine ⟨7519690093014994749169987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40105013829413305328906597 7519690093014994749169987)
    ·
      refine ⟨11279535139522492123754981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7519690093014994749169987 11279535139522492123754981)
      ·
        refine ⟨2114912838660467273204059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11279535139522492123754981 2114912838660467273204059)
        ·
          refine ⟨3172369257990700909806089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114912838660467273204059 3172369257990700909806089)
          ·
            refine ⟨2379276943493025682354567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3172369257990700909806089 2379276943493025682354567)
            ·
              refine ⟨3568915415239538523531851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379276943493025682354567 3568915415239538523531851)
              ·
                refine ⟨5353373122859307785297777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3568915415239538523531851 5353373122859307785297777)
                ·
                  refine ⟨4015029842144480838973333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5353373122859307785297777 4015029842144480838973333)
                  ·
                    refine ⟨188204523850522539326875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4015029842144480838973333 188204523850522539326875)
                    ·
                      rfl

theorem cell23_1099581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_1099581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099581 prefixEnd_1099581 := by exact prefixLift 1099581
  have htrace : WordTrace (prefixWord ++ tailWord_1099581) baseStart_1099581 baseEnd_1099581 := by
    simpa [prefixWord, tailWord_1099581, baseEnd_1099581] using wordTrace_append hprefix tailTrace_1099581
  have hstable : (prefixWord ++ tailWord_1099581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099581).length < 2 ^ (prefixWord ++ tailWord_1099581).sum := by decide
  have hdescent : baseEnd_1099581 < baseStart_1099581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099594 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 7]
def baseStart_1099594 : Nat := 118140960795 + 1099594 * 2 ^ 59
def prefixEnd_1099594 : Nat := 4983230072969 + 3 ^ 40 * 1099594 * 2
def baseEnd_1099594 : Nat := 62735582977786229679785

theorem tailTrace_1099594 : CollatzResearch.WordTrace tailWord_1099594 prefixEnd_1099594 62735582977786229679785 := by
  unfold tailWord_1099594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10026371994591552137282459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26736991985577472366086557 10026371994591552137282459)
  ·
    refine ⟨15039557991887328205923689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10026371994591552137282459 15039557991887328205923689)
    ·
      refine ⟨11279668493915496154442767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15039557991887328205923689 11279668493915496154442767)
      ·
        refine ⟨16919502740873244231664151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11279668493915496154442767 16919502740873244231664151)
        ·
          refine ⟨25379254111309866347496227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16919502740873244231664151 25379254111309866347496227)
          ·
            refine ⟨38068881166964799521244341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25379254111309866347496227 38068881166964799521244341)
            ·
              refine ⟨3568957609402949955116657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38068881166964799521244341 3568957609402949955116657)
              ·
                refine ⟨2676718207052212466337493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3568957609402949955116657 2676718207052212466337493)
                ·
                  refine ⟨62735582977786229679785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2676718207052212466337493 62735582977786229679785)
                  ·
                    rfl

theorem cell23_1099594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_1099594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099594 prefixEnd_1099594 := by exact prefixLift 1099594
  have htrace : WordTrace (prefixWord ++ tailWord_1099594) baseStart_1099594 baseEnd_1099594 := by
    simpa [prefixWord, tailWord_1099594, baseEnd_1099594] using wordTrace_append hprefix tailTrace_1099594
  have hstable : (prefixWord ++ tailWord_1099594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099594).length < 2 ^ (prefixWord ++ tailWord_1099594).sum := by decide
  have hdescent : baseEnd_1099594 < baseStart_1099594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099634 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1099634 : Nat := 118140960795 + 1099634 * 2 ^ 59
def prefixEnd_1099634 : Nat := 4983230072969 + 3 ^ 40 * 1099634 * 2
def baseEnd_1099634 : Nat := 564640786026255910617881

theorem tailTrace_1099634 : CollatzResearch.WordTrace tailWord_1099634 prefixEnd_1099634 564640786026255910617881 := by
  unfold tailWord_1099634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10026736724555323845146489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26737964598814196920390637 10026736724555323845146489)
  ·
    refine ⟨7520052543416492883859867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10026736724555323845146489 7520052543416492883859867)
    ·
      refine ⟨11280078815124739325789801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520052543416492883859867 11280078815124739325789801)
      ·
        refine ⟨8460059111343554494342351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11280078815124739325789801 8460059111343554494342351)
        ·
          refine ⟨12690088667015331741513527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8460059111343554494342351 12690088667015331741513527)
          ·
            refine ⟨19035133000522997612270291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12690088667015331741513527 19035133000522997612270291)
            ·
              refine ⟨28552699500784496418405437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19035133000522997612270291 28552699500784496418405437)
              ·
                refine ⟨10707262312794186156902039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28552699500784496418405437 10707262312794186156902039)
                ·
                  refine ⟨16060893469191279235353059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10707262312794186156902039 16060893469191279235353059)
                  ·
                    refine ⟨24091340203786918853029589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16060893469191279235353059 24091340203786918853029589)
                    ·
                      refine ⟨564640786026255910617881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24091340203786918853029589 564640786026255910617881)
                      ·
                        rfl

theorem cell23_1099634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1099634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099634 prefixEnd_1099634 := by exact prefixLift 1099634
  have htrace : WordTrace (prefixWord ++ tailWord_1099634) baseStart_1099634 baseEnd_1099634 := by
    simpa [prefixWord, tailWord_1099634, baseEnd_1099634] using wordTrace_append hprefix tailTrace_1099634
  have hstable : (prefixWord ++ tailWord_1099634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099634).length < 2 ^ (prefixWord ++ tailWord_1099634).sum := by decide
  have hdescent : baseEnd_1099634 < baseStart_1099634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099662 : List Nat := [4, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_1099662 : Nat := 118140960795 + 1099662 * 2 ^ 59
def prefixEnd_1099662 : Nat := 4983230072969 + 3 ^ 40 * 1099662 * 2
def baseEnd_1099662 : Nat := 62739462609397977896417

theorem tailTrace_1099662 : CollatzResearch.WordTrace tailWord_1099662 prefixEnd_1099662 62739462609397977896417 := by
  unfold tailWord_1099662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013496017764982020325655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26738645428079904108403493 5013496017764982020325655)
  ·
    refine ⟨7520244026647473030488483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5013496017764982020325655 7520244026647473030488483)
    ·
      refine ⟨11280366039971209545732725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520244026647473030488483 11280366039971209545732725)
      ·
        refine ⟨1057534316247300894912443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11280366039971209545732725 1057534316247300894912443)
        ·
          refine ⟨1586301474370951342368665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057534316247300894912443 1586301474370951342368665)
          ·
            refine ⟨1189726105778213506776499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1586301474370951342368665 1189726105778213506776499)
            ·
              refine ⟨1784589158667320260164749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189726105778213506776499 1784589158667320260164749)
              ·
                refine ⟨669220934500245097561781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1784589158667320260164749 669220934500245097561781)
                ·
                  refine ⟨62739462609397977896417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 669220934500245097561781 62739462609397977896417)
                  ·
                    rfl

theorem cell23_1099662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_1099662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099662 prefixEnd_1099662 := by exact prefixLift 1099662
  have htrace : WordTrace (prefixWord ++ tailWord_1099662) baseStart_1099662 baseEnd_1099662 := by
    simpa [prefixWord, tailWord_1099662, baseEnd_1099662] using wordTrace_append hprefix tailTrace_1099662
  have hstable : (prefixWord ++ tailWord_1099662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099662).length < 2 ^ (prefixWord ++ tailWord_1099662).sum := by decide
  have hdescent : baseEnd_1099662 < baseStart_1099662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099802 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2]
def baseStart_1099802 : Nat := 118140960795 + 1099802 * 2 ^ 59
def prefixEnd_1099802 : Nat := 4983230072969 + 3 ^ 40 * 1099802 * 2
def baseEnd_1099802 : Nat := 564727050776211253317109

theorem tailTrace_1099802 : CollatzResearch.WordTrace tailWord_1099802 prefixEnd_1099802 564727050776211253317109 := by
  unfold tailWord_1099802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10028268590403165018175415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26742049574408440048467773 10028268590403165018175415)
  ·
    refine ⟨15042402885604747527263123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10028268590403165018175415 15042402885604747527263123)
    ·
      refine ⟨22563604328407121290894685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15042402885604747527263123 22563604328407121290894685)
      ·
        refine ⟨8461351623152670484085507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22563604328407121290894685 8461351623152670484085507)
        ·
          refine ⟨12692027434729005726128261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8461351623152670484085507 12692027434729005726128261)
          ·
            refine ⟨2379755144011688573649049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12692027434729005726128261 2379755144011688573649049)
            ·
              refine ⟨1784816358008766430236787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379755144011688573649049 1784816358008766430236787)
              ·
                refine ⟨2677224537013149645355181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784816358008766430236787 2677224537013149645355181)
                ·
                  refine ⟨1003959201379931117008193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2677224537013149645355181 1003959201379931117008193)
                  ·
                    refine ⟨752969401034948337756145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1003959201379931117008193 752969401034948337756145)
                    ·
                      refine ⟨564727050776211253317109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 752969401034948337756145 564727050776211253317109)
                      ·
                        rfl

theorem cell23_1099802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_1099802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099802 prefixEnd_1099802 := by exact prefixLift 1099802
  have htrace : WordTrace (prefixWord ++ tailWord_1099802) baseStart_1099802 baseEnd_1099802 := by
    simpa [prefixWord, tailWord_1099802, baseEnd_1099802] using wordTrace_append hprefix tailTrace_1099802
  have hstable : (prefixWord ++ tailWord_1099802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099802).length < 2 ^ (prefixWord ++ tailWord_1099802).sum := by decide
  have hdescent : baseEnd_1099802 < baseStart_1099802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099812 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_1099812 : Nat := 118140960795 + 1099812 * 2 ^ 59
def prefixEnd_1099812 : Nat := 4983230072969 + 3 ^ 40 * 1099812 * 2
def baseEnd_1099812 : Nat := 188244061860918738064021

theorem tailTrace_1099812 : CollatzResearch.WordTrace tailWord_1099812 prefixEnd_1099812 188244061860918738064021 := by
  unfold tailWord_1099812
  simp only [CollatzResearch.WordTrace]
  refine ⟨20056719545788215890282845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26742292727717621187043793 20056719545788215890282845)
  ·
    refine ⟨7521269829670580958856067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20056719545788215890282845 7521269829670580958856067)
    ·
      refine ⟨11281904744505871438284101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7521269829670580958856067 11281904744505871438284101)
      ·
        refine ⟨2115357139594850894678269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11281904744505871438284101 2115357139594850894678269)
        ·
          refine ⟨793258927348069085504351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2115357139594850894678269 793258927348069085504351)
          ·
            refine ⟨1189888391022103628256527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793258927348069085504351 1189888391022103628256527)
            ·
              refine ⟨1784832586533155442384791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189888391022103628256527 1784832586533155442384791)
              ·
                refine ⟨2677248879799733163577187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784832586533155442384791 2677248879799733163577187)
                ·
                  refine ⟨4015873319699599745365781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677248879799733163577187 4015873319699599745365781)
                  ·
                    refine ⟨188244061860918738064021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4015873319699599745365781 188244061860918738064021)
                    ·
                      rfl

theorem cell23_1099812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_1099812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099812 prefixEnd_1099812 := by exact prefixLift 1099812
  have htrace : WordTrace (prefixWord ++ tailWord_1099812) baseStart_1099812 baseEnd_1099812 := by
    simpa [prefixWord, tailWord_1099812, baseEnd_1099812] using wordTrace_append hprefix tailTrace_1099812
  have hstable : (prefixWord ++ tailWord_1099812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099812).length < 2 ^ (prefixWord ++ tailWord_1099812).sum := by decide
  have hdescent : baseEnd_1099812 < baseStart_1099812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099815 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1099815 : Nat := 118140960795 + 1099815 * 2 ^ 59
def prefixEnd_1099815 : Nat := 4983230072969 + 3 ^ 40 * 1099815 * 2
def baseEnd_1099815 : Nat := 564733726024719702454549

theorem tailTrace_1099815 : CollatzResearch.WordTrace tailWord_1099815 prefixEnd_1099815 564733726024719702454549 := by
  unfold tailWord_1099815
  simp only [CollatzResearch.WordTrace]
  refine ⟨40113548510565563292924899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26742365673710375528616599 40113548510565563292924899)
  ·
    refine ⟨60170322765848344939387349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40113548510565563292924899 60170322765848344939387349)
    ·
      refine ⟨1410241939824570584516891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 60170322765848344939387349 1410241939824570584516891)
      ·
        refine ⟨2115362909736855876775337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410241939824570584516891 2115362909736855876775337)
        ·
          refine ⟨1586522182302641907581503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115362909736855876775337 1586522182302641907581503)
          ·
            refine ⟨2379783273453962861372255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586522182302641907581503 2379783273453962861372255)
            ·
              refine ⟨3569674910180944292058383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379783273453962861372255 3569674910180944292058383)
              ·
                refine ⟨5354512365271416438087575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569674910180944292058383 5354512365271416438087575)
                ·
                  refine ⟨8031768547907124657131363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354512365271416438087575 8031768547907124657131363)
                  ·
                    refine ⟨12047652821860686985697045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8031768547907124657131363 12047652821860686985697045)
                    ·
                      refine ⟨564733726024719702454549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12047652821860686985697045 564733726024719702454549)
                      ·
                        rfl

theorem cell23_1099815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1099815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099815 prefixEnd_1099815 := by exact prefixLift 1099815
  have htrace : WordTrace (prefixWord ++ tailWord_1099815) baseStart_1099815 baseEnd_1099815 := by
    simpa [prefixWord, tailWord_1099815, baseEnd_1099815] using wordTrace_append hprefix tailTrace_1099815
  have hstable : (prefixWord ++ tailWord_1099815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099815).length < 2 ^ (prefixWord ++ tailWord_1099815).sum := by decide
  have hdescent : baseEnd_1099815 < baseStart_1099815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099822 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1099822 : Nat := 118140960795 + 1099822 * 2 ^ 59
def prefixEnd_1099822 : Nat := 4983230072969 + 3 ^ 40 * 1099822 * 2
def baseEnd_1099822 : Nat := 564737320389301175067017

theorem tailTrace_1099822 : CollatzResearch.WordTrace tailWord_1099822 prefixEnd_1099822 564737320389301175067017 := by
  unfold tailWord_1099822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014225477692525436053715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26742535881026802325619813 5014225477692525436053715)
  ·
    refine ⟨7521338216538788154080573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5014225477692525436053715 7521338216538788154080573)
    ·
      refine ⟨2820501831202045557780215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7521338216538788154080573 2820501831202045557780215)
      ·
        refine ⟨4230752746803068336670323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820501831202045557780215 4230752746803068336670323)
        ·
          refine ⟨6346129120204602505005485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230752746803068336670323 6346129120204602505005485)
          ·
            refine ⟨2379798420076725939377057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6346129120204602505005485 2379798420076725939377057)
            ·
              refine ⟨1784848815057544454532793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379798420076725939377057 1784848815057544454532793)
              ·
                refine ⟨1338636611293158340899595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784848815057544454532793 1338636611293158340899595)
                ·
                  refine ⟨2007954916939737511349393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338636611293158340899595 2007954916939737511349393)
                  ·
                    refine ⟨1505966187704803133512045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2007954916939737511349393 1505966187704803133512045)
                    ·
                      refine ⟨564737320389301175067017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1505966187704803133512045 564737320389301175067017)
                      ·
                        rfl

theorem cell23_1099822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1099822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099822 prefixEnd_1099822 := by exact prefixLift 1099822
  have htrace : WordTrace (prefixWord ++ tailWord_1099822) baseStart_1099822 baseEnd_1099822 := by
    simpa [prefixWord, tailWord_1099822, baseEnd_1099822] using wordTrace_append hprefix tailTrace_1099822
  have hstable : (prefixWord ++ tailWord_1099822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099822).length < 2 ^ (prefixWord ++ tailWord_1099822).sum := by decide
  have hdescent : baseEnd_1099822 < baseStart_1099822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099831 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1099831 : Nat := 118140960795 + 1099831 * 2 ^ 59
def prefixEnd_1099831 : Nat := 4983230072969 + 3 ^ 40 * 1099831 * 2
def baseEnd_1099831 : Nat := 564741941715191639854475

theorem tailTrace_1099831 : CollatzResearch.WordTrace tailWord_1099831 prefixEnd_1099831 564741941715191639854475 := by
  unfold tailWord_1099831
  simp only [CollatzResearch.WordTrace]
  refine ⟨40114132078507598025507347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26742754719005065350338231 40114132078507598025507347)
  ·
    refine ⟨60171198117761397038261021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40114132078507598025507347 60171198117761397038261021)
    ·
      refine ⟨22564199294160523889347883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60171198117761397038261021 22564199294160523889347883)
      ·
        refine ⟨33846298941240785834021825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22564199294160523889347883 33846298941240785834021825)
        ·
          refine ⟨25384724205930589375516369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33846298941240785834021825 25384724205930589375516369)
          ·
            refine ⟨19038543154447942031637277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25384724205930589375516369 19038543154447942031637277)
            ·
              refine ⟨7139453682917978261863979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19038543154447942031637277 7139453682917978261863979)
              ·
                refine ⟨10709180524376967392795969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139453682917978261863979 10709180524376967392795969)
                ·
                  refine ⟨8031885393282725544596977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10709180524376967392795969 8031885393282725544596977)
                  ·
                    refine ⟨6023914044962044158447733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8031885393282725544596977 6023914044962044158447733)
                    ·
                      refine ⟨564741941715191639854475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6023914044962044158447733 564741941715191639854475)
                      ·
                        rfl

theorem cell23_1099831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1099831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099831 prefixEnd_1099831 := by exact prefixLift 1099831
  have htrace : WordTrace (prefixWord ++ tailWord_1099831) baseStart_1099831 baseEnd_1099831 := by
    simpa [prefixWord, tailWord_1099831, baseEnd_1099831] using wordTrace_append hprefix tailTrace_1099831
  have hstable : (prefixWord ++ tailWord_1099831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099831).length < 2 ^ (prefixWord ++ tailWord_1099831).sum := by decide
  have hdescent : baseEnd_1099831 < baseStart_1099831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099869 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1099869 : Nat := 118140960795 + 1099869 * 2 ^ 59
def prefixEnd_1099869 : Nat := 4983230072969 + 3 ^ 40 * 1099869 * 2
def baseEnd_1099869 : Nat := 564761453980062491179301

theorem tailTrace_1099869 : CollatzResearch.WordTrace tailWord_1099869 prefixEnd_1099869 564761453980062491179301 := by
  unfold tailWord_1099869
  simp only [CollatzResearch.WordTrace]
  refine ⟨40115518052369930515390661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26743678701579953676927107 40115518052369930515390661)
  ·
    refine ⟨7521659634819361971635749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40115518052369930515390661 7521659634819361971635749)
    ·
      refine ⟨1410311181528630369681703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7521659634819361971635749 1410311181528630369681703)
      ·
        refine ⟨2115466772292945554522555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410311181528630369681703 2115466772292945554522555)
        ·
          refine ⟨3173200158439418331783833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115466772292945554522555 3173200158439418331783833)
          ·
            refine ⟨2379900118829563748837875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3173200158439418331783833 2379900118829563748837875)
            ·
              refine ⟨3569850178244345623256813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379900118829563748837875 3569850178244345623256813)
              ·
                refine ⟨1338693816841629608721305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3569850178244345623256813 1338693816841629608721305)
                ·
                  refine ⟨1004020362631222206540979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1338693816841629608721305 1004020362631222206540979)
                  ·
                    refine ⟨1506030543946833309811469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1004020362631222206540979 1506030543946833309811469)
                    ·
                      refine ⟨564761453980062491179301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506030543946833309811469 564761453980062491179301)
                      ·
                        rfl

theorem cell23_1099869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1099869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099869 prefixEnd_1099869 := by exact prefixLift 1099869
  have htrace : WordTrace (prefixWord ++ tailWord_1099869) baseStart_1099869 baseEnd_1099869 := by
    simpa [prefixWord, tailWord_1099869, baseEnd_1099869] using wordTrace_append hprefix tailTrace_1099869
  have hstable : (prefixWord ++ tailWord_1099869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099869).length < 2 ^ (prefixWord ++ tailWord_1099869).sum := by decide
  have hdescent : baseEnd_1099869 < baseStart_1099869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099881 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 9]
def baseStart_1099881 : Nat := 118140960795 + 1099881 * 2 ^ 59
def prefixEnd_1099881 : Nat := 4983230072969 + 3 ^ 40 * 1099881 * 2
def baseEnd_1099881 : Nat := 62751957305324049358805

theorem tailTrace_1099881 : CollatzResearch.WordTrace tailWord_1099881 prefixEnd_1099881 62751957305324049358805 := by
  unfold tailWord_1099881
  simp only [CollatzResearch.WordTrace]
  refine ⟨40115955728326456564827497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26743970485550971043218331 40115955728326456564827497)
  ·
    refine ⟨30086966796244842423620623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40115955728326456564827497 30086966796244842423620623)
    ·
      refine ⟨45130450194367263635430935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30086966796244842423620623 45130450194367263635430935)
      ·
        refine ⟨67695675291550895453146403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45130450194367263635430935 67695675291550895453146403)
        ·
          refine ⟨101543512937326343179719605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67695675291550895453146403 101543512937326343179719605)
          ·
            refine ⟨9519704337874344673098713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101543512937326343179719605 9519704337874344673098713)
            ·
              refine ⟨7139778253405758504824035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9519704337874344673098713 7139778253405758504824035)
              ·
                refine ⟨10709667380108637757236053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139778253405758504824035 10709667380108637757236053)
                ·
                  refine ⟨62751957305324049358805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10709667380108637757236053 62751957305324049358805)
                  ·
                    rfl

theorem cell23_1099881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_1099881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099881 prefixEnd_1099881 := by exact prefixLift 1099881
  have htrace : WordTrace (prefixWord ++ tailWord_1099881) baseStart_1099881 baseEnd_1099881 := by
    simpa [prefixWord, tailWord_1099881, baseEnd_1099881] using wordTrace_append hprefix tailTrace_1099881
  have hstable : (prefixWord ++ tailWord_1099881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099881).length < 2 ^ (prefixWord ++ tailWord_1099881).sum := by decide
  have hdescent : baseEnd_1099881 < baseStart_1099881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099909 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 2, 2, 2]
def baseStart_1099909 : Nat := 118140960795 + 1099909 * 2 ^ 59
def prefixEnd_1099909 : Nat := 4983230072969 + 3 ^ 40 * 1099909 * 2
def baseEnd_1099909 : Nat := 564781993206242334679117

theorem tailTrace_1099909 : CollatzResearch.WordTrace tailWord_1099909 prefixEnd_1099909 564781993206242334679117 := by
  unfold tailWord_1099909
  simp only [CollatzResearch.WordTrace]
  refine ⟨40116976972225017346846781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26744651314816678231231187 40116976972225017346846781)
  ·
    refine ⟨15043866364584381505067543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40116976972225017346846781 15043866364584381505067543)
    ·
      refine ⟨22565799546876572257601315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15043866364584381505067543 22565799546876572257601315)
      ·
        refine ⟨33848699320314858386401973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22565799546876572257601315 33848699320314858386401973)
        ·
          refine ⟨3173315561279517973725185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33848699320314858386401973 3173315561279517973725185)
          ·
            refine ⟨2379986670959638480293889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3173315561279517973725185 2379986670959638480293889)
            ·
              refine ⟨1784990003219728860220417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379986670959638480293889 1784990003219728860220417)
              ·
                refine ⟨1338742502414796645165313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784990003219728860220417 1338742502414796645165313)
                ·
                  refine ⟨1004056876811097483873985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1338742502414796645165313 1004056876811097483873985)
                  ·
                    refine ⟨753042657608323112905489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1004056876811097483873985 753042657608323112905489)
                    ·
                      refine ⟨564781993206242334679117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753042657608323112905489 564781993206242334679117)
                      ·
                        rfl

theorem cell23_1099909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_1099909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099909 prefixEnd_1099909 := by exact prefixLift 1099909
  have htrace : WordTrace (prefixWord ++ tailWord_1099909) baseStart_1099909 baseEnd_1099909 := by
    simpa [prefixWord, tailWord_1099909, baseEnd_1099909] using wordTrace_append hprefix tailTrace_1099909
  have hstable : (prefixWord ++ tailWord_1099909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099909).length < 2 ^ (prefixWord ++ tailWord_1099909).sum := by decide
  have hdescent : baseEnd_1099909 < baseStart_1099909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099978 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1099978 : Nat := 118140960795 + 1099978 * 2 ^ 59
def prefixEnd_1099978 : Nat := 4983230072969 + 3 ^ 40 * 1099978 * 2
def baseEnd_1099978 : Nat := 564817423371402564716299

theorem tailTrace_1099978 : CollatzResearch.WordTrace tailWord_1099978 prefixEnd_1099978 564817423371402564716299 := by
  unfold tailWord_1099978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10029873402243760532777147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26746329072650028087405725 10029873402243760532777147)
  ·
    refine ⟨15044810103365640799165721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10029873402243760532777147 15044810103365640799165721)
    ·
      refine ⟨11283607577524230599374291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15044810103365640799165721 11283607577524230599374291)
      ·
        refine ⟨16925411366286345899061437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11283607577524230599374291 16925411366286345899061437)
        ·
          refine ⟨6347029262357379712148039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16925411366286345899061437 6347029262357379712148039)
          ·
            refine ⟨9520543893536069568222059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347029262357379712148039 9520543893536069568222059)
            ·
              refine ⟨14280815840304104352333089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9520543893536069568222059 14280815840304104352333089)
              ·
                refine ⟨10710611880228078264249817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14280815840304104352333089 10710611880228078264249817)
                ·
                  refine ⟨8032958910171058698187363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10710611880228078264249817 8032958910171058698187363)
                  ·
                    refine ⟨12049438365256588047281045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8032958910171058698187363 12049438365256588047281045)
                    ·
                      refine ⟨564817423371402564716299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12049438365256588047281045 564817423371402564716299)
                      ·
                        rfl

theorem cell23_1099978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1099978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099978 prefixEnd_1099978 := by exact prefixLift 1099978
  have htrace : WordTrace (prefixWord ++ tailWord_1099978) baseStart_1099978 baseEnd_1099978 := by
    simpa [prefixWord, tailWord_1099978, baseEnd_1099978] using wordTrace_append hprefix tailTrace_1099978
  have hstable : (prefixWord ++ tailWord_1099978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099978).length < 2 ^ (prefixWord ++ tailWord_1099978).sum := by decide
  have hdescent : baseEnd_1099978 < baseStart_1099978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1099982 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_1099982 : Nat := 118140960795 + 1099982 * 2 ^ 59
def prefixEnd_1099982 : Nat := 4983230072969 + 3 ^ 40 * 1099982 * 2
def baseEnd_1099982 : Nat := 564819477294020549066281

theorem tailTrace_1099982 : CollatzResearch.WordTrace tailWord_1099982 prefixEnd_1099982 564819477294020549066281 := by
  unfold tailWord_1099982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014954937620068851781775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26746426333973700542836133 5014954937620068851781775)
  ·
    refine ⟨7522432406430103277672663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5014954937620068851781775 7522432406430103277672663)
    ·
      refine ⟨11283648609645154916508995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7522432406430103277672663 11283648609645154916508995)
      ·
        refine ⟨16925472914467732374763493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11283648609645154916508995 16925472914467732374763493)
        ·
          refine ⟨3173526171462699820268155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16925472914467732374763493 3173526171462699820268155)
          ·
            refine ⟨4760289257194049730402233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173526171462699820268155 4760289257194049730402233)
            ·
              refine ⟨3570216942895537297801675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4760289257194049730402233 3570216942895537297801675)
              ·
                refine ⟨5355325414343305946702513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3570216942895537297801675 5355325414343305946702513)
                ·
                  refine ⟨4016494060757479460026885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5355325414343305946702513 4016494060757479460026885)
                  ·
                    refine ⟨753092636392027398755041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4016494060757479460026885 753092636392027398755041)
                    ·
                      refine ⟨564819477294020549066281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753092636392027398755041 564819477294020549066281)
                      ·
                        rfl

theorem cell23_1099982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_1099982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1099982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1099982 prefixEnd_1099982 := by exact prefixLift 1099982
  have htrace : WordTrace (prefixWord ++ tailWord_1099982) baseStart_1099982 baseEnd_1099982 := by
    simpa [prefixWord, tailWord_1099982, baseEnd_1099982] using wordTrace_append hprefix tailTrace_1099982
  have hstable : (prefixWord ++ tailWord_1099982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1099982).length < 2 ^ (prefixWord ++ tailWord_1099982).sum := by decide
  have hdescent : baseEnd_1099982 < baseStart_1099982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1099982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100025 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 3, 5, 2]
def baseStart_1100025 : Nat := 118140960795 + 1100025 * 2 ^ 59
def prefixEnd_1100025 : Nat := 4983230072969 + 3 ^ 40 * 1100025 * 2
def baseEnd_1100025 : Nat := 564841556962163880828583

theorem tailTrace_1100025 : CollatzResearch.WordTrace tailWord_1100025 prefixEnd_1100025 564841556962163880828583 := by
  unfold tailWord_1100025
  simp only [CollatzResearch.WordTrace]
  refine ⟨40121207839804769158069529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26747471893203179438713019 40121207839804769158069529)
  ·
    refine ⟨30090905879853576868552147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40121207839804769158069529 30090905879853576868552147)
    ·
      refine ⟨45136358819780365302828221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30090905879853576868552147 45136358819780365302828221)
      ·
        refine ⟨16926134557417636988560583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45136358819780365302828221 16926134557417636988560583)
        ·
          refine ⟨25389201836126455482840875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16926134557417636988560583 25389201836126455482840875)
          ·
            refine ⟨38083802754189683224261313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25389201836126455482840875 38083802754189683224261313)
            ·
              refine ⟨28562852065642262418195985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38083802754189683224261313 28562852065642262418195985)
              ·
                refine ⟨21422139049231696813646989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28562852065642262418195985 21422139049231696813646989)
                ·
                  refine ⟨8033302143461886305117621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21422139049231696813646989 8033302143461886305117621)
                  ·
                    refine ⟨753122075949551841104777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8033302143461886305117621 753122075949551841104777)
                    ·
                      refine ⟨564841556962163880828583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753122075949551841104777 564841556962163880828583)
                      ·
                        rfl

theorem cell23_1100025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_1100025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100025 prefixEnd_1100025 := by exact prefixLift 1100025
  have htrace : WordTrace (prefixWord ++ tailWord_1100025) baseStart_1100025 baseEnd_1100025 := by
    simpa [prefixWord, tailWord_1100025, baseEnd_1100025] using wordTrace_append hprefix tailTrace_1100025
  have hstable : (prefixWord ++ tailWord_1100025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100025).length < 2 ^ (prefixWord ++ tailWord_1100025).sum := by decide
  have hdescent : baseEnd_1100025 < baseStart_1100025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100032 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 3, 1, 3]
def baseStart_1100032 : Nat := 118140960795 + 1100032 * 2 ^ 59
def prefixEnd_1100032 : Nat := 4983230072969 + 3 ^ 40 * 1100032 * 2
def baseEnd_1100032 : Nat := 564845151326745353441051

theorem tailTrace_1100032 : CollatzResearch.WordTrace tailWord_1100032 prefixEnd_1100032 564845151326745353441051 := by
  unfold tailWord_1100032
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060731575389704676787175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26747642100519606235716233 20060731575389704676787175)
  ·
    refine ⟨30091097363084557015180763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20060731575389704676787175 30091097363084557015180763)
    ·
      refine ⟨45136646044626835522771145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30091097363084557015180763 45136646044626835522771145)
      ·
        refine ⟨33852484533470126642078359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45136646044626835522771145 33852484533470126642078359)
        ·
          refine ⟨50778726800205189963117539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33852484533470126642078359 50778726800205189963117539)
          ·
            refine ⟨76168090200307784944676309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50778726800205189963117539 76168090200307784944676309)
            ·
              refine ⟨1785189614069713709640851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 76168090200307784944676309 1785189614069713709640851)
              ·
                refine ⟨2677784421104570564461277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785189614069713709640851 2677784421104570564461277)
                ·
                  refine ⟨1004169157914213961672979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2677784421104570564461277 1004169157914213961672979)
                  ·
                    refine ⟨1506253736871320942509469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1004169157914213961672979 1506253736871320942509469)
                    ·
                      refine ⟨564845151326745353441051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506253736871320942509469 564845151326745353441051)
                      ·
                        rfl

theorem cell23_1100032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_1100032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100032 prefixEnd_1100032 := by exact prefixLift 1100032
  have htrace : WordTrace (prefixWord ++ tailWord_1100032) baseStart_1100032 baseEnd_1100032 := by
    simpa [prefixWord, tailWord_1100032, baseEnd_1100032] using wordTrace_append hprefix tailTrace_1100032
  have hstable : (prefixWord ++ tailWord_1100032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100032).length < 2 ^ (prefixWord ++ tailWord_1100032).sum := by decide
  have hdescent : baseEnd_1100032 < baseStart_1100032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100065 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1100065 : Nat := 118140960795 + 1100065 * 2 ^ 59
def prefixEnd_1100065 : Nat := 4983230072969 + 3 ^ 40 * 1100065 * 2
def baseEnd_1100065 : Nat := 188287365396114574776133

theorem tailTrace_1100065 : CollatzResearch.WordTrace tailWord_1100065 prefixEnd_1100065 188287365396114574776133 := by
  unfold tailWord_1100065
  simp only [CollatzResearch.WordTrace]
  refine ⟨40122666759659855989525649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26748444506439903993017099 40122666759659855989525649)
  ·
    refine ⟨30092000069744891992144237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40122666759659855989525649 30092000069744891992144237)
    ·
      refine ⟨11284500026154334497054089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30092000069744891992144237 11284500026154334497054089)
      ·
        refine ⟨8463375019615750872790567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11284500026154334497054089 8463375019615750872790567)
        ·
          refine ⟨12695062529423626309185851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8463375019615750872790567 12695062529423626309185851)
          ·
            refine ⟨19042593794135439463778777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12695062529423626309185851 19042593794135439463778777)
            ·
              refine ⟨14281945345601579597834083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19042593794135439463778777 14281945345601579597834083)
              ·
                refine ⟨21422918018402369396751125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14281945345601579597834083 21422918018402369396751125)
                ·
                  refine ⟨1004199282112611065472709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21422918018402369396751125 1004199282112611065472709)
                  ·
                    refine ⟨188287365396114574776133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1004199282112611065472709 188287365396114574776133)
                    ·
                      rfl

theorem cell23_1100065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1100065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100065 prefixEnd_1100065 := by exact prefixLift 1100065
  have htrace : WordTrace (prefixWord ++ tailWord_1100065) baseStart_1100065 baseEnd_1100065 := by
    simpa [prefixWord, tailWord_1100065, baseEnd_1100065] using wordTrace_append hprefix tailTrace_1100065
  have hstable : (prefixWord ++ tailWord_1100065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100065).length < 2 ^ (prefixWord ++ tailWord_1100065).sum := by decide
  have hdescent : baseEnd_1100065 < baseStart_1100065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100069 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_1100069 : Nat := 118140960795 + 1100069 * 2 ^ 59
def prefixEnd_1100069 : Nat := 4983230072969 + 3 ^ 40 * 1100069 * 2
def baseEnd_1100069 : Nat := 188288050036987236226127

theorem tailTrace_1100069 : CollatzResearch.WordTrace tailWord_1100069 prefixEnd_1100069 188288050036987236226127 := by
  unfold tailWord_1100069
  simp only [CollatzResearch.WordTrace]
  refine ⟨40122812651645364672671261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26748541767763576448447507 40122812651645364672671261)
  ·
    refine ⟨15046054744367011752251723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40122812651645364672671261 15046054744367011752251723)
    ·
      refine ⟨22569082116550517628377585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15046054744367011752251723 22569082116550517628377585)
      ·
        refine ⟨16926811587412888221283189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22569082116550517628377585 16926811587412888221283189)
        ·
          refine ⟨1586888586319958270745299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16926811587412888221283189 1586888586319958270745299)
          ·
            refine ⟨2380332879479937406117949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586888586319958270745299 2380332879479937406117949)
            ·
              refine ⟨892624829804976527294231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2380332879479937406117949 892624829804976527294231)
              ·
                refine ⟨1338937244707464790941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892624829804976527294231 1338937244707464790941347)
                ·
                  refine ⟨2008405867061197186412021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338937244707464790941347 2008405867061197186412021)
                  ·
                    refine ⟨188288050036987236226127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2008405867061197186412021 188288050036987236226127)
                    ·
                      rfl

theorem cell23_1100069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_1100069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100069 prefixEnd_1100069 := by exact prefixLift 1100069
  have htrace : WordTrace (prefixWord ++ tailWord_1100069) baseStart_1100069 baseEnd_1100069 := by
    simpa [prefixWord, tailWord_1100069, baseEnd_1100069] using wordTrace_append hprefix tailTrace_1100069
  have hstable : (prefixWord ++ tailWord_1100069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100069).length < 2 ^ (prefixWord ++ tailWord_1100069).sum := by decide
  have hdescent : baseEnd_1100069 < baseStart_1100069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100085 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1100085 : Nat := 118140960795 + 1100085 * 2 ^ 59
def prefixEnd_1100085 : Nat := 4983230072969 + 3 ^ 40 * 1100085 * 2
def baseEnd_1100085 : Nat := 564872365801433646078307

theorem tailTrace_1100085 : CollatzResearch.WordTrace tailWord_1100085 prefixEnd_1100085 564872365801433646078307 := by
  unfold tailWord_1100085
  simp only [CollatzResearch.WordTrace]
  refine ⟨40123396219587399405253709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26748930813058266270169139 40123396219587399405253709)
  ·
    refine ⟨15046273582345274776970141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40123396219587399405253709 15046273582345274776970141)
    ·
      refine ⟨5642352593379478041363803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15046273582345274776970141 5642352593379478041363803)
      ·
        refine ⟨8463528890069217062045705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5642352593379478041363803 8463528890069217062045705)
        ·
          refine ⟨6347646667551912796534279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8463528890069217062045705 6347646667551912796534279)
          ·
            refine ⟨9521470001327869194801419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347646667551912796534279 9521470001327869194801419)
            ·
              refine ⟨14282205001991803792202129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9521470001327869194801419 14282205001991803792202129)
              ·
                refine ⟨10711653751493852844151597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14282205001991803792202129 10711653751493852844151597)
                ·
                  refine ⟨4016870156810194816556849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10711653751493852844151597 4016870156810194816556849)
                  ·
                    refine ⟨3012652617607646112417637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016870156810194816556849 3012652617607646112417637)
                    ·
                      refine ⟨564872365801433646078307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3012652617607646112417637 564872365801433646078307)
                      ·
                        rfl

theorem cell23_1100085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1100085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100085 prefixEnd_1100085 := by exact prefixLift 1100085
  have htrace : WordTrace (prefixWord ++ tailWord_1100085) baseStart_1100085 baseEnd_1100085 := by
    simpa [prefixWord, tailWord_1100085, baseEnd_1100085] using wordTrace_append hprefix tailTrace_1100085
  have hstable : (prefixWord ++ tailWord_1100085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100085).length < 2 ^ (prefixWord ++ tailWord_1100085).sum := by decide
  have hdescent : baseEnd_1100085 < baseStart_1100085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100122 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_1100122 : Nat := 118140960795 + 1100122 * 2 ^ 59
def prefixEnd_1100122 : Nat := 4983230072969 + 3 ^ 40 * 1100122 * 2
def baseEnd_1100122 : Nat := 564891364585650001315637

theorem tailTrace_1100122 : CollatzResearch.WordTrace tailWord_1100122 prefixEnd_1100122 564891364585650001315637 := by
  unfold tailWord_1100122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10031186430113338681087655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26749830480302236482900413 10031186430113338681087655)
  ·
    refine ⟨15046779645170008021631483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10031186430113338681087655 15046779645170008021631483)
    ·
      refine ⟨22570169467755012032447225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15046779645170008021631483 22570169467755012032447225)
      ·
        refine ⟨16927627100816259024335419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22570169467755012032447225 16927627100816259024335419)
        ·
          refine ⟨25391440651224388536503129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16927627100816259024335419 25391440651224388536503129)
          ·
            refine ⟨19043580488418291402377347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25391440651224388536503129 19043580488418291402377347)
            ·
              refine ⟨28565370732627437103566021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19043580488418291402377347 28565370732627437103566021)
              ·
                refine ⟨5356007012367644456918629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28565370732627437103566021 5356007012367644456918629)
                ·
                  refine ⟨1004251314818933335672243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5356007012367644456918629 1004251314818933335672243)
                  ·
                    refine ⟨1506376972228400003508365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1004251314818933335672243 1506376972228400003508365)
                    ·
                      refine ⟨564891364585650001315637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506376972228400003508365 564891364585650001315637)
                      ·
                        rfl

theorem cell23_1100122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_1100122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100122 prefixEnd_1100122 := by exact prefixLift 1100122
  have htrace : WordTrace (prefixWord ++ tailWord_1100122) baseStart_1100122 baseEnd_1100122 := by
    simpa [prefixWord, tailWord_1100122, baseEnd_1100122] using wordTrace_append hprefix tailTrace_1100122
  have hstable : (prefixWord ++ tailWord_1100122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100122).length < 2 ^ (prefixWord ++ tailWord_1100122).sum := by decide
  have hdescent : baseEnd_1100122 < baseStart_1100122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100155 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 2, 6]
def baseStart_1100155 : Nat := 118140960795 + 1100155 * 2 ^ 59
def prefixEnd_1100155 : Nat := 4983230072969 + 3 ^ 40 * 1100155 * 2
def baseEnd_1100155 : Nat := 188302769815749457400995

theorem tailTrace_1100155 : CollatzResearch.WordTrace tailWord_1100155 prefixEnd_1100155 188302769815749457400995 := by
  unfold tailWord_1100155
  simp only [CollatzResearch.WordTrace]
  refine ⟨40125949329333801360301919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26750632886222534240201279 40125949329333801360301919)
  ·
    refine ⟨60188923994000702040452879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40125949329333801360301919 60188923994000702040452879)
    ·
      refine ⟨90283385991001053060679319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60188923994000702040452879 90283385991001053060679319)
      ·
        refine ⟨135425078986501579591018979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90283385991001053060679319 135425078986501579591018979)
        ·
          refine ⟨203137618479752369386528469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135425078986501579591018979 203137618479752369386528469)
          ·
            refine ⟨4761037933119196157496761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 203137618479752369386528469 4761037933119196157496761)
            ·
              refine ⟨3570778449839397118122571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4761037933119196157496761 3570778449839397118122571)
              ·
                refine ⟨5356167674759095677183857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3570778449839397118122571 5356167674759095677183857)
                ·
                  refine ⟨4017125756069321757887893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5356167674759095677183857 4017125756069321757887893)
                  ·
                    refine ⟨188302769815749457400995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4017125756069321757887893 188302769815749457400995)
                    ·
                      rfl

theorem cell23_1100155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 6].length) (baseStart_1100155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100155 prefixEnd_1100155 := by exact prefixLift 1100155
  have htrace : WordTrace (prefixWord ++ tailWord_1100155) baseStart_1100155 baseEnd_1100155 := by
    simpa [prefixWord, tailWord_1100155, baseEnd_1100155] using wordTrace_append hprefix tailTrace_1100155
  have hstable : (prefixWord ++ tailWord_1100155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100155).length < 2 ^ (prefixWord ++ tailWord_1100155).sum := by decide
  have hdescent : baseEnd_1100155 < baseStart_1100155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100165 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_1100165 : Nat := 118140960795 + 1100165 * 2 ^ 59
def prefixEnd_1100165 : Nat := 4983230072969 + 3 ^ 40 * 1100165 * 2
def baseEnd_1100165 : Nat := 564913444253793333077939

theorem tailTrace_1100165 : CollatzResearch.WordTrace tailWord_1100165 prefixEnd_1100165 564913444253793333077939 := by
  unfold tailWord_1100165
  simp only [CollatzResearch.WordTrace]
  refine ⟨40126314059297573068165949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26750876039531715378777299 40126314059297573068165949)
  ·
    refine ⟨15047367772236589900562231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40126314059297573068165949 15047367772236589900562231)
    ·
      refine ⟨22571051658354884850843347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15047367772236589900562231 22571051658354884850843347)
      ·
        refine ⟨33856577487532327276265021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22571051658354884850843347 33856577487532327276265021)
        ·
          refine ⟨12696216557824622728599383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33856577487532327276265021 12696216557824622728599383)
          ·
            refine ⟨19044324836736934092899075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12696216557824622728599383 19044324836736934092899075)
            ·
              refine ⟨28566487255105401139348613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19044324836736934092899075 28566487255105401139348613)
              ·
                refine ⟨5356216360332262713627865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28566487255105401139348613 5356216360332262713627865)
                ·
                  refine ⟨4017162270249197035220899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5356216360332262713627865 4017162270249197035220899)
                  ·
                    refine ⟨6025743405373795552831349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017162270249197035220899 6025743405373795552831349)
                    ·
                      refine ⟨564913444253793333077939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6025743405373795552831349 564913444253793333077939)
                      ·
                        rfl

theorem cell23_1100165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_1100165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100165 prefixEnd_1100165 := by exact prefixLift 1100165
  have htrace : WordTrace (prefixWord ++ tailWord_1100165) baseStart_1100165 baseEnd_1100165 := by
    simpa [prefixWord, tailWord_1100165, baseEnd_1100165] using wordTrace_append hprefix tailTrace_1100165
  have hstable : (prefixWord ++ tailWord_1100165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100165).length < 2 ^ (prefixWord ++ tailWord_1100165).sum := by decide
  have hdescent : baseEnd_1100165 < baseStart_1100165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100213 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_1100213 : Nat := 118140960795 + 1100213 * 2 ^ 59
def prefixEnd_1100213 : Nat := 4983230072969 + 3 ^ 40 * 1100213 * 2
def baseEnd_1100213 : Nat := 564938091325209145277719

theorem tailTrace_1100213 : CollatzResearch.WordTrace tailWord_1100213 prefixEnd_1100213 564938091325209145277719 := by
  unfold tailWord_1100213
  simp only [CollatzResearch.WordTrace]
  refine ⟨40128064763123677265913293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26752043175415784843942195 40128064763123677265913293)
  ·
    refine ⟨15048024286171378974717485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40128064763123677265913293 15048024286171378974717485)
    ·
      refine ⟨5643009107314267115519057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15048024286171378974717485 5643009107314267115519057)
      ·
        refine ⟨4232256830485700336639293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5643009107314267115519057 4232256830485700336639293)
        ·
          refine ⟨1587096311432137626239735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4232256830485700336639293 1587096311432137626239735)
          ·
            refine ⟨2380644467148206439359603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587096311432137626239735 2380644467148206439359603)
            ·
              refine ⟨3570966700722309659039405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380644467148206439359603 3570966700722309659039405)
              ·
                refine ⟨1339112512770866122139777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3570966700722309659039405 1339112512770866122139777)
                ·
                  refine ⟨1004334384578149591604833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1339112512770866122139777 1004334384578149591604833)
                  ·
                    refine ⟨753250788433612193703625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1004334384578149591604833 753250788433612193703625)
                    ·
                      refine ⟨564938091325209145277719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753250788433612193703625 564938091325209145277719)
                      ·
                        rfl

theorem cell23_1100213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_1100213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100213 prefixEnd_1100213 := by exact prefixLift 1100213
  have htrace : WordTrace (prefixWord ++ tailWord_1100213) baseStart_1100213 baseEnd_1100213 := by
    simpa [prefixWord, tailWord_1100213, baseEnd_1100213] using wordTrace_append hprefix tailTrace_1100213
  have hstable : (prefixWord ++ tailWord_1100213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100213).length < 2 ^ (prefixWord ++ tailWord_1100213).sum := by decide
  have hdescent : baseEnd_1100213 < baseStart_1100213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100232 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1100232 : Nat := 118140960795 + 1100232 * 2 ^ 59
def prefixEnd_1100232 : Nat := 4983230072969 + 3 ^ 40 * 1100232 * 2
def baseEnd_1100232 : Nat := 188315949152548190313377

theorem tailTrace_1100232 : CollatzResearch.WordTrace tailWord_1100232 prefixEnd_1100232 188315949152548190313377 := by
  unfold tailWord_1100232
  simp only [CollatzResearch.WordTrace]
  refine ⟨20064378875027421755427475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26752505166703229007236633 20064378875027421755427475)
  ·
    refine ⟨30096568312541132633141213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20064378875027421755427475 30096568312541132633141213)
    ·
      refine ⟨11286213117202924737427955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30096568312541132633141213 11286213117202924737427955)
      ·
        refine ⟨16929319675804387106141933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11286213117202924737427955 16929319675804387106141933)
        ·
          refine ⟨6348494878426645164803225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16929319675804387106141933 6348494878426645164803225)
          ·
            refine ⟨4761371158819983873602419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6348494878426645164803225 4761371158819983873602419)
            ·
              refine ⟨7142056738229975810403629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761371158819983873602419 7142056738229975810403629)
              ·
                refine ⟨2678271276836240928901361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7142056738229975810403629 2678271276836240928901361)
                ·
                  refine ⟨2008703457627180696676021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2678271276836240928901361 2008703457627180696676021)
                  ·
                    refine ⟨188315949152548190313377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2008703457627180696676021 188315949152548190313377)
                    ·
                      rfl

theorem cell23_1100232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1100232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100232 prefixEnd_1100232 := by exact prefixLift 1100232
  have htrace : WordTrace (prefixWord ++ tailWord_1100232) baseStart_1100232 baseEnd_1100232 := by
    simpa [prefixWord, tailWord_1100232, baseEnd_1100232] using wordTrace_append hprefix tailTrace_1100232
  have hstable : (prefixWord ++ tailWord_1100232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100232).length < 2 ^ (prefixWord ++ tailWord_1100232).sum := by decide
  have hdescent : baseEnd_1100232 < baseStart_1100232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100265 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_1100265 : Nat := 118140960795 + 1100265 * 2 ^ 59
def prefixEnd_1100265 : Nat := 4983230072969 + 3 ^ 40 * 1100265 * 2
def baseEnd_1100265 : Nat := 564964792319242941827479

theorem tailTrace_1100265 : CollatzResearch.WordTrace tailWord_1100265 prefixEnd_1100265 564964792319242941827479 := by
  unfold tailWord_1100265
  simp only [CollatzResearch.WordTrace]
  refine ⟨40129961358935290146806249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26753307572623526764537499 40129961358935290146806249)
  ·
    refine ⟨30097471019201467610104687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40129961358935290146806249 30097471019201467610104687)
    ·
      refine ⟨45146206528802201415157031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30097471019201467610104687 45146206528802201415157031)
      ·
        refine ⟨67719309793203302122735547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45146206528802201415157031 67719309793203302122735547)
        ·
          refine ⟨101578964689804953184103321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67719309793203302122735547 101578964689804953184103321)
          ·
            refine ⟨76184223517353714888077491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101578964689804953184103321 76184223517353714888077491)
            ·
              refine ⟨114276335276030572332116237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76184223517353714888077491 114276335276030572332116237)
              ·
                refine ⟨42853625728511464624543589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114276335276030572332116237 42853625728511464624543589)
                ·
                  refine ⟨8035054824095899617101923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42853625728511464624543589 8035054824095899617101923)
                  ·
                    refine ⟨12052582236143849425652885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8035054824095899617101923 12052582236143849425652885)
                    ·
                      refine ⟨564964792319242941827479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12052582236143849425652885 564964792319242941827479)
                      ·
                        rfl

theorem cell23_1100265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_1100265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100265 prefixEnd_1100265 := by exact prefixLift 1100265
  have htrace : WordTrace (prefixWord ++ tailWord_1100265) baseStart_1100265 baseEnd_1100265 := by
    simpa [prefixWord, tailWord_1100265, baseEnd_1100265] using wordTrace_append hprefix tailTrace_1100265
  have hstable : (prefixWord ++ tailWord_1100265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100265).length < 2 ^ (prefixWord ++ tailWord_1100265).sum := by decide
  have hdescent : baseEnd_1100265 < baseStart_1100265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100272 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3]
def baseStart_1100272 : Nat := 118140960795 + 1100272 * 2 ^ 59
def prefixEnd_1100272 : Nat := 4983230072969 + 3 ^ 40 * 1100272 * 2
def baseEnd_1100272 : Nat := 564968386683824414439947

theorem tailTrace_1100272 : CollatzResearch.WordTrace tailWord_1100272 prefixEnd_1100272 564968386683824414439947 := by
  unfold tailWord_1100272
  simp only [CollatzResearch.WordTrace]
  refine ⟨20065108334954965171155535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26753477779939953561540713 20065108334954965171155535)
  ·
    refine ⟨30097662502432447756733303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20065108334954965171155535 30097662502432447756733303)
    ·
      refine ⟨45146493753648671635099955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30097662502432447756733303 45146493753648671635099955)
      ·
        refine ⟨67719740630473007452649933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45146493753648671635099955 67719740630473007452649933)
        ·
          refine ⟨25394902736427377794743725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67719740630473007452649933 25394902736427377794743725)
          ·
            refine ⟨9523088526160266673028897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25394902736427377794743725 9523088526160266673028897)
            ·
              refine ⟨7142316394620200004771673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9523088526160266673028897 7142316394620200004771673)
              ·
                refine ⟨5356737295965150003578755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7142316394620200004771673 5356737295965150003578755)
                ·
                  refine ⟨8035105943947725005368133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356737295965150003578755 8035105943947725005368133)
                  ·
                    refine ⟨1506582364490198438506525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8035105943947725005368133 1506582364490198438506525)
                    ·
                      refine ⟨564968386683824414439947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506582364490198438506525 564968386683824414439947)
                      ·
                        rfl

theorem cell23_1100272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_1100272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100272 prefixEnd_1100272 := by exact prefixLift 1100272
  have htrace : WordTrace (prefixWord ++ tailWord_1100272) baseStart_1100272 baseEnd_1100272 := by
    simpa [prefixWord, tailWord_1100272, baseEnd_1100272] using wordTrace_append hprefix tailTrace_1100272
  have hstable : (prefixWord ++ tailWord_1100272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100272).length < 2 ^ (prefixWord ++ tailWord_1100272).sum := by decide
  have hdescent : baseEnd_1100272 < baseStart_1100272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100289 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1100289 : Nat := 118140960795 + 1100289 * 2 ^ 59
def prefixEnd_1100289 : Nat := 4983230072969 + 3 ^ 40 * 1100289 * 2
def baseEnd_1100289 : Nat := 564977115854950847927369

theorem tailTrace_1100289 : CollatzResearch.WordTrace tailWord_1100289 prefixEnd_1100289 564977115854950847927369 := by
  unfold tailWord_1100289
  simp only [CollatzResearch.WordTrace]
  refine ⟨40130836710848342245679921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26753891140565561497119947 40130836710848342245679921)
  ·
    refine ⟨30098127533136256684259941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40130836710848342245679921 30098127533136256684259941)
    ·
      refine ⟨5643398912463048128298739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30098127533136256684259941 5643398912463048128298739)
      ·
        refine ⟨8465098368694572192448109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643398912463048128298739 8465098368694572192448109)
        ·
          refine ⟨3174411888260464572168041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8465098368694572192448109 3174411888260464572168041)
          ·
            refine ⟨2380808916195348429126031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3174411888260464572168041 2380808916195348429126031)
            ·
              refine ⟨3571213374293022643689047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380808916195348429126031 3571213374293022643689047)
              ·
                refine ⟨5356820061439533965533571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571213374293022643689047 5356820061439533965533571)
                ·
                  refine ⟨8035230092159300948300357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5356820061439533965533571 8035230092159300948300357)
                  ·
                    refine ⟨1506605642279868927806317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8035230092159300948300357 1506605642279868927806317)
                    ·
                      refine ⟨564977115854950847927369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506605642279868927806317 564977115854950847927369)
                      ·
                        rfl

theorem cell23_1100289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1100289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100289 prefixEnd_1100289 := by exact prefixLift 1100289
  have htrace : WordTrace (prefixWord ++ tailWord_1100289) baseStart_1100289 baseEnd_1100289 := by
    simpa [prefixWord, tailWord_1100289, baseEnd_1100289] using wordTrace_append hprefix tailTrace_1100289
  have hstable : (prefixWord ++ tailWord_1100289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100289).length < 2 ^ (prefixWord ++ tailWord_1100289).sum := by decide
  have hdescent : baseEnd_1100289 < baseStart_1100289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100312 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1100312 : Nat := 118140960795 + 1100312 * 2 ^ 59
def prefixEnd_1100312 : Nat := 4983230072969 + 3 ^ 40 * 1100312 * 2
def baseEnd_1100312 : Nat := 564988925910004257939763

theorem tailTrace_1100312 : CollatzResearch.WordTrace tailWord_1100312 prefixEnd_1100312 564988925910004257939763 := by
  unfold tailWord_1100312
  simp only [CollatzResearch.WordTrace]
  refine ⟨20065837794882508586883595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26754450393176678115844793 20065837794882508586883595)
  ·
    refine ⟨30098756692323762880325393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20065837794882508586883595 30098756692323762880325393)
    ·
      refine ⟨22574067519242822160244045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30098756692323762880325393 22574067519242822160244045)
      ·
        refine ⟨8465275319716058310091517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22574067519242822160244045 8465275319716058310091517)
        ·
          refine ⟨3174478244893521866284319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8465275319716058310091517 3174478244893521866284319)
          ·
            refine ⟨4761717367340282799426479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174478244893521866284319 4761717367340282799426479)
            ·
              refine ⟨7142576051010424199139719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761717367340282799426479 7142576051010424199139719)
              ·
                refine ⟨10713864076515636298709579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7142576051010424199139719 10713864076515636298709579)
                ·
                  refine ⟨16070796114773454448064369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10713864076515636298709579 16070796114773454448064369)
                  ·
                    refine ⟨12053097086080090836048277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16070796114773454448064369 12053097086080090836048277)
                    ·
                      refine ⟨564988925910004257939763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12053097086080090836048277 564988925910004257939763)
                      ·
                        rfl

theorem cell23_1100312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1100312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100312 prefixEnd_1100312 := by exact prefixLift 1100312
  have htrace : WordTrace (prefixWord ++ tailWord_1100312) baseStart_1100312 baseEnd_1100312 := by
    simpa [prefixWord, tailWord_1100312, baseEnd_1100312] using wordTrace_append hprefix tailTrace_1100312
  have hstable : (prefixWord ++ tailWord_1100312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100312).length < 2 ^ (prefixWord ++ tailWord_1100312).sum := by decide
  have hdescent : baseEnd_1100312 < baseStart_1100312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100339 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 1, 5]
def baseStart_1100339 : Nat := 118140960795 + 1100339 * 2 ^ 59
def prefixEnd_1100339 : Nat := 4983230072969 + 3 ^ 40 * 1100339 * 2
def baseEnd_1100339 : Nat := 188334263295891884100713

theorem tailTrace_1100339 : CollatzResearch.WordTrace tailWord_1100339 prefixEnd_1100339 188334263295891884100713 := by
  unfold tailWord_1100339
  simp only [CollatzResearch.WordTrace]
  refine ⟨40132660360667200785000071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26755106907111467190000047 40132660360667200785000071)
  ·
    refine ⟨60198990541000801177500107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40132660360667200785000071 60198990541000801177500107)
    ·
      refine ⟨90298485811501201766250161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60198990541000801177500107 90298485811501201766250161)
      ·
        refine ⟨67723864358625901324687621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90298485811501201766250161 67723864358625901324687621)
        ·
          refine ⟨12698224567242356498378929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67723864358625901324687621 12698224567242356498378929)
          ·
            refine ⟨9523668425431767373784197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12698224567242356498378929 9523668425431767373784197)
            ·
              refine ⟨1785687829768456382584537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9523668425431767373784197 1785687829768456382584537)
              ·
                refine ⟨1339265872326342286938403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785687829768456382584537 1339265872326342286938403)
                ·
                  refine ⟨2008898808489513430407605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339265872326342286938403 2008898808489513430407605)
                  ·
                    refine ⟨188334263295891884100713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2008898808489513430407605 188334263295891884100713)
                    ·
                      rfl

theorem cell23_1100339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 5].length) (baseStart_1100339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100339 prefixEnd_1100339 := by exact prefixLift 1100339
  have htrace : WordTrace (prefixWord ++ tailWord_1100339) baseStart_1100339 baseEnd_1100339 := by
    simpa [prefixWord, tailWord_1100339, baseEnd_1100339] using wordTrace_append hprefix tailTrace_1100339
  have hstable : (prefixWord ++ tailWord_1100339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100339).length < 2 ^ (prefixWord ++ tailWord_1100339).sum := by decide
  have hdescent : baseEnd_1100339 < baseStart_1100339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100352 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 1, 6]
def baseStart_1100352 : Nat := 118140960795 + 1100352 * 2 ^ 59
def prefixEnd_1100352 : Nat := 4983230072969 + 3 ^ 40 * 1100352 * 2
def baseEnd_1100352 : Nat := 188336488378728033813193

theorem tailTrace_1100352 : CollatzResearch.WordTrace tailWord_1100352 prefixEnd_1100352 188336488378728033813193 := by
  unfold tailWord_1100352
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066567254810052002611655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26755423006413402670148873 20066567254810052002611655)
  ·
    refine ⟨30099850882215078003917483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20066567254810052002611655 30099850882215078003917483)
    ·
      refine ⟨45149776323322617005876225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30099850882215078003917483 45149776323322617005876225)
      ·
        refine ⟨33862332242491962754407169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45149776323322617005876225 33862332242491962754407169)
        ·
          refine ⟨25396749181868972065805377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33862332242491962754407169 25396749181868972065805377)
          ·
            refine ⟨19047561886401729049354033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25396749181868972065805377 19047561886401729049354033)
            ·
              refine ⟨14285671414801296787015525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19047561886401729049354033 14285671414801296787015525)
              ·
                refine ⟨2678563390275243147565411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14285671414801296787015525 2678563390275243147565411)
                ·
                  refine ⟨4017845085412864721348117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678563390275243147565411 4017845085412864721348117)
                  ·
                    refine ⟨188336488378728033813193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4017845085412864721348117 188336488378728033813193)
                    ·
                      rfl

theorem cell23_1100352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_1100352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100352 prefixEnd_1100352 := by exact prefixLift 1100352
  have htrace : WordTrace (prefixWord ++ tailWord_1100352) baseStart_1100352 baseEnd_1100352 := by
    simpa [prefixWord, tailWord_1100352, baseEnd_1100352] using wordTrace_append hprefix tailTrace_1100352
  have hstable : (prefixWord ++ tailWord_1100352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100352).length < 2 ^ (prefixWord ++ tailWord_1100352).sum := by decide
  have hdescent : baseEnd_1100352 < baseStart_1100352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100369 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 4, 4]
def baseStart_1100369 : Nat := 118140960795 + 1100369 * 2 ^ 59
def prefixEnd_1100369 : Nat := 4983230072969 + 3 ^ 40 * 1100369 * 2
def baseEnd_1100369 : Nat := 188339398102436844975667

theorem tailTrace_1100369 : CollatzResearch.WordTrace tailWord_1100369 prefixEnd_1100369 188339398102436844975667 := by
  unfold tailWord_1100369
  simp only [CollatzResearch.WordTrace]
  refine ⟨40133754550558515908592161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26755836367039010605728107 40133754550558515908592161)
  ·
    refine ⟨30100315912918886931444121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40133754550558515908592161 30100315912918886931444121)
    ·
      refine ⟨22575236934689165198583091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30100315912918886931444121 22575236934689165198583091)
      ·
        refine ⟨33862855402033747797874637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22575236934689165198583091 33862855402033747797874637)
        ·
          refine ⟨12698570775762655424202989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33862855402033747797874637 12698570775762655424202989)
          ·
            refine ⟨4761964040910995784076121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12698570775762655424202989 4761964040910995784076121)
            ·
              refine ⟨3571473030683246838057091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4761964040910995784076121 3571473030683246838057091)
              ·
                refine ⟨5357209546024870257085637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571473030683246838057091 5357209546024870257085637)
                ·
                  refine ⟨1004476789879663173203557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5357209546024870257085637 1004476789879663173203557)
                  ·
                    refine ⟨188339398102436844975667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1004476789879663173203557 188339398102436844975667)
                    ·
                      rfl

theorem cell23_1100369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_1100369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100369 prefixEnd_1100369 := by exact prefixLift 1100369
  have htrace : WordTrace (prefixWord ++ tailWord_1100369) baseStart_1100369 baseEnd_1100369 := by
    simpa [prefixWord, tailWord_1100369, baseEnd_1100369] using wordTrace_append hprefix tailTrace_1100369
  have hstable : (prefixWord ++ tailWord_1100369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100369).length < 2 ^ (prefixWord ++ tailWord_1100369).sum := by decide
  have hdescent : baseEnd_1100369 < baseStart_1100369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100370 : List Nat := [3, 2, 2, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_1100370 : Nat := 118140960795 + 1100370 * 2 ^ 59
def prefixEnd_1100370 : Nat := 4983230072969 + 3 ^ 40 * 1100370 * 2
def baseEnd_1100370 : Nat := 565018707787965031014497

theorem tailTrace_1100370 : CollatzResearch.WordTrace tailWord_1100370 prefixEnd_1100370 565018707787965031014497 := by
  unfold tailWord_1100370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10033447755888723269844641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26755860682369928719585709 10033447755888723269844641)
  ·
    refine ⟨7525085816916542452383481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10033447755888723269844641 7525085816916542452383481)
    ·
      refine ⟨5643814362687406839287611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7525085816916542452383481 5643814362687406839287611)
      ·
        refine ⟨8465721544031110258931417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5643814362687406839287611 8465721544031110258931417)
        ·
          refine ⟨6349291158023332694198563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8465721544031110258931417 6349291158023332694198563)
          ·
            refine ⟨9523936737034999041297845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6349291158023332694198563 9523936737034999041297845)
            ·
              refine ⟨892869069097031160121673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9523936737034999041297845 892869069097031160121673)
              ·
                refine ⟨669651801822773370091255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892869069097031160121673 669651801822773370091255)
                ·
                  refine ⟨1004477702734160055136883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669651801822773370091255 1004477702734160055136883)
                  ·
                    refine ⟨1506716554101240082705325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1004477702734160055136883 1506716554101240082705325)
                    ·
                      refine ⟨565018707787965031014497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506716554101240082705325 565018707787965031014497)
                      ·
                        rfl

theorem cell23_1100370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_1100370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100370 prefixEnd_1100370 := by exact prefixLift 1100370
  have htrace : WordTrace (prefixWord ++ tailWord_1100370) baseStart_1100370 baseEnd_1100370 := by
    simpa [prefixWord, tailWord_1100370, baseEnd_1100370] using wordTrace_append hprefix tailTrace_1100370
  have hstable : (prefixWord ++ tailWord_1100370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100370).length < 2 ^ (prefixWord ++ tailWord_1100370).sum := by decide
  have hdescent : baseEnd_1100370 < baseStart_1100370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100396 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_1100396 : Nat := 118140960795 + 1100396 * 2 ^ 59
def prefixEnd_1100396 : Nat := 4983230072969 + 3 ^ 40 * 1100396 * 2
def baseEnd_1100396 : Nat := 565032058284981929289377

theorem tailTrace_1100396 : CollatzResearch.WordTrace tailWord_1100396 prefixEnd_1100396 565032058284981929289377 := by
  unfold tailWord_1100396
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067369660730349759912521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26756492880973799679883361 20067369660730349759912521)
  ·
    refine ⟨15050527245547762319934391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20067369660730349759912521 15050527245547762319934391)
    ·
      refine ⟨22575790868321643479901587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15050527245547762319934391 22575790868321643479901587)
      ·
        refine ⟨33863686302482465219852381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22575790868321643479901587 33863686302482465219852381)
        ·
          refine ⟨12698882363430924457444643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33863686302482465219852381 12698882363430924457444643)
          ·
            refine ⟨19048323545146386686166965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12698882363430924457444643 19048323545146386686166965)
            ·
              refine ⟨1785780332357473751828153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19048323545146386686166965 1785780332357473751828153)
              ·
                refine ⟨1339335249268105313871115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785780332357473751828153 1339335249268105313871115)
                ·
                  refine ⟨2009002873902157970806673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339335249268105313871115 2009002873902157970806673)
                  ·
                    refine ⟨1506752155426618478105005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2009002873902157970806673 1506752155426618478105005)
                    ·
                      refine ⟨565032058284981929289377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506752155426618478105005 565032058284981929289377)
                      ·
                        rfl

theorem cell23_1100396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_1100396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100396 prefixEnd_1100396 := by exact prefixLift 1100396
  have htrace : WordTrace (prefixWord ++ tailWord_1100396) baseStart_1100396 baseEnd_1100396 := by
    simpa [prefixWord, tailWord_1100396, baseEnd_1100396] using wordTrace_append hprefix tailTrace_1100396
  have hstable : (prefixWord ++ tailWord_1100396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100396).length < 2 ^ (prefixWord ++ tailWord_1100396).sum := by decide
  have hdescent : baseEnd_1100396 < baseStart_1100396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100409 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 3]
def baseStart_1100409 : Nat := 118140960795 + 1100409 * 2 ^ 59
def prefixEnd_1100409 : Nat := 4983230072969 + 3 ^ 40 * 1100409 * 2
def baseEnd_1100409 : Nat := 565038733533490378426817

theorem tailTrace_1100409 : CollatzResearch.WordTrace tailWord_1100409 prefixEnd_1100409 565038733533490378426817 := by
  unfold tailWord_1100409
  simp only [CollatzResearch.WordTrace]
  refine ⟨40135213470413602740048281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26756808980275735160032187 40135213470413602740048281)
  ·
    refine ⟨30101410102810202055036211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40135213470413602740048281 30101410102810202055036211)
    ·
      refine ⟨45152115154215303082554317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30101410102810202055036211 45152115154215303082554317)
      ·
        refine ⟨16932043182830738655957869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45152115154215303082554317 16932043182830738655957869)
        ·
          refine ⟨6349516193561526995984201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16932043182830738655957869 6349516193561526995984201)
          ·
            refine ⟨4762137145171145246988151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6349516193561526995984201 4762137145171145246988151)
            ·
              refine ⟨7143205717756717870482227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4762137145171145246988151 7143205717756717870482227)
              ·
                refine ⟨10714808576635076805723341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7143205717756717870482227 10714808576635076805723341)
                ·
                  refine ⟨4018053216238153802146253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10714808576635076805723341 4018053216238153802146253)
                  ·
                    refine ⟨1506769956089307675804845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4018053216238153802146253 1506769956089307675804845)
                    ·
                      refine ⟨565038733533490378426817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1506769956089307675804845 565038733533490378426817)
                      ·
                        rfl

theorem cell23_1100409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_1100409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100409 prefixEnd_1100409 := by exact prefixLift 1100409
  have htrace : WordTrace (prefixWord ++ tailWord_1100409) baseStart_1100409 baseEnd_1100409 := by
    simpa [prefixWord, tailWord_1100409, baseEnd_1100409] using wordTrace_append hprefix tailTrace_1100409
  have hstable : (prefixWord ++ tailWord_1100409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100409).length < 2 ^ (prefixWord ++ tailWord_1100409).sum := by decide
  have hdescent : baseEnd_1100409 < baseStart_1100409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100413 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_1100413 : Nat := 118140960795 + 1100413 * 2 ^ 59
def prefixEnd_1100413 : Nat := 4983230072969 + 3 ^ 40 * 1100413 * 2
def baseEnd_1100413 : Nat := 565040787456108362776799

theorem tailTrace_1100413 : CollatzResearch.WordTrace tailWord_1100413 prefixEnd_1100413 565040787456108362776799 := by
  unfold tailWord_1100413
  simp only [CollatzResearch.WordTrace]
  refine ⟨40135359362399111423193893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26756906241599407615462595 40135359362399111423193893)
  ·
    refine ⟨7525379880449833391848855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40135359362399111423193893 7525379880449833391848855)
    ·
      refine ⟨11288069820674750087773283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7525379880449833391848855 11288069820674750087773283)
      ·
        refine ⟨16932104731012125131659925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11288069820674750087773283 16932104731012125131659925)
        ·
          refine ⟨793692409266193365546559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16932104731012125131659925 793692409266193365546559)
          ·
            refine ⟨1190538613899290048319839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793692409266193365546559 1190538613899290048319839)
            ·
              refine ⟨1785807920848935072479759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190538613899290048319839 1785807920848935072479759)
              ·
                refine ⟨2678711881273402608719639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785807920848935072479759 2678711881273402608719639)
                ·
                  refine ⟨4018067821910103913079459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678711881273402608719639 4018067821910103913079459)
                  ·
                    refine ⟨6027101732865155869619189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4018067821910103913079459 6027101732865155869619189)
                    ·
                      refine ⟨565040787456108362776799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6027101732865155869619189 565040787456108362776799)
                      ·
                        rfl

theorem cell23_1100413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_1100413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100413 prefixEnd_1100413 := by exact prefixLift 1100413
  have htrace : WordTrace (prefixWord ++ tailWord_1100413) baseStart_1100413 baseEnd_1100413 := by
    simpa [prefixWord, tailWord_1100413, baseEnd_1100413] using wordTrace_append hprefix tailTrace_1100413
  have hstable : (prefixWord ++ tailWord_1100413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100413).length < 2 ^ (prefixWord ++ tailWord_1100413).sum := by decide
  have hdescent : baseEnd_1100413 < baseStart_1100413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100479 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_1100479 : Nat := 118140960795 + 1100479 * 2 ^ 59
def prefixEnd_1100479 : Nat := 4983230072969 + 3 ^ 40 * 1100479 * 2
def baseEnd_1100479 : Nat := 565074677179305104551495

theorem tailTrace_1100479 : CollatzResearch.WordTrace tailWord_1100479 prefixEnd_1100479 565074677179305104551495 := by
  unfold tailWord_1100479
  simp only [CollatzResearch.WordTrace]
  refine ⟨40137766580160004695096491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26758511053440003130064327 40137766580160004695096491)
  ·
    refine ⟨60206649870240007042644737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40137766580160004695096491 60206649870240007042644737)
    ·
      refine ⟨45154987402680005281983553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60206649870240007042644737 45154987402680005281983553)
      ·
        refine ⟨33866240552010003961487665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45154987402680005281983553 33866240552010003961487665)
        ·
          refine ⟨25399680414007502971115749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33866240552010003961487665 25399680414007502971115749)
          ·
            refine ⟨4762440077626406807084203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25399680414007502971115749 4762440077626406807084203)
            ·
              refine ⟨7143660116439610210626305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4762440077626406807084203 7143660116439610210626305)
              ·
                refine ⟨5357745087329707657969729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7143660116439610210626305 5357745087329707657969729)
                ·
                  refine ⟨4018308815497280743477297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5357745087329707657969729 4018308815497280743477297)
                  ·
                    refine ⟨3013731611622960557607973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4018308815497280743477297 3013731611622960557607973)
                    ·
                      refine ⟨565074677179305104551495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3013731611622960557607973 565074677179305104551495)
                      ·
                        rfl

theorem cell23_1100479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_1100479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100479 prefixEnd_1100479 := by exact prefixLift 1100479
  have htrace : WordTrace (prefixWord ++ tailWord_1100479) baseStart_1100479 baseEnd_1100479 := by
    simpa [prefixWord, tailWord_1100479, baseEnd_1100479] using wordTrace_append hprefix tailTrace_1100479
  have hstable : (prefixWord ++ tailWord_1100479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100479).length < 2 ^ (prefixWord ++ tailWord_1100479).sum := by decide
  have hdescent : baseEnd_1100479 < baseStart_1100479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100529 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_1100529 : Nat := 118140960795 + 1100529 * 2 ^ 59
def prefixEnd_1100529 : Nat := 4983230072969 + 3 ^ 40 * 1100529 * 2
def baseEnd_1100529 : Nat := 565100351212029908926265

theorem tailTrace_1100529 : CollatzResearch.WordTrace tailWord_1100529 prefixEnd_1100529 565100351212029908926265 := by
  unfold tailWord_1100529
  simp only [CollatzResearch.WordTrace]
  refine ⟨40139590229978863234416641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26759726819985908822944427 40139590229978863234416641)
  ·
    refine ⟨30104692672484147425812481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40139590229978863234416641 30104692672484147425812481)
    ·
      refine ⟨22578519504363110569359361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30104692672484147425812481 22578519504363110569359361)
      ·
        refine ⟨16933889628272332927019521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22578519504363110569359361 16933889628272332927019521)
        ·
          refine ⟨12700417221204249695264641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16933889628272332927019521 12700417221204249695264641)
          ·
            refine ⟨9525312915903187271448481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12700417221204249695264641 9525312915903187271448481)
            ·
              refine ⟨7143984686927390453586361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9525312915903187271448481 7143984686927390453586361)
              ·
                refine ⟨5357988515195542840189771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7143984686927390453586361 5357988515195542840189771)
                ·
                  refine ⟨8036982772793314260284657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357988515195542840189771 8036982772793314260284657)
                  ·
                    refine ⟨6027737079594985695213493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8036982772793314260284657 6027737079594985695213493)
                    ·
                      refine ⟨565100351212029908926265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6027737079594985695213493 565100351212029908926265)
                      ·
                        rfl

theorem cell23_1100529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_1100529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100529 prefixEnd_1100529 := by exact prefixLift 1100529
  have htrace : WordTrace (prefixWord ++ tailWord_1100529) baseStart_1100529 baseEnd_1100529 := by
    simpa [prefixWord, tailWord_1100529, baseEnd_1100529] using wordTrace_append hprefix tailTrace_1100529
  have hstable : (prefixWord ++ tailWord_1100529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100529).length < 2 ^ (prefixWord ++ tailWord_1100529).sum := by decide
  have hdescent : baseEnd_1100529 < baseStart_1100529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100546 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1100546 : Nat := 118140960795 + 1100546 * 2 ^ 59
def prefixEnd_1100546 : Nat := 4983230072969 + 3 ^ 40 * 1100546 * 2
def baseEnd_1100546 : Nat := 565109080383156342413687

theorem tailTrace_1100546 : CollatzResearch.WordTrace tailWord_1100546 prefixEnd_1100546 565109080383156342413687 := by
  unfold tailWord_1100546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10035052567729318784446373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26760140180611516758523661 10035052567729318784446373)
  ·
    refine ⟨1881572356449247272083695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10035052567729318784446373 1881572356449247272083695)
    ·
      refine ⟨2822358534673870908125543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881572356449247272083695 2822358534673870908125543)
      ·
        refine ⟨4233537802010806362188315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2822358534673870908125543 4233537802010806362188315)
        ·
          refine ⟨6350306703016209543282473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233537802010806362188315 6350306703016209543282473)
          ·
            refine ⟨4762730027262157157461855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6350306703016209543282473 4762730027262157157461855)
            ·
              refine ⟨7144095040893235736192783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4762730027262157157461855 7144095040893235736192783)
              ·
                refine ⟨10716142561339853604289175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7144095040893235736192783 10716142561339853604289175)
                ·
                  refine ⟨16074213842009780406433763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10716142561339853604289175 16074213842009780406433763)
                  ·
                    refine ⟨24111320763014670609650645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16074213842009780406433763 24111320763014670609650645)
                    ·
                      refine ⟨565109080383156342413687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24111320763014670609650645 565109080383156342413687)
                      ·
                        rfl

theorem cell23_1100546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1100546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100546 prefixEnd_1100546 := by exact prefixLift 1100546
  have htrace : WordTrace (prefixWord ++ tailWord_1100546) baseStart_1100546 baseEnd_1100546 := by
    simpa [prefixWord, tailWord_1100546, baseEnd_1100546] using wordTrace_append hprefix tailTrace_1100546
  have hstable : (prefixWord ++ tailWord_1100546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100546).length < 2 ^ (prefixWord ++ tailWord_1100546).sum := by decide
  have hdescent : baseEnd_1100546 < baseStart_1100546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100556 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 1, 6, 2]
def baseStart_1100556 : Nat := 118140960795 + 1100556 * 2 ^ 59
def prefixEnd_1100556 : Nat := 4983230072969 + 3 ^ 40 * 1100556 * 2
def baseEnd_1100556 : Nat := 565114215189701303288641

theorem tailTrace_1100556 : CollatzResearch.WordTrace tailWord_1100556 prefixEnd_1100556 565114215189701303288641 := by
  unfold tailWord_1100556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20070287500440523422824761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26760383333920697897099681 20070287500440523422824761)
  ·
    refine ⟨15052715625330392567118571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20070287500440523422824761 15052715625330392567118571)
    ·
      refine ⟨22579073437995588850677857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15052715625330392567118571 22579073437995588850677857)
      ·
        refine ⟨16934305078496691638008393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22579073437995588850677857 16934305078496691638008393)
        ·
          refine ⟨12700728808872518728506295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16934305078496691638008393 12700728808872518728506295)
          ·
            refine ⟨19051093213308778092759443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12700728808872518728506295 19051093213308778092759443)
            ·
              refine ⟨28576639819963167139139165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19051093213308778092759443 28576639819963167139139165)
              ·
                refine ⟨10716239932486187677177187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28576639819963167139139165 10716239932486187677177187)
                ·
                  refine ⟨16074359898729281515765781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10716239932486187677177187 16074359898729281515765781)
                  ·
                    refine ⟨753485620252935071051521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16074359898729281515765781 753485620252935071051521)
                    ·
                      refine ⟨565114215189701303288641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753485620252935071051521 565114215189701303288641)
                      ·
                        rfl

theorem cell23_1100556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_1100556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100556 prefixEnd_1100556 := by exact prefixLift 1100556
  have htrace : WordTrace (prefixWord ++ tailWord_1100556) baseStart_1100556 baseEnd_1100556 := by
    simpa [prefixWord, tailWord_1100556, baseEnd_1100556] using wordTrace_append hprefix tailTrace_1100556
  have hstable : (prefixWord ++ tailWord_1100556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100556).length < 2 ^ (prefixWord ++ tailWord_1100556).sum := by decide
  have hdescent : baseEnd_1100556 < baseStart_1100556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100599 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1100599 : Nat := 118140960795 + 1100599 * 2 ^ 59
def prefixEnd_1100599 : Nat := 4983230072969 + 3 ^ 40 * 1100599 * 2
def baseEnd_1100599 : Nat := 565136294857844635050943

theorem tailTrace_1100599 : CollatzResearch.WordTrace tailWord_1100599 prefixEnd_1100599 565136294857844635050943 := by
  unfold tailWord_1100599
  simp only [CollatzResearch.WordTrace]
  refine ⟨40142143339725265189464851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26761428893150176792976567 40142143339725265189464851)
  ·
    refine ⟨60213215009587897784197277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40142143339725265189464851 60213215009587897784197277)
    ·
      refine ⟨22579955628595461669073979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60213215009587897784197277 22579955628595461669073979)
      ·
        refine ⟨33869933442893192503610969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22579955628595461669073979 33869933442893192503610969)
        ·
          refine ⟨25402450082169894377708227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33869933442893192503610969 25402450082169894377708227)
          ·
            refine ⟨38103675123254841566562341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25402450082169894377708227 38103675123254841566562341)
            ·
              refine ⟨7144439085610282793730439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38103675123254841566562341 7144439085610282793730439)
              ·
                refine ⟨10716658628415424190595659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7144439085610282793730439 10716658628415424190595659)
                ·
                  refine ⟨16074987942623136285893489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10716658628415424190595659 16074987942623136285893489)
                  ·
                    refine ⟨12056240956967352214420117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16074987942623136285893489 12056240956967352214420117)
                    ·
                      refine ⟨565136294857844635050943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12056240956967352214420117 565136294857844635050943)
                      ·
                        rfl

theorem cell23_1100599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1100599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100599 prefixEnd_1100599 := by exact prefixLift 1100599
  have htrace : WordTrace (prefixWord ++ tailWord_1100599) baseStart_1100599 baseEnd_1100599 := by
    simpa [prefixWord, tailWord_1100599, baseEnd_1100599] using wordTrace_append hprefix tailTrace_1100599
  have hstable : (prefixWord ++ tailWord_1100599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100599).length < 2 ^ (prefixWord ++ tailWord_1100599).sum := by decide
  have hdescent : baseEnd_1100599 < baseStart_1100599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100626 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1100626 : Nat := 118140960795 + 1100626 * 2 ^ 59
def prefixEnd_1100626 : Nat := 4983230072969 + 3 ^ 40 * 1100626 * 2
def baseEnd_1100626 : Nat := 188383386278505343137773

theorem tailTrace_1100626 : CollatzResearch.WordTrace tailWord_1100626 prefixEnd_1100626 188383386278505343137773 := by
  unfold tailWord_1100626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10035782027656862200174433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26762085407084965867131821 10035782027656862200174433)
  ·
    refine ⟨7526836520742646650130825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10035782027656862200174433 7526836520742646650130825)
    ·
      refine ⟨5645127390556984987598119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7526836520742646650130825 5645127390556984987598119)
      ·
        refine ⟨8467691085835477481397179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5645127390556984987598119 8467691085835477481397179)
        ·
          refine ⟨12701536628753216222095769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8467691085835477481397179 12701536628753216222095769)
          ·
            refine ⟨9526152471564912166571827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12701536628753216222095769 9526152471564912166571827)
            ·
              refine ⟨14289228707347368249857741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9526152471564912166571827 14289228707347368249857741)
              ·
                refine ⟨5358460765255263093696653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14289228707347368249857741 5358460765255263093696653)
                ·
                  refine ⟨2009422786970723660136245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5358460765255263093696653 2009422786970723660136245)
                  ·
                    refine ⟨188383386278505343137773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2009422786970723660136245 188383386278505343137773)
                    ·
                      rfl

theorem cell23_1100626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1100626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100626 prefixEnd_1100626 := by exact prefixLift 1100626
  have htrace : WordTrace (prefixWord ++ tailWord_1100626) baseStart_1100626 baseEnd_1100626 := by
    simpa [prefixWord, tailWord_1100626, baseEnd_1100626] using wordTrace_append hprefix tailTrace_1100626
  have hstable : (prefixWord ++ tailWord_1100626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100626).length < 2 ^ (prefixWord ++ tailWord_1100626).sum := by decide
  have hdescent : baseEnd_1100626 < baseStart_1100626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100633 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 1, 5, 2]
def baseStart_1100633 : Nat := 118140960795 + 1100633 * 2 ^ 59
def prefixEnd_1100633 : Nat := 4983230072969 + 3 ^ 40 * 1100633 * 2
def baseEnd_1100633 : Nat := 565153753200097502025787

theorem tailTrace_1100633 : CollatzResearch.WordTrace tailWord_1100633 prefixEnd_1100633 565153753200097502025787 := by
  unfold tailWord_1100633
  simp only [CollatzResearch.WordTrace]
  refine ⟨40143383421602088996202553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26762255614401392664135035 40143383421602088996202553)
  ·
    refine ⟨30107537566201566747151915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40143383421602088996202553 30107537566201566747151915)
    ·
      refine ⟨45161306349302350120727873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30107537566201566747151915 45161306349302350120727873)
      ·
        refine ⟨33870979761976762590545905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45161306349302350120727873 33870979761976762590545905)
        ·
          refine ⟨25403234821482571942909429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33870979761976762590545905 25403234821482571942909429)
          ·
            refine ⟨2381553264513991119647759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25403234821482571942909429 2381553264513991119647759)
            ·
              refine ⟨3572329896770986679471639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381553264513991119647759 3572329896770986679471639)
              ·
                refine ⟨5358494845156480019207459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572329896770986679471639 5358494845156480019207459)
                ·
                  refine ⟨8037742267734720028811189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5358494845156480019207459 8037742267734720028811189)
                  ·
                    refine ⟨753538337600130002701049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8037742267734720028811189 753538337600130002701049)
                    ·
                      refine ⟨565153753200097502025787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753538337600130002701049 565153753200097502025787)
                      ·
                        rfl

theorem cell23_1100633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_1100633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100633 prefixEnd_1100633 := by exact prefixLift 1100633
  have htrace : WordTrace (prefixWord ++ tailWord_1100633) baseStart_1100633 baseEnd_1100633 := by
    simpa [prefixWord, tailWord_1100633, baseEnd_1100633] using wordTrace_append hprefix tailTrace_1100633
  have hstable : (prefixWord ++ tailWord_1100633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100633).length < 2 ^ (prefixWord ++ tailWord_1100633).sum := by decide
  have hdescent : baseEnd_1100633 < baseStart_1100633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100643 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 1, 5]
def baseStart_1100643 : Nat := 118140960795 + 1100643 * 2 ^ 59
def prefixEnd_1100643 : Nat := 4983230072969 + 3 ^ 40 * 1100643 * 2
def baseEnd_1100643 : Nat := 188386296002214154300247

theorem tailTrace_1100643 : CollatzResearch.WordTrace tailWord_1100643 prefixEnd_1100643 188386296002214154300247 := by
  unfold tailWord_1100643
  simp only [CollatzResearch.WordTrace]
  refine ⟨40143748151565860704066583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26762498767710573802711055 40143748151565860704066583)
  ·
    refine ⟨60215622227348791056099875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40143748151565860704066583 60215622227348791056099875)
    ·
      refine ⟨90323433341023186584149813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60215622227348791056099875 90323433341023186584149813)
      ·
        refine ⟨8467821875720923742264045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90323433341023186584149813 8467821875720923742264045)
        ·
          refine ⟨3175433203395346403349017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8467821875720923742264045 3175433203395346403349017)
          ·
            refine ⟨2381574902546509802511763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3175433203395346403349017 2381574902546509802511763)
            ·
              refine ⟨3572362353819764703767645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381574902546509802511763 3572362353819764703767645)
              ·
                refine ⟨1339635882682411763912867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3572362353819764703767645 1339635882682411763912867)
                ·
                  refine ⟨2009453824023617645869301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339635882682411763912867 2009453824023617645869301)
                  ·
                    refine ⟨188386296002214154300247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2009453824023617645869301 188386296002214154300247)
                    ·
                      rfl

theorem cell23_1100643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 5].length) (baseStart_1100643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100643 prefixEnd_1100643 := by exact prefixLift 1100643
  have htrace : WordTrace (prefixWord ++ tailWord_1100643) baseStart_1100643 baseEnd_1100643 := by
    simpa [prefixWord, tailWord_1100643, baseEnd_1100643] using wordTrace_append hprefix tailTrace_1100643
  have hstable : (prefixWord ++ tailWord_1100643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100643).length < 2 ^ (prefixWord ++ tailWord_1100643).sum := by decide
  have hdescent : baseEnd_1100643 < baseStart_1100643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100680 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_1100680 : Nat := 118140960795 + 1100680 * 2 ^ 59
def prefixEnd_1100680 : Nat := 4983230072969 + 3 ^ 40 * 1100680 * 2
def baseEnd_1100680 : Nat := 565177886790858818138071

theorem tailTrace_1100680 : CollatzResearch.WordTrace tailWord_1100680 prefixEnd_1100680 565177886790858818138071 := by
  unfold tailWord_1100680
  simp only [CollatzResearch.WordTrace]
  refine ⟨20072548826215908011581747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26763398434954544015442329 20072548826215908011581747)
  ·
    refine ⟨30108823239323862017372621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20072548826215908011581747 30108823239323862017372621)
    ·
      refine ⟨11290808714746448256514733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30108823239323862017372621 11290808714746448256514733)
      ·
        refine ⟨4234053268029918096193025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11290808714746448256514733 4234053268029918096193025)
        ·
          refine ⟨3175539951022438572144769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4234053268029918096193025 3175539951022438572144769)
          ·
            refine ⟨2381654963266828929108577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3175539951022438572144769 2381654963266828929108577)
            ·
              refine ⟨1786241222450121696831433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381654963266828929108577 1786241222450121696831433)
              ·
                refine ⟨1339680916837591272623575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786241222450121696831433 1339680916837591272623575)
                ·
                  refine ⟨2009521375256386908935363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339680916837591272623575 2009521375256386908935363)
                  ·
                    refine ⟨3014282062884580363403045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2009521375256386908935363 3014282062884580363403045)
                    ·
                      refine ⟨565177886790858818138071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3014282062884580363403045 565177886790858818138071)
                      ·
                        rfl

theorem cell23_1100680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_1100680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100680 prefixEnd_1100680 := by exact prefixLift 1100680
  have htrace : WordTrace (prefixWord ++ tailWord_1100680) baseStart_1100680 baseEnd_1100680 := by
    simpa [prefixWord, tailWord_1100680, baseEnd_1100680] using wordTrace_append hprefix tailTrace_1100680
  have hstable : (prefixWord ++ tailWord_1100680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100680).length < 2 ^ (prefixWord ++ tailWord_1100680).sum := by decide
  have hdescent : baseEnd_1100680 < baseStart_1100680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100683 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 3]
def baseStart_1100683 : Nat := 118140960795 + 1100683 * 2 ^ 59
def prefixEnd_1100683 : Nat := 4983230072969 + 3 ^ 40 * 1100683 * 2
def baseEnd_1100683 : Nat := 565179427232822306400557

theorem tailTrace_1100683 : CollatzResearch.WordTrace tailWord_1100683 prefixEnd_1100683 565179427232822306400557 := by
  unfold tailWord_1100683
  simp only [CollatzResearch.WordTrace]
  refine ⟨40145207071420947535522703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26763471380947298357015135 40145207071420947535522703)
  ·
    refine ⟨60217810607131421303284055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40145207071420947535522703 60217810607131421303284055)
    ·
      refine ⟨90326715910697131954926083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60217810607131421303284055 90326715910697131954926083)
      ·
        refine ⟨135490073866045697932389125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90326715910697131954926083 135490073866045697932389125)
        ·
          refine ⟨25404388849883568362322961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135490073866045697932389125 25404388849883568362322961)
          ·
            refine ⟨19053291637412676271742221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25404388849883568362322961 19053291637412676271742221)
            ·
              refine ⟨7144984364029753601903333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19053291637412676271742221 7144984364029753601903333)
              ·
                refine ⟨1339684568255578800356875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7144984364029753601903333 1339684568255578800356875)
                ·
                  refine ⟨2009526852383368200535313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339684568255578800356875 2009526852383368200535313)
                  ·
                    refine ⟨1507145139287526150401485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2009526852383368200535313 1507145139287526150401485)
                    ·
                      refine ⟨565179427232822306400557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507145139287526150401485 565179427232822306400557)
                      ·
                        rfl

theorem cell23_1100683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 3].length) (baseStart_1100683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100683 prefixEnd_1100683 := by exact prefixLift 1100683
  have htrace : WordTrace (prefixWord ++ tailWord_1100683) baseStart_1100683 baseEnd_1100683 := by
    simpa [prefixWord, tailWord_1100683, baseEnd_1100683] using wordTrace_append hprefix tailTrace_1100683
  have hstable : (prefixWord ++ tailWord_1100683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100683).length < 2 ^ (prefixWord ++ tailWord_1100683).sum := by decide
  have hdescent : baseEnd_1100683 < baseStart_1100683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100700 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1100700 : Nat := 118140960795 + 1100700 * 2 ^ 59
def prefixEnd_1100700 : Nat := 4983230072969 + 3 ^ 40 * 1100700 * 2
def baseEnd_1100700 : Nat := 565188156403948739887979

theorem tailTrace_1100700 : CollatzResearch.WordTrace tailWord_1100700 prefixEnd_1100700 565188156403948739887979 := by
  unfold tailWord_1100700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20072913556179679719445777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26763884741572906292594369 20072913556179679719445777)
  ·
    refine ⟨15054685167134759789584333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20072913556179679719445777 15054685167134759789584333)
    ·
      refine ⟨5645506937675534921094125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15054685167134759789584333 5645506937675534921094125)
      ·
        refine ⟨2117065101628325595410297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5645506937675534921094125 2117065101628325595410297)
        ·
          refine ⟨1587798826221244196557723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2117065101628325595410297 1587798826221244196557723)
          ·
            refine ⟨2381698239331866294836585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587798826221244196557723 2381698239331866294836585)
            ·
              refine ⟨1786273679498899721127439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2381698239331866294836585 1786273679498899721127439)
              ·
                refine ⟨2679410519248349581691159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786273679498899721127439 2679410519248349581691159)
                ·
                  refine ⟨4019115778872524372536739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2679410519248349581691159 4019115778872524372536739)
                  ·
                    refine ⟨6028673668308786558805109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4019115778872524372536739 6028673668308786558805109)
                    ·
                      refine ⟨565188156403948739887979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6028673668308786558805109 565188156403948739887979)
                      ·
                        rfl

theorem cell23_1100700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1100700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100700 prefixEnd_1100700 := by exact prefixLift 1100700
  have htrace : WordTrace (prefixWord ++ tailWord_1100700) baseStart_1100700 baseEnd_1100700 := by
    simpa [prefixWord, tailWord_1100700, baseEnd_1100700] using wordTrace_append hprefix tailTrace_1100700
  have hstable : (prefixWord ++ tailWord_1100700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100700).length < 2 ^ (prefixWord ++ tailWord_1100700).sum := by decide
  have hdescent : baseEnd_1100700 < baseStart_1100700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100713 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 3]
def baseStart_1100713 : Nat := 118140960795 + 1100713 * 2 ^ 59
def prefixEnd_1100713 : Nat := 4983230072969 + 3 ^ 40 * 1100713 * 2
def baseEnd_1100713 : Nat := 565194831652457189025419

theorem tailTrace_1100713 : CollatzResearch.WordTrace tailWord_1100713 prefixEnd_1100713 565194831652457189025419 := by
  unfold tailWord_1100713
  simp only [CollatzResearch.WordTrace]
  refine ⟨40146301261312262659114793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26764200840874841772743195 40146301261312262659114793)
  ·
    refine ⟨30109725945984196994336095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40146301261312262659114793 30109725945984196994336095)
    ·
      refine ⟨45164588918976295491504143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30109725945984196994336095 45164588918976295491504143)
      ·
        refine ⟨67746883378464443237256215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45164588918976295491504143 67746883378464443237256215)
        ·
          refine ⟨101620325067696664855884323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67746883378464443237256215 101620325067696664855884323)
          ·
            refine ⟨152430487601544997283826485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101620325067696664855884323 152430487601544997283826485)
            ·
              refine ⟨14290358212644843495358733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152430487601544997283826485 14290358212644843495358733)
              ·
                refine ⟨5358884329741816310759525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14290358212644843495358733 5358884329741816310759525)
                ·
                  refine ⟨1004790811826590558267411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5358884329741816310759525 1004790811826590558267411)
                  ·
                    refine ⟨1507186217739885837401117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1004790811826590558267411 1507186217739885837401117)
                    ·
                      refine ⟨565194831652457189025419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507186217739885837401117 565194831652457189025419)
                      ·
                        rfl

theorem cell23_1100713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 3].length) (baseStart_1100713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100713 prefixEnd_1100713 := by exact prefixLift 1100713
  have htrace : WordTrace (prefixWord ++ tailWord_1100713) baseStart_1100713 baseEnd_1100713 := by
    simpa [prefixWord, tailWord_1100713, baseEnd_1100713] using wordTrace_append hprefix tailTrace_1100713
  have hstable : (prefixWord ++ tailWord_1100713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100713).length < 2 ^ (prefixWord ++ tailWord_1100713).sum := by decide
  have hdescent : baseEnd_1100713 < baseStart_1100713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100724 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1100724 : Nat := 118140960795 + 1100724 * 2 ^ 59
def prefixEnd_1100724 : Nat := 4983230072969 + 3 ^ 40 * 1100724 * 2
def baseEnd_1100724 : Nat := 188400159979885548662623

theorem tailTrace_1100724 : CollatzResearch.WordTrace tailWord_1100724 prefixEnd_1100724 188400159979885548662623 := by
  unfold tailWord_1100724
  simp only [CollatzResearch.WordTrace]
  refine ⟨20073351232136205768882613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26764468309514941025176817 20073351232136205768882613)
  ·
    refine ⟨1881876678012769290832745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20073351232136205768882613 1881876678012769290832745)
    ·
      refine ⟨1411407508509576968124559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1881876678012769290832745 1411407508509576968124559)
      ·
        refine ⟨2117111262764365452186839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411407508509576968124559 2117111262764365452186839)
        ·
          refine ⟨3175666894146548178280259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117111262764365452186839 3175666894146548178280259)
          ·
            refine ⟨4763500341219822267420389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175666894146548178280259 4763500341219822267420389)
            ·
              refine ⟨893156313978716675141323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4763500341219822267420389 893156313978716675141323)
              ·
                refine ⟨1339734470968075012711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893156313978716675141323 1339734470968075012711985)
                ·
                  refine ⟨1004800853226056259533989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1339734470968075012711985 1004800853226056259533989)
                  ·
                    refine ⟨188400159979885548662623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1004800853226056259533989 188400159979885548662623)
                    ·
                      rfl

theorem cell23_1100724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1100724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100724 prefixEnd_1100724 := by exact prefixLift 1100724
  have htrace : WordTrace (prefixWord ++ tailWord_1100724) baseStart_1100724 baseEnd_1100724 := by
    simpa [prefixWord, tailWord_1100724, baseEnd_1100724] using wordTrace_append hprefix tailTrace_1100724
  have hstable : (prefixWord ++ tailWord_1100724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100724).length < 2 ^ (prefixWord ++ tailWord_1100724).sum := by decide
  have hdescent : baseEnd_1100724 < baseStart_1100724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100730 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_1100730 : Nat := 118140960795 + 1100730 * 2 ^ 59
def prefixEnd_1100730 : Nat := 4983230072969 + 3 ^ 40 * 1100730 * 2
def baseEnd_1100730 : Nat := 565203560823583622512841

theorem tailTrace_1100730 : CollatzResearch.WordTrace tailWord_1100730 prefixEnd_1100730 565203560823583622512841 := by
  unfold tailWord_1100730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036730325562668640620911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26764614201500449708322429 10036730325562668640620911)
  ·
    refine ⟨15055095488344002960931367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10036730325562668640620911 15055095488344002960931367)
    ·
      refine ⟨22582643232516004441397051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15055095488344002960931367 22582643232516004441397051)
      ·
        refine ⟨33873964848774006662095577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22582643232516004441397051 33873964848774006662095577)
        ·
          refine ⟨25405473636580504996571683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33873964848774006662095577 25405473636580504996571683)
          ·
            refine ⟨38108210454870757494857525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25405473636580504996571683 38108210454870757494857525)
            ·
              refine ⟨3572644730144133515142893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38108210454870757494857525 3572644730144133515142893)
              ·
                refine ⟨1339741773804050068178585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3572644730144133515142893 1339741773804050068178585)
                ·
                  refine ⟨1004806330353037551133939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1339741773804050068178585 1004806330353037551133939)
                  ·
                    refine ⟨1507209495529556326700909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1004806330353037551133939 1507209495529556326700909)
                    ·
                      refine ⟨565203560823583622512841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507209495529556326700909 565203560823583622512841)
                      ·
                        rfl

theorem cell23_1100730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_1100730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100730 prefixEnd_1100730 := by exact prefixLift 1100730
  have htrace : WordTrace (prefixWord ++ tailWord_1100730) baseStart_1100730 baseEnd_1100730 := by
    simpa [prefixWord, tailWord_1100730, baseEnd_1100730] using wordTrace_append hprefix tailTrace_1100730
  have hstable : (prefixWord ++ tailWord_1100730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100730).length < 2 ^ (prefixWord ++ tailWord_1100730).sum := by decide
  have hdescent : baseEnd_1100730 < baseStart_1100730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100746 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_1100746 : Nat := 118140960795 + 1100746 * 2 ^ 59
def prefixEnd_1100746 : Nat := 4983230072969 + 3 ^ 40 * 1100746 * 2
def baseEnd_1100746 : Nat := 188403925504685186637589

theorem tailTrace_1100746 : CollatzResearch.WordTrace tailWord_1100746 prefixEnd_1100746 188403925504685186637589 := by
  unfold tailWord_1100746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036876217548177323766523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26765003246795139530044061 10036876217548177323766523)
  ·
    refine ⟨15055314326322265985649785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10036876217548177323766523 15055314326322265985649785)
    ·
      refine ⟨11291485744741699489237339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15055314326322265985649785 11291485744741699489237339)
      ·
        refine ⟨16937228617112549233856009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11291485744741699489237339 16937228617112549233856009)
        ·
          refine ⟨12702921462834411925392007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16937228617112549233856009 12702921462834411925392007)
          ·
            refine ⟨19054382194251617888088011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12702921462834411925392007 19054382194251617888088011)
            ·
              refine ⟨28581573291377426832132017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19054382194251617888088011 28581573291377426832132017)
              ·
                refine ⟨21436179968533070124099013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28581573291377426832132017 21436179968533070124099013)
                ·
                  refine ⟨4019283744099950648268565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21436179968533070124099013 4019283744099950648268565)
                  ·
                    refine ⟨188403925504685186637589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4019283744099950648268565 188403925504685186637589)
                    ·
                      rfl

theorem cell23_1100746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_1100746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100746 prefixEnd_1100746 := by exact prefixLift 1100746
  have htrace : WordTrace (prefixWord ++ tailWord_1100746) baseStart_1100746 baseEnd_1100746 := by
    simpa [prefixWord, tailWord_1100746, baseEnd_1100746] using wordTrace_append hprefix tailTrace_1100746
  have hstable : (prefixWord ++ tailWord_1100746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100746).length < 2 ^ (prefixWord ++ tailWord_1100746).sum := by decide
  have hdescent : baseEnd_1100746 < baseStart_1100746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100770 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1100770 : Nat := 118140960795 + 1100770 * 2 ^ 59
def prefixEnd_1100770 : Nat := 4983230072969 + 3 ^ 40 * 1100770 * 2
def baseEnd_1100770 : Nat := 565224100049763466012657

theorem tailTrace_1100770 : CollatzResearch.WordTrace tailWord_1100770 prefixEnd_1100770 565224100049763466012657 := by
  unfold tailWord_1100770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10037095055526440348484941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26765586814737174262626509 10037095055526440348484941)
  ·
    refine ⟨3763910645822415130681853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10037095055526440348484941 3763910645822415130681853)
    ·
      refine ⟨1411466492183405674005695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3763910645822415130681853 1411466492183405674005695)
      ·
        refine ⟨2117199738275108511008543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411466492183405674005695 2117199738275108511008543)
        ·
          refine ⟨3175799607412662766512815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117199738275108511008543 3175799607412662766512815)
          ·
            refine ⟨4763699411118994149769223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175799607412662766512815 4763699411118994149769223)
            ·
              refine ⟨7145549116678491224653835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763699411118994149769223 7145549116678491224653835)
              ·
                refine ⟨10718323675017736836980753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7145549116678491224653835 10718323675017736836980753)
                ·
                  refine ⟨8038742756263302627735565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10718323675017736836980753 8038742756263302627735565)
                  ·
                    refine ⟨3014528533598738485400837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8038742756263302627735565 3014528533598738485400837)
                    ·
                      refine ⟨565224100049763466012657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3014528533598738485400837 565224100049763466012657)
                      ·
                        rfl

theorem cell23_1100770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1100770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100770 prefixEnd_1100770 := by exact prefixLift 1100770
  have htrace : WordTrace (prefixWord ++ tailWord_1100770) baseStart_1100770 baseEnd_1100770 := by
    simpa [prefixWord, tailWord_1100770, baseEnd_1100770] using wordTrace_append hprefix tailTrace_1100770
  have hstable : (prefixWord ++ tailWord_1100770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100770).length < 2 ^ (prefixWord ++ tailWord_1100770).sum := by decide
  have hdescent : baseEnd_1100770 < baseStart_1100770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100783 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_1100783 : Nat := 118140960795 + 1100783 * 2 ^ 59
def prefixEnd_1100783 : Nat := 4983230072969 + 3 ^ 40 * 1100783 * 2
def baseEnd_1100783 : Nat := 565230775298271915150097

theorem tailTrace_1100783 : CollatzResearch.WordTrace tailWord_1100783 prefixEnd_1100783 565230775298271915150097 := by
  unfold tailWord_1100783
  simp only [CollatzResearch.WordTrace]
  refine ⟨40148854371058664614163003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26765902914039109742775335 40148854371058664614163003)
  ·
    refine ⟨60223281556587996921244505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40148854371058664614163003 60223281556587996921244505)
    ·
      refine ⟨45167461167440997690933379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60223281556587996921244505 45167461167440997690933379)
      ·
        refine ⟨67751191751161496536400069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45167461167440997690933379 67751191751161496536400069)
        ·
          refine ⟨12703348453342780600575013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67751191751161496536400069 12703348453342780600575013)
          ·
            refine ⟨2381877835001771362607815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12703348453342780600575013 2381877835001771362607815)
            ·
              refine ⟨3572816752502657043911723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381877835001771362607815 3572816752502657043911723)
              ·
                refine ⟨5359225128753985565867585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3572816752502657043911723 5359225128753985565867585)
                ·
                  refine ⟨4019418846565489174400689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5359225128753985565867585 4019418846565489174400689)
                  ·
                    refine ⟨3014564134924116880800517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4019418846565489174400689 3014564134924116880800517)
                    ·
                      refine ⟨565230775298271915150097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3014564134924116880800517 565230775298271915150097)
                      ·
                        rfl

theorem cell23_1100783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_1100783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100783 prefixEnd_1100783 := by exact prefixLift 1100783
  have htrace : WordTrace (prefixWord ++ tailWord_1100783) baseStart_1100783 baseEnd_1100783 := by
    simpa [prefixWord, tailWord_1100783, baseEnd_1100783] using wordTrace_append hprefix tailTrace_1100783
  have hstable : (prefixWord ++ tailWord_1100783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100783).length < 2 ^ (prefixWord ++ tailWord_1100783).sum := by decide
  have hdescent : baseEnd_1100783 < baseStart_1100783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100810 : List Nat := [3, 1, 2, 2, 3, 1, 1, 5, 5]
def baseStart_1100810 : Nat := 118140960795 + 1100810 * 2 ^ 59
def prefixEnd_1100810 : Nat := 4983230072969 + 3 ^ 40 * 1100810 * 2
def baseEnd_1100810 : Nat := 62804959919549256612497

theorem tailTrace_1100810 : CollatzResearch.WordTrace tailWord_1100810 prefixEnd_1100810 62804959919549256612497 := by
  unfold tailWord_1100810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10037459785490212056348971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26766559427973898816930589 10037459785490212056348971)
  ·
    refine ⟨15056189678235318084523457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10037459785490212056348971 15056189678235318084523457)
    ·
      refine ⟨11292142258676488563392593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15056189678235318084523457 11292142258676488563392593)
      ·
        refine ⟨8469106694007366422544445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11292142258676488563392593 8469106694007366422544445)
        ·
          refine ⟨3175915010252762408454167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8469106694007366422544445 3175915010252762408454167)
          ·
            refine ⟨4763872515379143612681251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3175915010252762408454167 4763872515379143612681251)
            ·
              refine ⟨7145808773068715419021877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4763872515379143612681251 7145808773068715419021877)
              ·
                refine ⟨669919572475192070533301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7145808773068715419021877 669919572475192070533301)
                ·
                  refine ⟨62804959919549256612497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 669919572475192070533301 62804959919549256612497)
                  ·
                    rfl

theorem cell23_1100810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_1100810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100810 prefixEnd_1100810 := by exact prefixLift 1100810
  have htrace : WordTrace (prefixWord ++ tailWord_1100810) baseStart_1100810 baseEnd_1100810 := by
    simpa [prefixWord, tailWord_1100810, baseEnd_1100810] using wordTrace_append hprefix tailTrace_1100810
  have hstable : (prefixWord ++ tailWord_1100810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100810).length < 2 ^ (prefixWord ++ tailWord_1100810).sum := by decide
  have hdescent : baseEnd_1100810 < baseStart_1100810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100877 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1100877 : Nat := 118140960795 + 1100877 * 2 ^ 59
def prefixEnd_1100877 : Nat := 4983230072969 + 3 ^ 40 * 1100877 * 2
def baseEnd_1100877 : Nat := 565279042479794547374665

theorem tailTrace_1100877 : CollatzResearch.WordTrace tailWord_1100877 prefixEnd_1100877 565279042479794547374665 := by
  unfold tailWord_1100877
  simp only [CollatzResearch.WordTrace]
  refine ⟨40152282832718118668084885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26768188555145412445389923 40152282832718118668084885)
  ·
    refine ⟨1882138257783661812566479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40152282832718118668084885 1882138257783661812566479)
    ·
      refine ⟨2823207386675492718849719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1882138257783661812566479 2823207386675492718849719)
      ·
        refine ⟨4234811080013239078274579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823207386675492718849719 4234811080013239078274579)
        ·
          refine ⟨6352216620019858617411869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234811080013239078274579 6352216620019858617411869)
          ·
            refine ⟨2382081232507446981529451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6352216620019858617411869 2382081232507446981529451)
            ·
              refine ⟨3573121848761170472294177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382081232507446981529451 3573121848761170472294177)
              ·
                refine ⟨2679841386570877854220633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3573121848761170472294177 2679841386570877854220633)
                ·
                  refine ⟨2009881039928158390665475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679841386570877854220633 2009881039928158390665475)
                  ·
                    refine ⟨3014821559892237585998213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2009881039928158390665475 3014821559892237585998213)
                    ·
                      refine ⟨565279042479794547374665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3014821559892237585998213 565279042479794547374665)
                      ·
                        rfl

theorem cell23_1100877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1100877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100877 prefixEnd_1100877 := by exact prefixLift 1100877
  have htrace : WordTrace (prefixWord ++ tailWord_1100877) baseStart_1100877 baseEnd_1100877 := by
    simpa [prefixWord, tailWord_1100877, baseEnd_1100877] using wordTrace_append hprefix tailTrace_1100877
  have hstable : (prefixWord ++ tailWord_1100877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100877).length < 2 ^ (prefixWord ++ tailWord_1100877).sum := by decide
  have hdescent : baseEnd_1100877 < baseStart_1100877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100920 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 1, 5, 2]
def baseStart_1100920 : Nat := 118140960795 + 1100920 * 2 ^ 59
def prefixEnd_1100920 : Nat := 4983230072969 + 3 ^ 40 * 1100920 * 2
def baseEnd_1100920 : Nat := 565301122147937879136967

theorem tailTrace_1100920 : CollatzResearch.WordTrace tailWord_1100920 prefixEnd_1100920 565301122147937879136967 := by
  unfold tailWord_1100920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20076925585781168505950107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26769234114374891341266809 20076925585781168505950107)
  ·
    refine ⟨30115388378671752758925161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20076925585781168505950107 30115388378671752758925161)
    ·
      refine ⟨22586541284003814569193871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30115388378671752758925161 22586541284003814569193871)
      ·
        refine ⟨33879811926005721853790807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22586541284003814569193871 33879811926005721853790807)
        ·
          refine ⟨50819717889008582780686211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33879811926005721853790807 50819717889008582780686211)
          ·
            refine ⟨76229576833512874171029317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50819717889008582780686211 76229576833512874171029317)
            ·
              refine ⟨14293045656283663907067997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76229576833512874171029317 14293045656283663907067997)
              ·
                refine ⟨5359892121106373965150499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14293045656283663907067997 5359892121106373965150499)
                ·
                  refine ⟨8039838181659560947725749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5359892121106373965150499 8039838181659560947725749)
                  ·
                    refine ⟨753734829530583838849289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8039838181659560947725749 753734829530583838849289)
                    ·
                      refine ⟨565301122147937879136967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753734829530583838849289 565301122147937879136967)
                      ·
                        rfl

theorem cell23_1100920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_1100920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100920 prefixEnd_1100920 := by exact prefixLift 1100920
  have htrace : WordTrace (prefixWord ++ tailWord_1100920) baseStart_1100920 baseEnd_1100920 := by
    simpa [prefixWord, tailWord_1100920, baseEnd_1100920] using wordTrace_append hprefix tailTrace_1100920
  have hstable : (prefixWord ++ tailWord_1100920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100920).length < 2 ^ (prefixWord ++ tailWord_1100920).sum := by decide
  have hdescent : baseEnd_1100920 < baseStart_1100920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100937 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 2, 3, 2]
def baseStart_1100937 : Nat := 118140960795 + 1100937 * 2 ^ 59
def prefixEnd_1100937 : Nat := 4983230072969 + 3 ^ 40 * 1100937 * 2
def baseEnd_1100937 : Nat := 565309851319064312624389

theorem tailTrace_1100937 : CollatzResearch.WordTrace tailWord_1100937 prefixEnd_1100937 565309851319064312624389 := by
  unfold tailWord_1100937
  simp only [CollatzResearch.WordTrace]
  refine ⟨40154471212500748915269065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26769647475000499276846043 40154471212500748915269065)
  ·
    refine ⟨30115853409375561686451799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40154471212500748915269065 30115853409375561686451799)
    ·
      refine ⟨45173780114063342529677699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30115853409375561686451799 45173780114063342529677699)
      ·
        refine ⟨67760670171095013794516549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45173780114063342529677699 67760670171095013794516549)
        ·
          refine ⟨12705125657080315086471853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67760670171095013794516549 12705125657080315086471853)
          ·
            refine ⟨4764422121405118157426945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12705125657080315086471853 4764422121405118157426945)
            ·
              refine ⟨3573316591053838618070209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4764422121405118157426945 3573316591053838618070209)
              ·
                refine ⟨2679987443290378963552657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3573316591053838618070209 2679987443290378963552657)
                ·
                  refine ⟨2009990582467784222664493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2679987443290378963552657 2009990582467784222664493)
                  ·
                    refine ⟨753746468425419083499185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009990582467784222664493 753746468425419083499185)
                    ·
                      refine ⟨565309851319064312624389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753746468425419083499185 565309851319064312624389)
                      ·
                        rfl

theorem cell23_1100937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 3, 2].length) (baseStart_1100937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100937 prefixEnd_1100937 := by exact prefixLift 1100937
  have htrace : WordTrace (prefixWord ++ tailWord_1100937) baseStart_1100937 baseEnd_1100937 := by
    simpa [prefixWord, tailWord_1100937, baseEnd_1100937] using wordTrace_append hprefix tailTrace_1100937
  have hstable : (prefixWord ++ tailWord_1100937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100937).length < 2 ^ (prefixWord ++ tailWord_1100937).sum := by decide
  have hdescent : baseEnd_1100937 < baseStart_1100937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100960 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 1, 6]
def baseStart_1100960 : Nat := 118140960795 + 1100960 * 2 ^ 59
def prefixEnd_1100960 : Nat := 4983230072969 + 3 ^ 40 * 1100960 * 2
def baseEnd_1100960 : Nat := 188440553791372574212261

theorem tailTrace_1100960 : CollatzResearch.WordTrace tailWord_1100960 prefixEnd_1100960 188440553791372574212261 := by
  unfold tailWord_1100960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20077655045708711921678167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26770206727611615895570889 20077655045708711921678167)
  ·
    refine ⟨30116482568563067882517251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20077655045708711921678167 30116482568563067882517251)
    ·
      refine ⟨45174723852844601823775877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30116482568563067882517251 45174723852844601823775877)
      ·
        refine ⟨8470260722408362841957977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45174723852844601823775877 8470260722408362841957977)
        ·
          refine ⟨6352695541806272131468483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8470260722408362841957977 6352695541806272131468483)
          ·
            refine ⟨9529043312709408197202725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6352695541806272131468483 9529043312709408197202725)
            ·
              refine ⟨1786695621133014036975511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9529043312709408197202725 1786695621133014036975511)
              ·
                refine ⟨2680043431699521055463267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786695621133014036975511 2680043431699521055463267)
                ·
                  refine ⟨4020065147549281583194901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680043431699521055463267 4020065147549281583194901)
                  ·
                    refine ⟨188440553791372574212261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4020065147549281583194901 188440553791372574212261)
                    ·
                      rfl

theorem cell23_1100960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_1100960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100960 prefixEnd_1100960 := by exact prefixLift 1100960
  have htrace : WordTrace (prefixWord ++ tailWord_1100960) baseStart_1100960 baseEnd_1100960 := by
    simpa [prefixWord, tailWord_1100960, baseEnd_1100960] using wordTrace_append hprefix tailTrace_1100960
  have hstable : (prefixWord ++ tailWord_1100960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100960).length < 2 ^ (prefixWord ++ tailWord_1100960).sum := by decide
  have hdescent : baseEnd_1100960 < baseStart_1100960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
