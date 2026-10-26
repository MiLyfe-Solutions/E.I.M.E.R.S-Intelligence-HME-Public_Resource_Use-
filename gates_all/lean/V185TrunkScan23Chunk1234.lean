import V185TrunkScan23Chunk1233

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7311258 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3]
def baseStart_7311258 : Nat := 118140960795 + 7311258 * 2 ^ 59
def prefixEnd_7311258 : Nat := 4983230072969 + 3 ^ 40 * 7311258 * 2
def baseEnd_7311258 : Nat := 3754189543029860903151143

theorem tailTrace_7311258 : CollatzResearch.WordTrace tailWord_7311258 prefixEnd_7311258 3754189543029860903151143 := by
  unfold tailWord_7311258
  simp only [CollatzResearch.WordTrace]
  refine ⟨66665871636642101075083607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177775657697712269533556285 66665871636642101075083607)
  ·
    refine ⟨99998807454963151612625411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66665871636642101075083607 99998807454963151612625411)
    ·
      refine ⟨149998211182444727418938117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99998807454963151612625411 149998211182444727418938117)
      ·
        refine ⟨28124664596708386391050897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149998211182444727418938117 28124664596708386391050897)
        ·
          refine ⟨21093498447531289793288173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28124664596708386391050897 21093498447531289793288173)
          ·
            refine ⟨7910061917824233672483065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21093498447531289793288173 7910061917824233672483065)
            ·
              refine ⟨5932546438368175254362299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910061917824233672483065 5932546438368175254362299)
              ·
                refine ⟨8898819657552262881543449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932546438368175254362299 8898819657552262881543449)
                ·
                  refine ⟨6674114743164197161157587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8898819657552262881543449 6674114743164197161157587)
                  ·
                    refine ⟨10011172114746295741736381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6674114743164197161157587 10011172114746295741736381)
                    ·
                      refine ⟨3754189543029860903151143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10011172114746295741736381 3754189543029860903151143)
                      ·
                        rfl

theorem cell23_7311258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_7311258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311258 prefixEnd_7311258 := by exact prefixLift 7311258
  have htrace : WordTrace (prefixWord ++ tailWord_7311258) baseStart_7311258 baseEnd_7311258 := by
    simpa [prefixWord, tailWord_7311258, baseEnd_7311258] using wordTrace_append hprefix tailTrace_7311258
  have hstable : (prefixWord ++ tailWord_7311258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311258).length < 2 ^ (prefixWord ++ tailWord_7311258).sum := by decide
  have hdescent : baseEnd_7311258 < baseStart_7311258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311287 : List Nat := [1, 1, 3, 1, 3, 1, 1, 7, 5]
def baseStart_7311287 : Nat := 118140960795 + 7311287 * 2 ^ 59
def prefixEnd_7311287 : Nat := 4983230072969 + 3 ^ 40 * 7311287 * 2
def baseEnd_7311287 : Nat := 417133825996537921076501

theorem tailTrace_7311287 : CollatzResearch.WordTrace tailWord_7311287 prefixEnd_7311287 417133825996537921076501 := by
  unfold tailWord_7311287
  simp only [CollatzResearch.WordTrace]
  refine ⟨266664544263463342253140115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177776362842308894835426743 266664544263463342253140115)
  ·
    refine ⟨399996816395195013379710173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266664544263463342253140115 399996816395195013379710173)
    ·
      refine ⟨149998806148198130017391315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399996816395195013379710173 149998806148198130017391315)
      ·
        refine ⟨224998209222297195026086973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149998806148198130017391315 224998209222297195026086973)
        ·
          refine ⟨84374328458361448134782615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224998209222297195026086973 84374328458361448134782615)
          ·
            refine ⟨126561492687542172202173923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84374328458361448134782615 126561492687542172202173923)
            ·
              refine ⟨189842239031313258303260885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126561492687542172202173923 189842239031313258303260885)
              ·
                refine ⟨4449427477296404491482677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 189842239031313258303260885 4449427477296404491482677)
                ·
                  refine ⟨417133825996537921076501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449427477296404491482677 417133825996537921076501)
                  ·
                    rfl

theorem cell23_7311287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 5].length) (baseStart_7311287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311287 prefixEnd_7311287 := by exact prefixLift 7311287
  have htrace : WordTrace (prefixWord ++ tailWord_7311287) baseStart_7311287 baseEnd_7311287 := by
    simpa [prefixWord, tailWord_7311287, baseEnd_7311287] using wordTrace_append hprefix tailTrace_7311287
  have hstable : (prefixWord ++ tailWord_7311287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311287).length < 2 ^ (prefixWord ++ tailWord_7311287).sum := by decide
  have hdescent : baseEnd_7311287 < baseStart_7311287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311304 : List Nat := [2, 1, 3, 1, 4, 2, 1, 4, 5]
def baseStart_7311304 : Nat := 118140960795 + 7311304 * 2 ^ 59
def prefixEnd_7311304 : Nat := 4983230072969 + 3 ^ 40 * 7311304 * 2
def baseEnd_7311304 : Nat := 417134795904440858130659

theorem tailTrace_7311304 : CollatzResearch.WordTrace tailWord_7311304 prefixEnd_7311304 417134795904440858130659 := by
  unfold tailWord_7311304
  simp only [CollatzResearch.WordTrace]
  refine ⟨133332582152200877078254483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177776776202934502771005977 133332582152200877078254483)
  ·
    refine ⟨199998873228301315617381725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133332582152200877078254483 199998873228301315617381725)
    ·
      refine ⟨74999577460612993356518147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199998873228301315617381725 74999577460612993356518147)
      ·
        refine ⟨112499366190919490034777221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74999577460612993356518147 112499366190919490034777221)
        ·
          refine ⟨21093631160797404381520729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112499366190919490034777221 21093631160797404381520729)
          ·
            refine ⟨15820223370598053286140547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21093631160797404381520729 15820223370598053286140547)
            ·
              refine ⟨23730335055897079929210821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15820223370598053286140547 23730335055897079929210821)
              ·
                refine ⟨4449437822980702486727029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23730335055897079929210821 4449437822980702486727029)
                ·
                  refine ⟨417134795904440858130659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449437822980702486727029 417134795904440858130659)
                  ·
                    rfl

theorem cell23_7311304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 5].length) (baseStart_7311304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311304 prefixEnd_7311304 := by exact prefixLift 7311304
  have htrace : WordTrace (prefixWord ++ tailWord_7311304) baseStart_7311304 baseEnd_7311304 := by
    simpa [prefixWord, tailWord_7311304, baseEnd_7311304] using wordTrace_append hprefix tailTrace_7311304
  have hstable : (prefixWord ++ tailWord_7311304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311304).length < 2 ^ (prefixWord ++ tailWord_7311304).sum := by decide
  have hdescent : baseEnd_7311304 < baseStart_7311304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311307 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 7, 2]
def baseStart_7311307 : Nat := 118140960795 + 7311307 * 2 ^ 59
def prefixEnd_7311307 : Nat := 4983230072969 + 3 ^ 40 * 7311307 * 2
def baseEnd_7311307 : Nat := 3754214703581931211438417

theorem tailTrace_7311307 : CollatzResearch.WordTrace tailWord_7311307 prefixEnd_7311307 3754214703581931211438417 := by
  unfold tailWord_7311307
  simp only [CollatzResearch.WordTrace]
  refine ⟨266665273723390885668868175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177776849148927257112578783 266665273723390885668868175)
  ·
    refine ⟨399997910585086328503302263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266665273723390885668868175 399997910585086328503302263)
    ·
      refine ⟨599996865877629492754953395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399997910585086328503302263 599996865877629492754953395)
      ·
        refine ⟨899995298816444239132430093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599996865877629492754953395 899995298816444239132430093)
        ·
          refine ⟨337498237056166589674661285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 899995298816444239132430093 337498237056166589674661285)
          ·
            refine ⟨63280919448031235563998991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337498237056166589674661285 63280919448031235563998991)
            ·
              refine ⟨94921379172046853345998487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63280919448031235563998991 94921379172046853345998487)
              ·
                refine ⟨142382068758070280018997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94921379172046853345998487 142382068758070280018997731)
                ·
                  refine ⟨213573103137105420028496597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142382068758070280018997731 213573103137105420028496597)
                  ·
                    refine ⟨5005619604775908281917889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213573103137105420028496597 5005619604775908281917889)
                    ·
                      refine ⟨3754214703581931211438417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005619604775908281917889 3754214703581931211438417)
                      ·
                        rfl

theorem cell23_7311307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7, 2].length) (baseStart_7311307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311307 prefixEnd_7311307 := by exact prefixLift 7311307
  have htrace : WordTrace (prefixWord ++ tailWord_7311307) baseStart_7311307 baseEnd_7311307 := by
    simpa [prefixWord, tailWord_7311307, baseEnd_7311307] using wordTrace_append hprefix tailTrace_7311307
  have hstable : (prefixWord ++ tailWord_7311307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311307).length < 2 ^ (prefixWord ++ tailWord_7311307).sum := by decide
  have hdescent : baseEnd_7311307 < baseStart_7311307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311366 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_7311366 : Nat := 118140960795 + 7311366 * 2 ^ 59
def prefixEnd_7311366 : Nat := 4983230072969 + 3 ^ 40 * 7311366 * 2
def baseEnd_7311366 : Nat := 3754244998940546480600647

theorem tailTrace_7311366 : CollatzResearch.WordTrace tailWord_7311366 prefixEnd_7311366 3754244998940546480600647 := by
  unfold tailWord_7311366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333357050943035585789561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177778283753451425830177301 8333357050943035585789561)
  ·
    refine ⟨6250017788207276689342171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8333357050943035585789561 6250017788207276689342171)
    ·
      refine ⟨9375026682310915034013257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6250017788207276689342171 9375026682310915034013257)
      ·
        refine ⟨7031270011733186275509943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9375026682310915034013257 7031270011733186275509943)
        ·
          refine ⟨10546905017599779413264915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031270011733186275509943 10546905017599779413264915)
          ·
            refine ⟨15820357526399669119897373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10546905017599779413264915 15820357526399669119897373)
            ·
              refine ⟨5932634072399875919961515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15820357526399669119897373 5932634072399875919961515)
              ·
                refine ⟨8898951108599813879942273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932634072399875919961515 8898951108599813879942273)
                ·
                  refine ⟨6674213331449860409956705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8898951108599813879942273 6674213331449860409956705)
                  ·
                    refine ⟨5005659998587395307467529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6674213331449860409956705 5005659998587395307467529)
                    ·
                      refine ⟨3754244998940546480600647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005659998587395307467529 3754244998940546480600647)
                      ·
                        rfl

theorem cell23_7311366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_7311366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311366 prefixEnd_7311366 := by exact prefixLift 7311366
  have htrace : WordTrace (prefixWord ++ tailWord_7311366) baseStart_7311366 baseEnd_7311366 := by
    simpa [prefixWord, tailWord_7311366, baseEnd_7311366] using wordTrace_append hprefix tailTrace_7311366
  have hstable : (prefixWord ++ tailWord_7311366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311366).length < 2 ^ (prefixWord ++ tailWord_7311366).sum := by decide
  have hdescent : baseEnd_7311366 < baseStart_7311366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311447 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_7311447 : Nat := 118140960795 + 7311447 * 2 ^ 59
def prefixEnd_7311447 : Nat := 4983230072969 + 3 ^ 40 * 7311447 * 2
def baseEnd_7311447 : Nat := 3754286590873560663687773

theorem tailTrace_7311447 : CollatzResearch.WordTrace tailWord_7311447 prefixEnd_7311447 3754286590873560663687773 := by
  unfold tailWord_7311447
  simp only [CollatzResearch.WordTrace]
  refine ⟨266670379942883689578964595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177780253295255793052643063 266670379942883689578964595)
  ·
    refine ⟨400005569914325534368446893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266670379942883689578964595 400005569914325534368446893)
    ·
      refine ⟨150002088717872075388167585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400005569914325534368446893 150002088717872075388167585)
      ·
        refine ⟨112501566538404056541125689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150002088717872075388167585 112501566538404056541125689)
        ·
          refine ⟨84376174903803042405844267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112501566538404056541125689 84376174903803042405844267)
          ·
            refine ⟨126564262355704563608766401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84376174903803042405844267 126564262355704563608766401)
            ·
              refine ⟨94923196766778422706574801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126564262355704563608766401 94923196766778422706574801)
              ·
                refine ⟨71192397575083817029931101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94923196766778422706574801 71192397575083817029931101)
                ·
                  refine ⟨26697149090656431386224163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71192397575083817029931101 26697149090656431386224163)
                  ·
                    refine ⟨40045723635984647079336245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26697149090656431386224163 40045723635984647079336245)
                    ·
                      refine ⟨3754286590873560663687773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40045723635984647079336245 3754286590873560663687773)
                      ·
                        rfl

theorem cell23_7311447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_7311447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311447 prefixEnd_7311447 := by exact prefixLift 7311447
  have htrace : WordTrace (prefixWord ++ tailWord_7311447) baseStart_7311447 baseEnd_7311447 := by
    simpa [prefixWord, tailWord_7311447, baseEnd_7311447] using wordTrace_append hprefix tailTrace_7311447
  have hstable : (prefixWord ++ tailWord_7311447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311447).length < 2 ^ (prefixWord ++ tailWord_7311447).sum := by decide
  have hdescent : baseEnd_7311447 < baseStart_7311447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311471 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 2, 4]
def baseStart_7311471 : Nat := 118140960795 + 7311471 * 2 ^ 59
def prefixEnd_7311471 : Nat := 4983230072969 + 3 ^ 40 * 7311471 * 2
def baseEnd_7311471 : Nat := 1251432971469756189929221

theorem tailTrace_7311471 : CollatzResearch.WordTrace tailWord_7311471 prefixEnd_7311471 1251432971469756189929221 := by
  unfold tailWord_7311471
  simp only [CollatzResearch.WordTrace]
  refine ⟨266671255294796741677838267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177780836863197827785225511 266671255294796741677838267)
  ·
    refine ⟨400006882942195112516757401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266671255294796741677838267 400006882942195112516757401)
    ·
      refine ⟨300005162206646334387568051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400006882942195112516757401 300005162206646334387568051)
      ·
        refine ⟨450007743309969501581352077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300005162206646334387568051 450007743309969501581352077)
        ·
          refine ⟨168752903741238563093007029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450007743309969501581352077 168752903741238563093007029)
          ·
            refine ⟨15820584725741115289969409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168752903741238563093007029 15820584725741115289969409)
            ·
              refine ⟨11865438544305836467477057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15820584725741115289969409 11865438544305836467477057)
              ·
                refine ⟨8899078908229377350607793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11865438544305836467477057 8899078908229377350607793)
                ·
                  refine ⟨6674309181172033012955845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8899078908229377350607793 6674309181172033012955845)
                  ·
                    refine ⟨1251432971469756189929221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674309181172033012955845 1251432971469756189929221)
                    ·
                      rfl

theorem cell23_7311471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_7311471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311471 prefixEnd_7311471 := by exact prefixLift 7311471
  have htrace : WordTrace (prefixWord ++ tailWord_7311471) baseStart_7311471 baseEnd_7311471 := by
    simpa [prefixWord, tailWord_7311471, baseEnd_7311471] using wordTrace_append hprefix tailTrace_7311471
  have hstable : (prefixWord ++ tailWord_7311471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311471).length < 2 ^ (prefixWord ++ tailWord_7311471).sum := by decide
  have hdescent : baseEnd_7311471 < baseStart_7311471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311484 : List Nat := [2, 2, 2, 1, 1, 6, 1, 8]
def baseStart_7311484 : Nat := 118140960795 + 7311484 * 2 ^ 59
def prefixEnd_7311484 : Nat := 4983230072969 + 3 ^ 40 * 7311484 * 2
def baseEnd_7311484 : Nat := 139048355172510259960189

theorem tailTrace_7311484 : CollatzResearch.WordTrace tailWord_7311484 prefixEnd_7311484 139048355172510259960189 := by
  unfold tailWord_7311484
  simp only [CollatzResearch.WordTrace]
  refine ⟨133335864721874822449030753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177781152962499763265374337 133335864721874822449030753)
  ·
    refine ⟨100001898541406116836773065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133335864721874822449030753 100001898541406116836773065)
    ·
      refine ⟨75001423906054587627579799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100001898541406116836773065 75001423906054587627579799)
      ·
        refine ⟨112502135859081881441369699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75001423906054587627579799 112502135859081881441369699)
        ·
          refine ⟨168753203788622822162054549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112502135859081881441369699 168753203788622822162054549)
          ·
            refine ⟨7910306427591694788846307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168753203788622822162054549 7910306427591694788846307)
            ·
              refine ⟨11865459641387542183269461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7910306427591694788846307 11865459641387542183269461)
              ·
                refine ⟨139048355172510259960189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11865459641387542183269461 139048355172510259960189)
                ·
                  rfl

theorem cell23_7311484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 8].length) (baseStart_7311484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311484 prefixEnd_7311484 := by exact prefixLift 7311484
  have htrace : WordTrace (prefixWord ++ tailWord_7311484) baseStart_7311484 baseEnd_7311484 := by
    simpa [prefixWord, tailWord_7311484, baseEnd_7311484] using wordTrace_append hprefix tailTrace_7311484
  have hstable : (prefixWord ++ tailWord_7311484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311484).length < 2 ^ (prefixWord ++ tailWord_7311484).sum := by decide
  have hdescent : baseEnd_7311484 < baseStart_7311484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311497 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 2, 7]
def baseStart_7311497 : Nat := 118140960795 + 7311497 * 2 ^ 59
def prefixEnd_7311497 : Nat := 4983230072969 + 3 ^ 40 * 7311497 * 2
def baseEnd_7311497 : Nat := 1251437421635428489354181

theorem tailTrace_7311497 : CollatzResearch.WordTrace tailWord_7311497 prefixEnd_7311497 1251437421635428489354181 := by
  unfold tailWord_7311497
  simp only [CollatzResearch.WordTrace]
  refine ⟨266672203592702548118284745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177781469061801698745523163 266672203592702548118284745)
  ·
    refine ⟨200004152694526911088713559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266672203592702548118284745 200004152694526911088713559)
    ·
      refine ⟨300006229041790366633070339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200004152694526911088713559 300006229041790366633070339)
      ·
        refine ⟨450009343562685549949605509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300006229041790366633070339 450009343562685549949605509)
        ·
          refine ⟨84376751918003540615551033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450009343562685549949605509 84376751918003540615551033)
          ·
            refine ⟨63282563938502655461663275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84376751918003540615551033 63282563938502655461663275)
            ·
              refine ⟨94923845907753983192494913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63282563938502655461663275 94923845907753983192494913)
              ·
                refine ⟨71192884430815487394371185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94923845907753983192494913 71192884430815487394371185)
                ·
                  refine ⟨53394663323111615545778389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71192884430815487394371185 53394663323111615545778389)
                  ·
                    refine ⟨1251437421635428489354181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53394663323111615545778389 1251437421635428489354181)
                    ·
                      rfl

theorem cell23_7311497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_7311497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311497 prefixEnd_7311497 := by exact prefixLift 7311497
  have htrace : WordTrace (prefixWord ++ tailWord_7311497) baseStart_7311497 baseEnd_7311497 := by
    simpa [prefixWord, tailWord_7311497, baseEnd_7311497] using wordTrace_append hprefix tailTrace_7311497
  have hstable : (prefixWord ++ tailWord_7311497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311497).length < 2 ^ (prefixWord ++ tailWord_7311497).sum := by decide
  have hdescent : baseEnd_7311497 < baseStart_7311497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311507 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5]
def baseStart_7311507 : Nat := 118140960795 + 7311507 * 2 ^ 59
def prefixEnd_7311507 : Nat := 4983230072969 + 3 ^ 40 * 7311507 * 2
def baseEnd_7311507 : Nat := 3754317399712830428937497

theorem tailTrace_7311507 : CollatzResearch.WordTrace tailWord_7311507 prefixEnd_7311507 3754317399712830428937497 := by
  unfold tailWord_7311507
  simp only [CollatzResearch.WordTrace]
  refine ⟨266672568322666319826148775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177781712215110879884099183 266672568322666319826148775)
  ·
    refine ⟨400008852483999479739223163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266672568322666319826148775 400008852483999479739223163)
    ·
      refine ⟨600013278725999219608834745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400008852483999479739223163 600013278725999219608834745)
      ·
        refine ⟨450009959044499414706626059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600013278725999219608834745 450009959044499414706626059)
        ·
          refine ⟨675014938566749122059939089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450009959044499414706626059 675014938566749122059939089)
          ·
            refine ⟨506261203925061841544954317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675014938566749122059939089 506261203925061841544954317)
            ·
              refine ⟨189847951471898190579357869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506261203925061841544954317 189847951471898190579357869)
              ·
                refine ⟨71192981801961821467259201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189847951471898190579357869 71192981801961821467259201)
                ·
                  refine ⟨53394736351471366100444401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71192981801961821467259201 53394736351471366100444401)
                  ·
                    refine ⟨40046052263603524575333301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53394736351471366100444401 40046052263603524575333301)
                    ·
                      refine ⟨3754317399712830428937497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40046052263603524575333301 3754317399712830428937497)
                      ·
                        rfl

theorem cell23_7311507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_7311507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311507 prefixEnd_7311507 := by exact prefixLift 7311507
  have htrace : WordTrace (prefixWord ++ tailWord_7311507) baseStart_7311507 baseEnd_7311507 := by
    simpa [prefixWord, tailWord_7311507, baseEnd_7311507] using wordTrace_append hprefix tailTrace_7311507
  have hstable : (prefixWord ++ tailWord_7311507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311507).length < 2 ^ (prefixWord ++ tailWord_7311507).sum := by decide
  have hdescent : baseEnd_7311507 < baseStart_7311507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311512 : List Nat := [2, 1, 2, 4, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7311512 : Nat := 118140960795 + 7311512 * 2 ^ 59
def prefixEnd_7311512 : Nat := 4983230072969 + 3 ^ 40 * 7311512 * 2
def baseEnd_7311512 : Nat := 3754319967116102909374975

theorem tailTrace_7311512 : CollatzResearch.WordTrace tailWord_7311512 prefixEnd_7311512 3754319967116102909374975 := by
  unfold tailWord_7311512
  simp only [CollatzResearch.WordTrace]
  refine ⟨133336375343824102840040395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177781833791765470453387193 133336375343824102840040395)
  ·
    refine ⟨200004563015736154260060593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133336375343824102840040395 200004563015736154260060593)
    ·
      refine ⟨150003422261802115695045445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200004563015736154260060593 150003422261802115695045445)
      ·
        refine ⟨28125641674087896692821021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150003422261802115695045445 28125641674087896692821021)
        ·
          refine ⟨10547115627782961259807883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28125641674087896692821021 10547115627782961259807883)
          ·
            refine ⟨15820673441674441889711825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547115627782961259807883 15820673441674441889711825)
            ·
              refine ⟨11865505081255831417283869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15820673441674441889711825 11865505081255831417283869)
              ·
                refine ⟨4449564405470936781481451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11865505081255831417283869 4449564405470936781481451)
                ·
                  refine ⟨6674346608206405172222177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449564405470936781481451 6674346608206405172222177)
                  ·
                    refine ⟨5005759956154803879166633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6674346608206405172222177 5005759956154803879166633)
                    ·
                      refine ⟨3754319967116102909374975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005759956154803879166633 3754319967116102909374975)
                      ·
                        rfl

theorem cell23_7311512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7311512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311512 prefixEnd_7311512 := by exact prefixLift 7311512
  have htrace : WordTrace (prefixWord ++ tailWord_7311512) baseStart_7311512 baseEnd_7311512 := by
    simpa [prefixWord, tailWord_7311512, baseEnd_7311512] using wordTrace_append hprefix tailTrace_7311512
  have hstable : (prefixWord ++ tailWord_7311512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311512).length < 2 ^ (prefixWord ++ tailWord_7311512).sum := by decide
  have hdescent : baseEnd_7311512 < baseStart_7311512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311591 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 7]
def baseStart_7311591 : Nat := 118140960795 + 7311591 * 2 ^ 59
def prefixEnd_7311591 : Nat := 4983230072969 + 3 ^ 40 * 7311591 * 2
def baseEnd_7311591 : Nat := 417151170231978677809679

theorem tailTrace_7311591 : CollatzResearch.WordTrace tailWord_7311591 prefixEnd_7311591 417151170231978677809679 := by
  unfold tailWord_7311591
  simp only [CollatzResearch.WordTrace]
  refine ⟨266675632054362002172206627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177783754702908001448137751 266675632054362002172206627)
  ·
    refine ⟨400013448081543003258309941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266675632054362002172206627 400013448081543003258309941)
    ·
      refine ⟨37501260757644656555466557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 400013448081543003258309941 37501260757644656555466557)
      ·
        refine ⟨14062972784116746208299959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37501260757644656555466557 14062972784116746208299959)
        ·
          refine ⟨21094459176175119312449939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14062972784116746208299959 21094459176175119312449939)
          ·
            refine ⟨31641688764262678968674909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21094459176175119312449939 31641688764262678968674909)
            ·
              refine ⟨11865633286598504613253091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31641688764262678968674909 11865633286598504613253091)
              ·
                refine ⟨17798449929897756919879637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11865633286598504613253091 17798449929897756919879637)
                ·
                  refine ⟨417151170231978677809679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17798449929897756919879637 417151170231978677809679)
                  ·
                    rfl

theorem cell23_7311591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 7].length) (baseStart_7311591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311591 prefixEnd_7311591 := by exact prefixLift 7311591
  have htrace : WordTrace (prefixWord ++ tailWord_7311591) baseStart_7311591 baseEnd_7311591 := by
    simpa [prefixWord, tailWord_7311591, baseEnd_7311591] using wordTrace_append hprefix tailTrace_7311591
  have hstable : (prefixWord ++ tailWord_7311591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311591).length < 2 ^ (prefixWord ++ tailWord_7311591).sum := by decide
  have hdescent : baseEnd_7311591 < baseStart_7311591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311602 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7311602 : Nat := 118140960795 + 7311602 * 2 ^ 59
def prefixEnd_7311602 : Nat := 4983230072969 + 3 ^ 40 * 7311602 * 2
def baseEnd_7311602 : Nat := 3754366180375007557249561

theorem tailTrace_7311602 : CollatzResearch.WordTrace tailWord_7311602 prefixEnd_7311602 3754366180375007557249561 := by
  unfold tailWord_7311602
  simp only [CollatzResearch.WordTrace]
  refine ⟨66669008314330537762714265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177784022171548100700571373 66669008314330537762714265)
  ·
    refine ⟨50001756235747903322035699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66669008314330537762714265 50001756235747903322035699)
    ·
      refine ⟨75002634353621854983053549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50001756235747903322035699 75002634353621854983053549)
      ·
        refine ⟨28125987882608195618645081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75002634353621854983053549 28125987882608195618645081)
        ·
          refine ⟨21094490911956146713983811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28125987882608195618645081 21094490911956146713983811)
          ·
            refine ⟨31641736367934220070975717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21094490911956146713983811 31641736367934220070975717)
            ·
              refine ⟨5932825568987666263307947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31641736367934220070975717 5932825568987666263307947)
              ·
                refine ⟨8899238353481499394961921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932825568987666263307947 8899238353481499394961921)
                ·
                  refine ⟨6674428765111124546221441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8899238353481499394961921 6674428765111124546221441)
                  ·
                    refine ⟨5005821573833343409666081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6674428765111124546221441 5005821573833343409666081)
                    ·
                      refine ⟨3754366180375007557249561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005821573833343409666081 3754366180375007557249561)
                      ·
                        rfl

theorem cell23_7311602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7311602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311602 prefixEnd_7311602 := by exact prefixLift 7311602
  have htrace : WordTrace (prefixWord ++ tailWord_7311602) baseStart_7311602 baseEnd_7311602 := by
    simpa [prefixWord, tailWord_7311602, baseEnd_7311602] using wordTrace_append hprefix tailTrace_7311602
  have hstable : (prefixWord ++ tailWord_7311602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311602).length < 2 ^ (prefixWord ++ tailWord_7311602).sum := by decide
  have hdescent : baseEnd_7311602 < baseStart_7311602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311642 : List Nat := [3, 1, 1, 3, 5, 1, 2, 2, 5]
def baseStart_7311642 : Nat := 118140960795 + 7311642 * 2 ^ 59
def prefixEnd_7311642 : Nat := 4983230072969 + 3 ^ 40 * 7311642 * 2
def baseEnd_7311642 : Nat := 417154079955687488972153

theorem tailTrace_7311642 : CollatzResearch.WordTrace tailWord_7311642 prefixEnd_7311642 417154079955687488972153 := by
  unfold tailWord_7311642
  simp only [CollatzResearch.WordTrace]
  refine ⟨66669373044294309470578295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177784994784784825254875453 66669373044294309470578295)
  ·
    refine ⟨100004059566441464205867443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66669373044294309470578295 100004059566441464205867443)
    ·
      refine ⟨150006089349662196308801165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100004059566441464205867443 150006089349662196308801165)
      ·
        refine ⟨56252283506123323615800437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150006089349662196308801165 56252283506123323615800437)
        ·
          refine ⟨5273651578699061588981291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56252283506123323615800437 5273651578699061588981291)
          ·
            refine ⟨7910477368048592383471937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5273651578699061588981291 7910477368048592383471937)
            ·
              refine ⟨5932858026036444287603953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910477368048592383471937 5932858026036444287603953)
              ·
                refine ⟨4449643519527333215702965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932858026036444287603953 4449643519527333215702965)
                ·
                  refine ⟨417154079955687488972153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449643519527333215702965 417154079955687488972153)
                  ·
                    rfl

theorem cell23_7311642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_7311642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311642 prefixEnd_7311642 := by exact prefixLift 7311642
  have htrace : WordTrace (prefixWord ++ tailWord_7311642) baseStart_7311642 baseEnd_7311642 := by
    simpa [prefixWord, tailWord_7311642, baseEnd_7311642] using wordTrace_append hprefix tailTrace_7311642
  have hstable : (prefixWord ++ tailWord_7311642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311642).length < 2 ^ (prefixWord ++ tailWord_7311642).sum := by decide
  have hdescent : baseEnd_7311642 < baseStart_7311642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311644 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7311644 : Nat := 118140960795 + 7311644 * 2 ^ 59
def prefixEnd_7311644 : Nat := 4983230072969 + 3 ^ 40 * 7311644 * 2
def baseEnd_7311644 : Nat := 3754387746562496392924367

theorem tailTrace_7311644 : CollatzResearch.WordTrace tailWord_7311644 prefixEnd_7311644 3754387746562496392924367 := by
  unfold tailWord_7311644
  simp only [CollatzResearch.WordTrace]
  refine ⟨133338782561584996111942993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177785043415446661482590657 133338782561584996111942993)
  ·
    refine ⟨100004086921188747083957245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133338782561584996111942993 100004086921188747083957245)
    ·
      refine ⟨37501532595445780156483967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100004086921188747083957245 37501532595445780156483967)
      ·
        refine ⟨56252298893168670234725951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37501532595445780156483967 56252298893168670234725951)
        ·
          refine ⟨84378448339753005352088927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56252298893168670234725951 84378448339753005352088927)
          ·
            refine ⟨126567672509629508028133391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84378448339753005352088927 126567672509629508028133391)
            ·
              refine ⟨189851508764444262042200087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126567672509629508028133391 189851508764444262042200087)
              ·
                refine ⟨284777263146666393063300131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189851508764444262042200087 284777263146666393063300131)
                ·
                  refine ⟨427165894719999589594950197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284777263146666393063300131 427165894719999589594950197)
                  ·
                    refine ⟨40046802629999961524526581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 427165894719999589594950197 40046802629999961524526581)
                    ·
                      refine ⟨3754387746562496392924367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40046802629999961524526581 3754387746562496392924367)
                      ·
                        rfl

theorem cell23_7311644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7311644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311644 prefixEnd_7311644 := by exact prefixLift 7311644
  have htrace : WordTrace (prefixWord ++ tailWord_7311644) baseStart_7311644 baseEnd_7311644 := by
    simpa [prefixWord, tailWord_7311644, baseEnd_7311644] using wordTrace_append hprefix tailTrace_7311644
  have hstable : (prefixWord ++ tailWord_7311644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311644).length < 2 ^ (prefixWord ++ tailWord_7311644).sum := by decide
  have hdescent : baseEnd_7311644 < baseStart_7311644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311651 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 3, 4]
def baseStart_7311651 : Nat := 118140960795 + 7311651 * 2 ^ 59
def prefixEnd_7311651 : Nat := 4983230072969 + 3 ^ 40 * 7311651 * 2
def baseEnd_7311651 : Nat := 1251463780309025955178945

theorem tailTrace_7311651 : CollatzResearch.WordTrace tailWord_7311651 prefixEnd_7311651 1251463780309025955178945 := by
  unfold tailWord_7311651
  simp only [CollatzResearch.WordTrace]
  refine ⟨266677820434144632419390807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177785213622763088279593871 266677820434144632419390807)
  ·
    refine ⟨400016730651216948629086211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266677820434144632419390807 400016730651216948629086211)
    ·
      refine ⟨600025095976825422943629317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400016730651216948629086211 600025095976825422943629317)
      ·
        refine ⟨112504705495654766801930497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 600025095976825422943629317 112504705495654766801930497)
        ·
          refine ⟨84378529121741075101447873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112504705495654766801930497 84378529121741075101447873)
          ·
            refine ⟨63283896841305806326085905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84378529121741075101447873 63283896841305806326085905)
            ·
              refine ⟨47462922630979354744564429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63283896841305806326085905 47462922630979354744564429)
              ·
                refine ⟨17798595986617258029211661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47462922630979354744564429 17798595986617258029211661)
                ·
                  refine ⟨6674473494981471760954373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17798595986617258029211661 6674473494981471760954373)
                  ·
                    refine ⟨1251463780309025955178945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674473494981471760954373 1251463780309025955178945)
                    ·
                      rfl

theorem cell23_7311651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 4].length) (baseStart_7311651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311651 prefixEnd_7311651 := by exact prefixLift 7311651
  have htrace : WordTrace (prefixWord ++ tailWord_7311651) baseStart_7311651 baseEnd_7311651 := by
    simpa [prefixWord, tailWord_7311651, baseEnd_7311651] using wordTrace_append hprefix tailTrace_7311651
  have hstable : (prefixWord ++ tailWord_7311651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311651).length < 2 ^ (prefixWord ++ tailWord_7311651).sum := by decide
  have hdescent : baseEnd_7311651 < baseStart_7311651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311668 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_7311668 : Nat := 118140960795 + 7311668 * 2 ^ 59
def prefixEnd_7311668 : Nat := 4983230072969 + 3 ^ 40 * 7311668 * 2
def baseEnd_7311668 : Nat := 1251466690032734766341419

theorem tailTrace_7311668 : CollatzResearch.WordTrace tailWord_7311668 prefixEnd_7311668 1251466690032734766341419 := by
  unfold tailWord_7311668
  simp only [CollatzResearch.WordTrace]
  refine ⟨133339220237541522161379829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177785626983388696215173105 133339220237541522161379829)
  ·
    refine ⟨12500551897269517702629359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133339220237541522161379829 12500551897269517702629359)
    ·
      refine ⟨18750827845904276553944039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12500551897269517702629359 18750827845904276553944039)
      ·
        refine ⟨28126241768856414830916059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18750827845904276553944039 28126241768856414830916059)
        ·
          refine ⟨42189362653284622246374089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28126241768856414830916059 42189362653284622246374089)
          ·
            refine ⟨31642021989963466684780567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42189362653284622246374089 31642021989963466684780567)
            ·
              refine ⟨47463032984945200027170851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31642021989963466684780567 47463032984945200027170851)
              ·
                refine ⟨71194549477417800040756277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47463032984945200027170851 71194549477417800040756277)
                ·
                  refine ⟨6674489013507918753820901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71194549477417800040756277 6674489013507918753820901)
                  ·
                    refine ⟨1251466690032734766341419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674489013507918753820901 1251466690032734766341419)
                    ·
                      rfl

theorem cell23_7311668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_7311668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311668 prefixEnd_7311668 := by exact prefixLift 7311668
  have htrace : WordTrace (prefixWord ++ tailWord_7311668) baseStart_7311668 baseEnd_7311668 := by
    simpa [prefixWord, tailWord_7311668, baseEnd_7311668] using wordTrace_append hprefix tailTrace_7311668
  have hstable : (prefixWord ++ tailWord_7311668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311668).length < 2 ^ (prefixWord ++ tailWord_7311668).sum := by decide
  have hdescent : baseEnd_7311668 < baseStart_7311668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311678 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_7311678 : Nat := 118140960795 + 7311678 * 2 ^ 59
def prefixEnd_7311678 : Nat := 4983230072969 + 3 ^ 40 * 7311678 * 2
def baseEnd_7311678 : Nat := 3754405204904749259899211

theorem tailTrace_7311678 : CollatzResearch.WordTrace tailWord_7311678 prefixEnd_7311678 3754405204904749259899211 := by
  unfold tailWord_7311678
  simp only [CollatzResearch.WordTrace]
  refine ⟨33334850650630852003827961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177785870136697877353749125 33334850650630852003827961)
  ·
    refine ⟨25001137987973139002870971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33334850650630852003827961 25001137987973139002870971)
    ·
      refine ⟨37501706981959708504306457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25001137987973139002870971 37501706981959708504306457)
      ·
        refine ⟨28126280236469781378229843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37501706981959708504306457 28126280236469781378229843)
        ·
          refine ⟨42189420354704672067344765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28126280236469781378229843 42189420354704672067344765)
          ·
            refine ⟨15821032633014252025254287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42189420354704672067344765 15821032633014252025254287)
            ·
              refine ⟨23731548949521378037881431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15821032633014252025254287 23731548949521378037881431)
              ·
                refine ⟨35597323424282067056822147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23731548949521378037881431 35597323424282067056822147)
                ·
                  refine ⟨53395985136423100585233221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35597323424282067056822147 53395985136423100585233221)
                  ·
                    refine ⟨10011747213079331359731229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53395985136423100585233221 10011747213079331359731229)
                    ·
                      refine ⟨3754405204904749259899211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10011747213079331359731229 3754405204904749259899211)
                      ·
                        rfl

theorem cell23_7311678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_7311678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311678 prefixEnd_7311678 := by exact prefixLift 7311678
  have htrace : WordTrace (prefixWord ++ tailWord_7311678) baseStart_7311678 baseEnd_7311678 := by
    simpa [prefixWord, tailWord_7311678, baseEnd_7311678] using wordTrace_append hprefix tailTrace_7311678
  have hstable : (prefixWord ++ tailWord_7311678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311678).length < 2 ^ (prefixWord ++ tailWord_7311678).sum := by decide
  have hdescent : baseEnd_7311678 < baseStart_7311678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311704 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_7311704 : Nat := 118140960795 + 7311704 * 2 ^ 59
def prefixEnd_7311704 : Nat := 4983230072969 + 3 ^ 40 * 7311704 * 2
def baseEnd_7311704 : Nat := 3754418555401766158174091

theorem tailTrace_7311704 : CollatzResearch.WordTrace tailWord_7311704 prefixEnd_7311704 3754418555401766158174091 := by
  unfold tailWord_7311704
  simp only [CollatzResearch.WordTrace]
  refine ⟨133339876751476311235535083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177786502335301748314046777 133339876751476311235535083)
  ·
    refine ⟨200009815127214466853302625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133339876751476311235535083 200009815127214466853302625)
    ·
      refine ⟨150007361345410850139976969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200009815127214466853302625 150007361345410850139976969)
      ·
        refine ⟨112505521009058137604982727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150007361345410850139976969 112505521009058137604982727)
        ·
          refine ⟨168758281513587206407474091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112505521009058137604982727 168758281513587206407474091)
          ·
            refine ⟨253137422270380809611211137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168758281513587206407474091 253137422270380809611211137)
            ·
              refine ⟨189853066702785607208408353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253137422270380809611211137 189853066702785607208408353)
              ·
                refine ⟨142389800027089205406306265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189853066702785607208408353 142389800027089205406306265)
                ·
                  refine ⟨106792350020316904054729699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142389800027089205406306265 106792350020316904054729699)
                  ·
                    refine ⟨160188525030475356082094549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106792350020316904054729699 160188525030475356082094549)
                    ·
                      refine ⟨3754418555401766158174091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160188525030475356082094549 3754418555401766158174091)
                      ·
                        rfl

theorem cell23_7311704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_7311704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311704 prefixEnd_7311704 := by exact prefixLift 7311704
  have htrace : WordTrace (prefixWord ++ tailWord_7311704) baseStart_7311704 baseEnd_7311704 := by
    simpa [prefixWord, tailWord_7311704, baseEnd_7311704] using wordTrace_append hprefix tailTrace_7311704
  have hstable : (prefixWord ++ tailWord_7311704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311704).length < 2 ^ (prefixWord ++ tailWord_7311704).sum := by decide
  have hdescent : baseEnd_7311704 < baseStart_7311704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311728 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 1, 5]
def baseStart_7311728 : Nat := 118140960795 + 7311728 * 2 ^ 59
def prefixEnd_7311728 : Nat := 4983230072969 + 3 ^ 40 * 7311728 * 2
def baseEnd_7311728 : Nat := 1251476959645824688091327

theorem tailTrace_7311728 : CollatzResearch.WordTrace tailWord_7311728 prefixEnd_7311728 1251476959645824688091327 := by
  unfold tailWord_7311728
  simp only [CollatzResearch.WordTrace]
  refine ⟨133340314427432837284971919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177787085903243783046629225 133340314427432837284971919)
  ·
    refine ⟨200010471641149255927457879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133340314427432837284971919 200010471641149255927457879)
    ·
      refine ⟨300015707461723883891186819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200010471641149255927457879 300015707461723883891186819)
      ·
        refine ⟨450023561192585825836780229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300015707461723883891186819 450023561192585825836780229)
        ·
          refine ⟨84379417723609842344396293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450023561192585825836780229 84379417723609842344396293)
          ·
            refine ⟨15821140823176845439574305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84379417723609842344396293 15821140823176845439574305)
            ·
              refine ⟨11865855617382634079680729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15821140823176845439574305 11865855617382634079680729)
              ·
                refine ⟨8899391713036975559760547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11865855617382634079680729 8899391713036975559760547)
                ·
                  refine ⟨13349087569555463339640821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8899391713036975559760547 13349087569555463339640821)
                  ·
                    refine ⟨1251476959645824688091327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13349087569555463339640821 1251476959645824688091327)
                    ·
                      rfl

theorem cell23_7311728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_7311728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311728 prefixEnd_7311728 := by exact prefixLift 7311728
  have htrace : WordTrace (prefixWord ++ tailWord_7311728) baseStart_7311728 baseEnd_7311728 := by
    simpa [prefixWord, tailWord_7311728, baseEnd_7311728] using wordTrace_append hprefix tailTrace_7311728
  have hstable : (prefixWord ++ tailWord_7311728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311728).length < 2 ^ (prefixWord ++ tailWord_7311728).sum := by decide
  have hdescent : baseEnd_7311728 < baseStart_7311728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311748 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_7311748 : Nat := 118140960795 + 7311748 * 2 ^ 59
def prefixEnd_7311748 : Nat := 4983230072969 + 3 ^ 40 * 7311748 * 2
def baseEnd_7311748 : Nat := 3754441148550563986023889

theorem tailTrace_7311748 : CollatzResearch.WordTrace tailWord_7311748 prefixEnd_7311748 3754441148550563986023889 := by
  unfold tailWord_7311748
  simp only [CollatzResearch.WordTrace]
  refine ⟨133340679157396608992835949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177787572209862145323781265 133340679157396608992835949)
  ·
    refine ⟨50002754684023728372313481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133340679157396608992835949 50002754684023728372313481)
    ·
      refine ⟨37502066013017796279235111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50002754684023728372313481 37502066013017796279235111)
      ·
        refine ⟨56253099019526694418852667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37502066013017796279235111 56253099019526694418852667)
        ·
          refine ⟨84379648529290041628279001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56253099019526694418852667 84379648529290041628279001)
          ·
            refine ⟨63284736396967531221209251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84379648529290041628279001 63284736396967531221209251)
            ·
              refine ⟨94927104595451296831813877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63284736396967531221209251 94927104595451296831813877)
              ·
                refine ⟨8899416055823559077982551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94927104595451296831813877 8899416055823559077982551)
                ·
                  refine ⟨13349124083735338616973827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8899416055823559077982551 13349124083735338616973827)
                  ·
                    refine ⟨20023686125603007925460741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13349124083735338616973827 20023686125603007925460741)
                    ·
                      refine ⟨3754441148550563986023889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20023686125603007925460741 3754441148550563986023889)
                      ·
                        rfl

theorem cell23_7311748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_7311748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311748 prefixEnd_7311748 := by exact prefixLift 7311748
  have htrace : WordTrace (prefixWord ++ tailWord_7311748) baseStart_7311748 baseEnd_7311748 := by
    simpa [prefixWord, tailWord_7311748, baseEnd_7311748] using wordTrace_append hprefix tailTrace_7311748
  have hstable : (prefixWord ++ tailWord_7311748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311748).length < 2 ^ (prefixWord ++ tailWord_7311748).sum := by decide
  have hdescent : baseEnd_7311748 < baseStart_7311748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311766 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7311766 : Nat := 118140960795 + 7311766 * 2 ^ 59
def prefixEnd_7311766 : Nat := 4983230072969 + 3 ^ 40 * 7311766 * 2
def baseEnd_7311766 : Nat := 417161154578038323955423

theorem tailTrace_7311766 : CollatzResearch.WordTrace tailWord_7311766 prefixEnd_7311766 417161154578038323955423 := by
  unfold tailWord_7311766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16667625926795500441239197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177788009885818671373218101 16667625926795500441239197)
  ·
    refine ⟨6250359722548312665464699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16667625926795500441239197 6250359722548312665464699)
    ·
      refine ⟨9375539583822468998197049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6250359722548312665464699 9375539583822468998197049)
      ·
        refine ⟨7031654687866851748647787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9375539583822468998197049 7031654687866851748647787)
        ·
          refine ⟨10547482031800277622971681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031654687866851748647787 10547482031800277622971681)
          ·
            refine ⟨7910611523850208217228761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10547482031800277622971681 7910611523850208217228761)
            ·
              refine ⟨5932958642887656162921571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910611523850208217228761 5932958642887656162921571)
              ·
                refine ⟨8899437964331484244382357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932958642887656162921571 8899437964331484244382357)
                ·
                  refine ⟨417161154578038323955423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8899437964331484244382357 417161154578038323955423)
                  ·
                    rfl

theorem cell23_7311766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7311766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311766 prefixEnd_7311766 := by exact prefixLift 7311766
  have htrace : WordTrace (prefixWord ++ tailWord_7311766) baseStart_7311766 baseEnd_7311766 := by
    simpa [prefixWord, tailWord_7311766, baseEnd_7311766] using wordTrace_append hprefix tailTrace_7311766
  have hstable : (prefixWord ++ tailWord_7311766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311766).length < 2 ^ (prefixWord ++ tailWord_7311766).sum := by decide
  have hdescent : baseEnd_7311766 < baseStart_7311766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311768 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7311768 : Nat := 118140960795 + 7311768 * 2 ^ 59
def prefixEnd_7311768 : Nat := 4983230072969 + 3 ^ 40 * 7311768 * 2
def baseEnd_7311768 : Nat := 3754451418163653907773797

theorem tailTrace_7311768 : CollatzResearch.WordTrace tailWord_7311768 prefixEnd_7311768 3754451418163653907773797 := by
  unfold tailWord_7311768
  simp only [CollatzResearch.WordTrace]
  refine ⟨133341043887360380700699979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177788058516480507600933305 133341043887360380700699979)
  ·
    refine ⟨200011565831040571051049969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133341043887360380700699979 200011565831040571051049969)
    ·
      refine ⟨150008674373280428288287477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200011565831040571051049969 150008674373280428288287477)
      ·
        refine ⟨14063313222495040152026951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150008674373280428288287477 14063313222495040152026951)
        ·
          refine ⟨21094969833742560228040427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063313222495040152026951 21094969833742560228040427)
          ·
            refine ⟨31642454750613840342060641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21094969833742560228040427 31642454750613840342060641)
            ·
              refine ⟨23731841062960380256545481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31642454750613840342060641 23731841062960380256545481)
              ·
                refine ⟨17798880797220285192409111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23731841062960380256545481 17798880797220285192409111)
                ·
                  refine ⟨26698321195830427788613667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17798880797220285192409111 26698321195830427788613667)
                  ·
                    refine ⟨40047481793745641682920501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26698321195830427788613667 40047481793745641682920501)
                    ·
                      refine ⟨3754451418163653907773797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40047481793745641682920501 3754451418163653907773797)
                      ·
                        rfl

theorem cell23_7311768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7311768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311768 prefixEnd_7311768 := by exact prefixLift 7311768
  have htrace : WordTrace (prefixWord ++ tailWord_7311768) baseStart_7311768 baseEnd_7311768 := by
    simpa [prefixWord, tailWord_7311768, baseEnd_7311768] using wordTrace_append hprefix tailTrace_7311768
  have hstable : (prefixWord ++ tailWord_7311768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311768).length < 2 ^ (prefixWord ++ tailWord_7311768).sum := by decide
  have hdescent : baseEnd_7311768 < baseStart_7311768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311778 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_7311778 : Nat := 118140960795 + 7311778 * 2 ^ 59
def prefixEnd_7311778 : Nat := 4983230072969 + 3 ^ 40 * 7311778 * 2
def baseEnd_7311778 : Nat := 3754456552970198868648751

theorem tailTrace_7311778 : CollatzResearch.WordTrace tailWord_7311778 prefixEnd_7311778 3754456552970198868648751 := by
  unfold tailWord_7311778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66670613126171133277315997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177788301669789688739509325 66670613126171133277315997)
  ·
    refine ⟨25001479922314174978993499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66670613126171133277315997 25001479922314174978993499)
    ·
      refine ⟨37502219883471262468490249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25001479922314174978993499 37502219883471262468490249)
      ·
        refine ⟨28126664912603446851367687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37502219883471262468490249 28126664912603446851367687)
        ·
          refine ⟨42189997368905170277051531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28126664912603446851367687 42189997368905170277051531)
          ·
            refine ⟨63284996053357755415577297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42189997368905170277051531 63284996053357755415577297)
            ·
              refine ⟨47463747040018316561682973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63284996053357755415577297 47463747040018316561682973)
              ·
                refine ⟨17798905140006868710631115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47463747040018316561682973 17798905140006868710631115)
                ·
                  refine ⟨26698357710010303065946673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17798905140006868710631115 26698357710010303065946673)
                  ·
                    refine ⟨20023768282507727299460005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26698357710010303065946673 20023768282507727299460005)
                    ·
                      refine ⟨3754456552970198868648751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20023768282507727299460005 3754456552970198868648751)
                      ·
                        rfl

theorem cell23_7311778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_7311778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311778 prefixEnd_7311778 := by exact prefixLift 7311778
  have htrace : WordTrace (prefixWord ++ tailWord_7311778) baseStart_7311778 baseEnd_7311778 := by
    simpa [prefixWord, tailWord_7311778, baseEnd_7311778] using wordTrace_append hprefix tailTrace_7311778
  have hstable : (prefixWord ++ tailWord_7311778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311778).length < 2 ^ (prefixWord ++ tailWord_7311778).sum := by decide
  have hdescent : baseEnd_7311778 < baseStart_7311778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311786 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7311786 : Nat := 118140960795 + 7311786 * 2 ^ 59
def prefixEnd_7311786 : Nat := 4983230072969 + 3 ^ 40 * 7311786 * 2
def baseEnd_7311786 : Nat := 3754460660815434837348715

theorem tailTrace_7311786 : CollatzResearch.WordTrace tailWord_7311786 prefixEnd_7311786 3754460660815434837348715 := by
  unfold tailWord_7311786
  simp only [CollatzResearch.WordTrace]
  refine ⟨66670686072163887618888803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177788496192437033650370141 66670686072163887618888803)
  ·
    refine ⟨100006029108245831428333205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66670686072163887618888803 100006029108245831428333205)
    ·
      refine ⟨4687782614449023348203119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100006029108245831428333205 4687782614449023348203119)
      ·
        refine ⟨7031673921673535022304679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4687782614449023348203119 7031673921673535022304679)
        ·
          refine ⟨10547510882510302533457019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031673921673535022304679 10547510882510302533457019)
          ·
            refine ⟨15821266323765453800185529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547510882510302533457019 15821266323765453800185529)
            ·
              refine ⟨11865949742824090350139147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15821266323765453800185529 11865949742824090350139147)
              ·
                refine ⟨17798924614236135525208721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11865949742824090350139147 17798924614236135525208721)
                ·
                  refine ⟨13349193460677101643906541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17798924614236135525208721 13349193460677101643906541)
                  ·
                    refine ⟨5005947547753913116464953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13349193460677101643906541 5005947547753913116464953)
                    ·
                      refine ⟨3754460660815434837348715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005947547753913116464953 3754460660815434837348715)
                      ·
                        rfl

theorem cell23_7311786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7311786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311786 prefixEnd_7311786 := by exact prefixLift 7311786
  have htrace : WordTrace (prefixWord ++ tailWord_7311786) baseStart_7311786 baseEnd_7311786 := by
    simpa [prefixWord, tailWord_7311786, baseEnd_7311786] using wordTrace_append hprefix tailTrace_7311786
  have hstable : (prefixWord ++ tailWord_7311786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311786).length < 2 ^ (prefixWord ++ tailWord_7311786).sum := by decide
  have hdescent : baseEnd_7311786 < baseStart_7311786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311815 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_7311815 : Nat := 118140960795 + 7311815 * 2 ^ 59
def prefixEnd_7311815 : Nat := 4983230072969 + 3 ^ 40 * 7311815 * 2
def baseEnd_7311815 : Nat := 3754475551754415223886081

theorem tailTrace_7311815 : CollatzResearch.WordTrace tailWord_7311815 prefixEnd_7311815 3754475551754415223886081 := by
  unfold tailWord_7311815
  simp only [CollatzResearch.WordTrace]
  refine ⟨266683802005550488428360899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177789201337033658952240599 266683802005550488428360899)
  ·
    refine ⟨400025703008325732642541349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266683802005550488428360899 400025703008325732642541349)
    ·
      refine ⟨75004819314061074870476503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400025703008325732642541349 75004819314061074870476503)
      ·
        refine ⟨112507228971091612305714755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75004819314061074870476503 112507228971091612305714755)
        ·
          refine ⟨168760843456637418458572133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112507228971091612305714755 168760843456637418458572133)
          ·
            refine ⟨31642658148119515960982275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168760843456637418458572133 31642658148119515960982275)
            ·
              refine ⟨47463987222179273941473413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31642658148119515960982275 47463987222179273941473413)
              ·
                refine ⟨8899497604158613864026265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47463987222179273941473413 8899497604158613864026265)
                ·
                  refine ⟨6674623203118960398019699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8899497604158613864026265 6674623203118960398019699)
                  ·
                    refine ⟨10011934804678440597029549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6674623203118960398019699 10011934804678440597029549)
                    ·
                      refine ⟨3754475551754415223886081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10011934804678440597029549 3754475551754415223886081)
                      ·
                        rfl

theorem cell23_7311815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_7311815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311815 prefixEnd_7311815 := by exact prefixLift 7311815
  have htrace : WordTrace (prefixWord ++ tailWord_7311815) baseStart_7311815 baseEnd_7311815 := by
    simpa [prefixWord, tailWord_7311815, baseEnd_7311815] using wordTrace_append hprefix tailTrace_7311815
  have hstable : (prefixWord ++ tailWord_7311815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311815).length < 2 ^ (prefixWord ++ tailWord_7311815).sum := by decide
  have hdescent : baseEnd_7311815 < baseStart_7311815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311816 : List Nat := [2, 1, 3, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_7311816 : Nat := 118140960795 + 7311816 * 2 ^ 59
def prefixEnd_7311816 : Nat := 4983230072969 + 3 ^ 40 * 7311816 * 2
def baseEnd_7311816 : Nat := 3754476065235069719973577

theorem tailTrace_7311816 : CollatzResearch.WordTrace tailWord_7311816 prefixEnd_7311816 3754476065235069719973577 := by
  unfold tailWord_7311816
  simp only [CollatzResearch.WordTrace]
  refine ⟨133341919239273432799573651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177789225652364577066098201 133341919239273432799573651)
  ·
    refine ⟨200012878858910149199360477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133341919239273432799573651 200012878858910149199360477)
    ·
      refine ⟨75004829572091305949760179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200012878858910149199360477 75004829572091305949760179)
      ·
        refine ⟨112507244358136958924640269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75004829572091305949760179 112507244358136958924640269)
        ·
          refine ⟨42190216634301359596740101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112507244358136958924640269 42190216634301359596740101)
          ·
            refine ⟨7910665618931504924388769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42190216634301359596740101 7910665618931504924388769)
            ·
              refine ⟨5932999214198628693291577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910665618931504924388769 5932999214198628693291577)
              ·
                refine ⟨4449749410648971519968683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932999214198628693291577 4449749410648971519968683)
                ·
                  refine ⟨6674624115973457279953025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449749410648971519968683 6674624115973457279953025)
                  ·
                    refine ⟨5005968086980092959964769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6674624115973457279953025 5005968086980092959964769)
                    ·
                      refine ⟨3754476065235069719973577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005968086980092959964769 3754476065235069719973577)
                      ·
                        rfl

theorem cell23_7311816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_7311816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311816 prefixEnd_7311816 := by exact prefixLift 7311816
  have htrace : WordTrace (prefixWord ++ tailWord_7311816) baseStart_7311816 baseEnd_7311816 := by
    simpa [prefixWord, tailWord_7311816, baseEnd_7311816] using wordTrace_append hprefix tailTrace_7311816
  have hstable : (prefixWord ++ tailWord_7311816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311816).length < 2 ^ (prefixWord ++ tailWord_7311816).sum := by decide
  have hdescent : baseEnd_7311816 < baseStart_7311816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311851 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4]
def baseStart_7311851 : Nat := 118140960795 + 7311851 * 2 ^ 59
def prefixEnd_7311851 : Nat := 4983230072969 + 3 ^ 40 * 7311851 * 2
def baseEnd_7311851 : Nat := 3754494037057977083035915

theorem tailTrace_7311851 : CollatzResearch.WordTrace tailWord_7311851 prefixEnd_7311851 3754494037057977083035915 := by
  unfold tailWord_7311851
  simp only [CollatzResearch.WordTrace]
  refine ⟨266685115033420066576671407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177790076688946711051114271 266685115033420066576671407)
  ·
    refine ⟨400027672550130099865007111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266685115033420066576671407 400027672550130099865007111)
    ·
      refine ⟨600041508825195149797510667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400027672550130099865007111 600041508825195149797510667)
      ·
        refine ⟨900062263237792724696266001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600041508825195149797510667 900062263237792724696266001)
        ·
          refine ⟨675046697428344543522199501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900062263237792724696266001 675046697428344543522199501)
          ·
            refine ⟨253142511535629203820824813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675046697428344543522199501 253142511535629203820824813)
            ·
              refine ⟨94928441825860951432809305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253142511535629203820824813 94928441825860951432809305)
              ·
                refine ⟨71196331369395713574606979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94928441825860951432809305 71196331369395713574606979)
                ·
                  refine ⟨106794497054093570361910469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71196331369395713574606979 106794497054093570361910469)
                  ·
                    refine ⟨20023968197642544442858213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106794497054093570361910469 20023968197642544442858213)
                    ·
                      refine ⟨3754494037057977083035915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20023968197642544442858213 3754494037057977083035915)
                      ·
                        rfl

theorem cell23_7311851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_7311851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311851 prefixEnd_7311851 := by exact prefixLift 7311851
  have htrace : WordTrace (prefixWord ++ tailWord_7311851) baseStart_7311851 baseEnd_7311851 := by
    simpa [prefixWord, tailWord_7311851, baseEnd_7311851] using wordTrace_append hprefix tailTrace_7311851
  have hstable : (prefixWord ++ tailWord_7311851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311851).length < 2 ^ (prefixWord ++ tailWord_7311851).sum := by decide
  have hdescent : baseEnd_7311851 < baseStart_7311851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311855 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 4, 2, 2]
def baseStart_7311855 : Nat := 118140960795 + 7311855 * 2 ^ 59
def prefixEnd_7311855 : Nat := 4983230072969 + 3 ^ 40 * 7311855 * 2
def baseEnd_7311855 : Nat := 3754496090980595067385897

theorem tailTrace_7311855 : CollatzResearch.WordTrace tailWord_7311855 prefixEnd_7311855 3754496090980595067385897 := by
  unfold tailWord_7311855
  simp only [CollatzResearch.WordTrace]
  refine ⟨266685260925405575259817019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177790173950270383506544679 266685260925405575259817019)
  ·
    refine ⟨400027891388108362889725529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266685260925405575259817019 400027891388108362889725529)
    ·
      refine ⟨300020918541081272167294147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400027891388108362889725529 300020918541081272167294147)
      ·
        refine ⟨450031377811621908250941221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300020918541081272167294147 450031377811621908250941221)
        ·
          refine ⟨84380883339679107797051479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450031377811621908250941221 84380883339679107797051479)
          ·
            refine ⟨126571325009518661695577219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84380883339679107797051479 126571325009518661695577219)
            ·
              refine ⟨189856987514277992543365829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126571325009518661695577219 189856987514277992543365829)
              ·
                refine ⟨35598185158927123601881093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189856987514277992543365829 35598185158927123601881093)
                ·
                  refine ⟨6674659717298835675352705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35598185158927123601881093 6674659717298835675352705)
                  ·
                    refine ⟨5005994787974126756514529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6674659717298835675352705 5005994787974126756514529)
                    ·
                      refine ⟨3754496090980595067385897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5005994787974126756514529 3754496090980595067385897)
                      ·
                        rfl

theorem cell23_7311855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 2, 2].length) (baseStart_7311855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311855 prefixEnd_7311855 := by exact prefixLift 7311855
  have htrace : WordTrace (prefixWord ++ tailWord_7311855) baseStart_7311855 baseEnd_7311855 := by
    simpa [prefixWord, tailWord_7311855, baseEnd_7311855] using wordTrace_append hprefix tailTrace_7311855
  have hstable : (prefixWord ++ tailWord_7311855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311855).length < 2 ^ (prefixWord ++ tailWord_7311855).sum := by decide
  have hdescent : baseEnd_7311855 < baseStart_7311855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311891 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 3, 7]
def baseStart_7311891 : Nat := 118140960795 + 7311891 * 2 ^ 59
def prefixEnd_7311891 : Nat := 4983230072969 + 3 ^ 40 * 7311891 * 2
def baseEnd_7311891 : Nat := 1251504858761385642178577

theorem tailTrace_7311891 : CollatzResearch.WordTrace tailWord_7311891 prefixEnd_7311891 1251504858761385642178577 := by
  unfold tailWord_7311891
  simp only [CollatzResearch.WordTrace]
  refine ⟨266686573953275153408127527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177791049302183435605418351 266686573953275153408127527)
  ·
    refine ⟨400029860929912730112191291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266686573953275153408127527 400029860929912730112191291)
    ·
      refine ⟨600044791394869095168286937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400029860929912730112191291 600044791394869095168286937)
      ·
        refine ⟨450033593546151821376215203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600044791394869095168286937 450033593546151821376215203)
        ·
          refine ⟨675050390319227732064322805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450033593546151821376215203 675050390319227732064322805)
          ·
            refine ⟨63285974092427599881030263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 675050390319227732064322805 63285974092427599881030263)
            ·
              refine ⟨94928961138641399821545395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63285974092427599881030263 94928961138641399821545395)
              ·
                refine ⟨142393441707962099732318093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94928961138641399821545395 142393441707962099732318093)
                ·
                  refine ⟨53397540640485787399619285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142393441707962099732318093 53397540640485787399619285)
                  ·
                    refine ⟨1251504858761385642178577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53397540640485787399619285 1251504858761385642178577)
                    ·
                      rfl

theorem cell23_7311891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 7].length) (baseStart_7311891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311891 prefixEnd_7311891 := by exact prefixLift 7311891
  have htrace : WordTrace (prefixWord ++ tailWord_7311891) baseStart_7311891 baseEnd_7311891 := by
    simpa [prefixWord, tailWord_7311891, baseEnd_7311891] using wordTrace_append hprefix tailTrace_7311891
  have hstable : (prefixWord ++ tailWord_7311891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311891).length < 2 ^ (prefixWord ++ tailWord_7311891).sum := by decide
  have hdescent : baseEnd_7311891 < baseStart_7311891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311912 : List Nat := [2, 1, 5, 2, 1, 1, 3, 3, 5]
def baseStart_7311912 : Nat := 118140960795 + 7311912 * 2 ^ 59
def prefixEnd_7311912 : Nat := 4983230072969 + 3 ^ 40 * 7311912 * 2
def baseEnd_7311912 : Nat := 417169484375322371597015

theorem tailTrace_7311912 : CollatzResearch.WordTrace tailWord_7311912 prefixEnd_7311912 417169484375322371597015 := by
  unfold tailWord_7311912
  simp only [CollatzResearch.WordTrace]
  refine ⟨133343669943099536997320995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177791559924132715996427993 133343669943099536997320995)
  ·
    refine ⟨200015504914649305495981493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133343669943099536997320995 200015504914649305495981493)
    ·
      refine ⟨18751453585748372390248265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200015504914649305495981493 18751453585748372390248265)
      ·
        refine ⟨14063590189311279292686199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18751453585748372390248265 14063590189311279292686199)
        ·
          refine ⟨21095385283966918939029299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063590189311279292686199 21095385283966918939029299)
          ·
            refine ⟨31643077925950378408543949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21095385283966918939029299 31643077925950378408543949)
            ·
              refine ⟨11866154222231391903203981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31643077925950378408543949 11866154222231391903203981)
              ·
                refine ⟨4449807833336771963701493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11866154222231391903203981 4449807833336771963701493)
                ·
                  refine ⟨417169484375322371597015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449807833336771963701493 417169484375322371597015)
                  ·
                    rfl

theorem cell23_7311912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 5].length) (baseStart_7311912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311912 prefixEnd_7311912 := by exact prefixLift 7311912
  have htrace : WordTrace (prefixWord ++ tailWord_7311912) baseStart_7311912 baseEnd_7311912 := by
    simpa [prefixWord, tailWord_7311912, baseEnd_7311912] using wordTrace_append hprefix tailTrace_7311912
  have hstable : (prefixWord ++ tailWord_7311912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311912).length < 2 ^ (prefixWord ++ tailWord_7311912).sum := by decide
  have hdescent : baseEnd_7311912 < baseStart_7311912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311972 : List Nat := [2, 3, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_7311972 : Nat := 118140960795 + 7311972 * 2 ^ 59
def prefixEnd_7311972 : Nat := 4983230072969 + 3 ^ 40 * 7311972 * 2
def baseEnd_7311972 : Nat := 1251518722739057036540953

theorem tailTrace_7311972 : CollatzResearch.WordTrace tailWord_7311972 prefixEnd_7311972 1251518722739057036540953 := by
  unfold tailWord_7311972
  simp only [CollatzResearch.WordTrace]
  refine ⟨133344764132990852120913085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177793018843987802827884113 133344764132990852120913085)
  ·
    refine ⟨50004286549871569545342407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133344764132990852120913085 50004286549871569545342407)
    ·
      refine ⟨75006429824807354318013611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50004286549871569545342407 75006429824807354318013611)
      ·
        refine ⟨112509644737211031477020417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75006429824807354318013611 112509644737211031477020417)
        ·
          refine ⟨84382233552908273607765313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112509644737211031477020417 84382233552908273607765313)
          ·
            refine ⟨63286675164681205205823985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84382233552908273607765313 63286675164681205205823985)
            ·
              refine ⟨47465006373510903904367989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63286675164681205205823985 47465006373510903904367989)
              ·
                refine ⟨4449844347516647241034499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47465006373510903904367989 4449844347516647241034499)
                ·
                  refine ⟨6674766521274970861551749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449844347516647241034499 6674766521274970861551749)
                  ·
                    refine ⟨1251518722739057036540953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674766521274970861551749 1251518722739057036540953)
                    ·
                      rfl

theorem cell23_7311972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_7311972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311972 prefixEnd_7311972 := by exact prefixLift 7311972
  have htrace : WordTrace (prefixWord ++ tailWord_7311972) baseStart_7311972 baseEnd_7311972 := by
    simpa [prefixWord, tailWord_7311972, baseEnd_7311972] using wordTrace_append hprefix tailTrace_7311972
  have hstable : (prefixWord ++ tailWord_7311972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311972).length < 2 ^ (prefixWord ++ tailWord_7311972).sum := by decide
  have hdescent : baseEnd_7311972 < baseStart_7311972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7311982 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_7311982 : Nat := 118140960795 + 7311982 * 2 ^ 59
def prefixEnd_7311982 : Nat := 4983230072969 + 3 ^ 40 * 7311982 * 2
def baseEnd_7311982 : Nat := 3754561303023716070497813

theorem tailTrace_7311982 : CollatzResearch.WordTrace tailWord_7311982 prefixEnd_7311982 3754561303023716070497813 := by
  unfold tailWord_7311982
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336236624493184493711275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177793261997296983966460133 33336236624493184493711275)
  ·
    refine ⟨50004354936739776740566913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33336236624493184493711275 50004354936739776740566913)
    ·
      refine ⟨37503266202554832555425185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50004354936739776740566913 37503266202554832555425185)
      ·
        refine ⟨28127449651916124416568889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37503266202554832555425185 28127449651916124416568889)
        ·
          refine ⟨21095587238937093312426667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28127449651916124416568889 21095587238937093312426667)
          ·
            refine ⟨31643380858405639968640001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21095587238937093312426667 31643380858405639968640001)
            ·
              refine ⟨23732535643804229976480001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31643380858405639968640001 23732535643804229976480001)
              ·
                refine ⟨17799401732853172482360001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23732535643804229976480001 17799401732853172482360001)
                ·
                  refine ⟨13349551299639879361770001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17799401732853172482360001 13349551299639879361770001)
                  ·
                    refine ⟨10012163474729909521327501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13349551299639879361770001 10012163474729909521327501)
                    ·
                      refine ⟨3754561303023716070497813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10012163474729909521327501 3754561303023716070497813)
                      ·
                        rfl

theorem cell23_7311982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_7311982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7311982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7311982 prefixEnd_7311982 := by exact prefixLift 7311982
  have htrace : WordTrace (prefixWord ++ tailWord_7311982) baseStart_7311982 baseEnd_7311982 := by
    simpa [prefixWord, tailWord_7311982, baseEnd_7311982] using wordTrace_append hprefix tailTrace_7311982
  have hstable : (prefixWord ++ tailWord_7311982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7311982).length < 2 ^ (prefixWord ++ tailWord_7311982).sum := by decide
  have hdescent : baseEnd_7311982 < baseStart_7311982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7311982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312029 : List Nat := [1, 4, 2, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_7312029 : Nat := 118140960795 + 7312029 * 2 ^ 59
def prefixEnd_7312029 : Nat := 4983230072969 + 3 ^ 40 * 7312029 * 2
def baseEnd_7312029 : Nat := 3754585436614477386610097

theorem tailTrace_7312029 : CollatzResearch.WordTrace tailWord_7312029 prefixEnd_7312029 3754585436614477386610097 := by
  unfold tailWord_7312029
  simp only [CollatzResearch.WordTrace]
  refine ⟨266691607226775202976651141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177794404817850135317767427 266691607226775202976651141)
  ·
    refine ⟨50004676355020350558122089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266691607226775202976651141 50004676355020350558122089)
    ·
      refine ⟨37503507266265262918591567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50004676355020350558122089 37503507266265262918591567)
      ·
        refine ⟨56255260899397894377887351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37503507266265262918591567 56255260899397894377887351)
        ·
          refine ⟨84382891349096841566831027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56255260899397894377887351 84382891349096841566831027)
          ·
            refine ⟨126574337023645262350246541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84382891349096841566831027 126574337023645262350246541)
            ·
              refine ⟨47465376383866973381342453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126574337023645262350246541 47465376383866973381342453)
              ·
                refine ⟨4449879035987528754500855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47465376383866973381342453 4449879035987528754500855)
                ·
                  refine ⟨6674818553981293131751283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449879035987528754500855 6674818553981293131751283)
                  ·
                    refine ⟨10012227830971939697626925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6674818553981293131751283 10012227830971939697626925)
                    ·
                      refine ⟨3754585436614477386610097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10012227830971939697626925 3754585436614477386610097)
                      ·
                        rfl

theorem cell23_7312029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_7312029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312029 prefixEnd_7312029 := by exact prefixLift 7312029
  have htrace : WordTrace (prefixWord ++ tailWord_7312029) baseStart_7312029 baseEnd_7312029 := by
    simpa [prefixWord, tailWord_7312029, baseEnd_7312029] using wordTrace_append hprefix tailTrace_7312029
  have hstable : (prefixWord ++ tailWord_7312029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312029).length < 2 ^ (prefixWord ++ tailWord_7312029).sum := by decide
  have hdescent : baseEnd_7312029 < baseStart_7312029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312032 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 1, 5]
def baseStart_7312032 : Nat := 118140960795 + 7312032 * 2 ^ 59
def prefixEnd_7312032 : Nat := 4983230072969 + 3 ^ 40 * 7312032 * 2
def baseEnd_7312032 : Nat := 1251528992352146958290861

theorem tailTrace_7312032 : CollatzResearch.WordTrace tailWord_7312032 prefixEnd_7312032 1251528992352146958290861 := by
  unfold tailWord_7312032
  simp only [CollatzResearch.WordTrace]
  refine ⟨133345858322882167244505175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177794477763842889659340233 133345858322882167244505175)
  ·
    refine ⟨200018787484323250866757763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133345858322882167244505175 200018787484323250866757763)
    ·
      refine ⟨300028181226484876300136645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200018787484323250866757763 300028181226484876300136645)
      ·
        refine ⟨56255283979965914306275621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300028181226484876300136645 56255283979965914306275621)
        ·
          refine ⟨10547865746243608932426679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56255283979965914306275621 10547865746243608932426679)
          ·
            refine ⟨15821798619365413398640019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547865746243608932426679 15821798619365413398640019)
            ·
              refine ⟨23732697929048120097960029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15821798619365413398640019 23732697929048120097960029)
              ·
                refine ⟨8899761723393045036735011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23732697929048120097960029 8899761723393045036735011)
                ·
                  refine ⟨13349642585089567555102517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8899761723393045036735011 13349642585089567555102517)
                  ·
                    refine ⟨1251528992352146958290861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13349642585089567555102517 1251528992352146958290861)
                    ·
                      rfl

theorem cell23_7312032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_7312032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312032 prefixEnd_7312032 := by exact prefixLift 7312032
  have htrace : WordTrace (prefixWord ++ tailWord_7312032) baseStart_7312032 baseEnd_7312032 := by
    simpa [prefixWord, tailWord_7312032, baseEnd_7312032] using wordTrace_append hprefix tailTrace_7312032
  have hstable : (prefixWord ++ tailWord_7312032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312032).length < 2 ^ (prefixWord ++ tailWord_7312032).sum := by decide
  have hdescent : baseEnd_7312032 < baseStart_7312032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312046 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_7312046 : Nat := 118140960795 + 7312046 * 2 ^ 59
def prefixEnd_7312046 : Nat := 4983230072969 + 3 ^ 40 * 7312046 * 2
def baseEnd_7312046 : Nat := 3754594165785603820097519

theorem tailTrace_7312046 : CollatzResearch.WordTrace tailWord_7312046 prefixEnd_7312046 3754594165785603820097519 := by
  unfold tailWord_7312046
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336528408464201860002499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177794818178475743253346661 33336528408464201860002499)
  ·
    refine ⟨50004792612696302790003749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33336528408464201860002499 50004792612696302790003749)
    ·
      refine ⟨9375898614880556773125703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50004792612696302790003749 9375898614880556773125703)
      ·
        refine ⟨14063847922320835159688555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9375898614880556773125703 14063847922320835159688555)
        ·
          refine ⟨21095771883481252739532833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063847922320835159688555 21095771883481252739532833)
          ·
            refine ⟨15821828912610939554649625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21095771883481252739532833 15821828912610939554649625)
            ·
              refine ⟨11866371684458204665987219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15821828912610939554649625 11866371684458204665987219)
              ·
                refine ⟨17799557526687306998980829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11866371684458204665987219 17799557526687306998980829)
                ·
                  refine ⟨6674834072507740124617811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17799557526687306998980829 6674834072507740124617811)
                  ·
                    refine ⟨10012251108761610186926717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6674834072507740124617811 10012251108761610186926717)
                    ·
                      refine ⟨3754594165785603820097519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10012251108761610186926717 3754594165785603820097519)
                      ·
                        rfl

theorem cell23_7312046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_7312046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312046 prefixEnd_7312046 := by exact prefixLift 7312046
  have htrace : WordTrace (prefixWord ++ tailWord_7312046) baseStart_7312046 baseEnd_7312046 := by
    simpa [prefixWord, tailWord_7312046, baseEnd_7312046] using wordTrace_append hprefix tailTrace_7312046
  have hstable : (prefixWord ++ tailWord_7312046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312046).length < 2 ^ (prefixWord ++ tailWord_7312046).sum := by decide
  have hdescent : baseEnd_7312046 < baseStart_7312046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312048 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_7312048 : Nat := 118140960795 + 7312048 * 2 ^ 59
def prefixEnd_7312048 : Nat := 4983230072969 + 3 ^ 40 * 7312048 * 2
def baseEnd_7312048 : Nat := 3754595192746912812272509

theorem tailTrace_7312048 : CollatzResearch.WordTrace tailWord_7312048 prefixEnd_7312048 3754595192746912812272509 := by
  unfold tailWord_7312048
  simp only [CollatzResearch.WordTrace]
  refine ⟨133346150106853184610796399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177794866809137579481061865 133346150106853184610796399)
  ·
    refine ⟨200019225160279776916194599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133346150106853184610796399 200019225160279776916194599)
    ·
      refine ⟨300028837740419665374291899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200019225160279776916194599 300028837740419665374291899)
      ·
        refine ⟨450043256610629498061437849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300028837740419665374291899 450043256610629498061437849)
        ·
          refine ⟨337532442457972123546078387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450043256610629498061437849 337532442457972123546078387)
          ·
            refine ⟨506298663686958185319117581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337532442457972123546078387 506298663686958185319117581)
            ·
              refine ⟨189861998882609319494669093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506298663686958185319117581 189861998882609319494669093)
              ·
                refine ⟨35599124790489247405250455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189861998882609319494669093 35599124790489247405250455)
                ·
                  refine ⟨53398687185733871107875683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35599124790489247405250455 53398687185733871107875683)
                  ·
                    refine ⟨80098030778600806661813525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53398687185733871107875683 80098030778600806661813525)
                    ·
                      refine ⟨3754595192746912812272509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80098030778600806661813525 3754595192746912812272509)
                      ·
                        rfl

theorem cell23_7312048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_7312048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312048 prefixEnd_7312048 := by exact prefixLift 7312048
  have htrace : WordTrace (prefixWord ++ tailWord_7312048) baseStart_7312048 baseEnd_7312048 := by
    simpa [prefixWord, tailWord_7312048, baseEnd_7312048] using wordTrace_append hprefix tailTrace_7312048
  have hstable : (prefixWord ++ tailWord_7312048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312048).length < 2 ^ (prefixWord ++ tailWord_7312048).sum := by decide
  have hdescent : baseEnd_7312048 < baseStart_7312048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312058 : List Nat := [3, 1, 1, 1, 2, 3, 2, 10]
def baseStart_7312058 : Nat := 118140960795 + 7312058 * 2 ^ 59
def prefixEnd_7312058 : Nat := 4983230072969 + 3 ^ 40 * 7312058 * 2
def baseEnd_7312058 : Nat := 139059271390868806412869

theorem tailTrace_7312058 : CollatzResearch.WordTrace tailWord_7312058 prefixEnd_7312058 139059271390868806412869 := by
  unfold tailWord_7312058
  simp only [CollatzResearch.WordTrace]
  refine ⟨66673166235917535232364207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177795109962446760619637885 66673166235917535232364207)
  ·
    refine ⟨100009749353876302848546311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66673166235917535232364207 100009749353876302848546311)
    ·
      refine ⟨150014624030814454272819467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100009749353876302848546311 150014624030814454272819467)
      ·
        refine ⟨225021936046221681409229201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150014624030814454272819467 225021936046221681409229201)
        ·
          refine ⟨168766452034666261056921901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225021936046221681409229201 168766452034666261056921901)
          ·
            refine ⟨63287419512999847896345713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168766452034666261056921901 63287419512999847896345713)
            ·
              refine ⟨47465564634749885922259285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63287419512999847896345713 47465564634749885922259285)
              ·
                refine ⟨139059271390868806412869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47465564634749885922259285 139059271390868806412869)
                ·
                  rfl

theorem cell23_7312058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 10].length) (baseStart_7312058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312058 prefixEnd_7312058 := by exact prefixLift 7312058
  have htrace : WordTrace (prefixWord ++ tailWord_7312058) baseStart_7312058 baseEnd_7312058 := by
    simpa [prefixWord, tailWord_7312058, baseEnd_7312058] using wordTrace_append hprefix tailTrace_7312058
  have hstable : (prefixWord ++ tailWord_7312058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312058).length < 2 ^ (prefixWord ++ tailWord_7312058).sum := by decide
  have hdescent : baseEnd_7312058 < baseStart_7312058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312072 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_7312072 : Nat := 118140960795 + 7312072 * 2 ^ 59
def prefixEnd_7312072 : Nat := 4983230072969 + 3 ^ 40 * 7312072 * 2
def baseEnd_7312072 : Nat := 3754607516282620718372399

theorem tailTrace_7312072 : CollatzResearch.WordTrace tailWord_7312072 prefixEnd_7312072 3754607516282620718372399 := by
  unfold tailWord_7312072
  simp only [CollatzResearch.WordTrace]
  refine ⟨133346587782809710660233235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177795450377079614213644313 133346587782809710660233235)
  ·
    refine ⟨200019881674214565990349853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133346587782809710660233235 200019881674214565990349853)
    ·
      refine ⟨75007455627830462246381195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200019881674214565990349853 75007455627830462246381195)
      ·
        refine ⟨112511183441745693369571793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75007455627830462246381195 112511183441745693369571793)
        ·
          refine ⟨84383387581309270027178845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112511183441745693369571793 84383387581309270027178845)
          ·
            refine ⟨31643770342990976260192067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84383387581309270027178845 31643770342990976260192067)
            ·
              refine ⟨47465655514486464390288101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31643770342990976260192067 47465655514486464390288101)
              ·
                refine ⟨8899810408966212073179019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47465655514486464390288101 8899810408966212073179019)
                ·
                  refine ⟨13349715613449318109768529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8899810408966212073179019 13349715613449318109768529)
                  ·
                    refine ⟨10012286710086988582326397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13349715613449318109768529 10012286710086988582326397)
                    ·
                      refine ⟨3754607516282620718372399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10012286710086988582326397 3754607516282620718372399)
                      ·
                        rfl

theorem cell23_7312072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_7312072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312072 prefixEnd_7312072 := by exact prefixLift 7312072
  have htrace : WordTrace (prefixWord ++ tailWord_7312072) baseStart_7312072 baseEnd_7312072 := by
    simpa [prefixWord, tailWord_7312072, baseEnd_7312072] using wordTrace_append hprefix tailTrace_7312072
  have hstable : (prefixWord ++ tailWord_7312072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312072).length < 2 ^ (prefixWord ++ tailWord_7312072).sum := by decide
  have hdescent : baseEnd_7312072 < baseStart_7312072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312092 : List Nat := [2, 2, 5, 1, 1, 3, 9]
def baseStart_7312092 : Nat := 118140960795 + 7312092 * 2 ^ 59
def prefixEnd_7312092 : Nat := 4983230072969 + 3 ^ 40 * 7312092 * 2
def baseEnd_7312092 : Nat := 46353305998712477038547

theorem tailTrace_7312092 : CollatzResearch.WordTrace tailWord_7312092 prefixEnd_7312092 46353305998712477038547 := by
  unfold tailWord_7312092
  simp only [CollatzResearch.WordTrace]
  refine ⟨133346952512773482368097265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177795936683697976490796353 133346952512773482368097265)
  ·
    refine ⟨100010214384580111776072949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133346952512773482368097265 100010214384580111776072949)
    ·
      refine ⟨9375957598554385479006839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100010214384580111776072949 9375957598554385479006839)
      ·
        refine ⟨14063936397831578218510259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9375957598554385479006839 14063936397831578218510259)
        ·
          refine ⟨21095904596747367327765389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063936397831578218510259 21095904596747367327765389)
          ·
            refine ⟨7910964223780262747912021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21095904596747367327765389 7910964223780262747912021)
            ·
              refine ⟨46353305998712477038547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7910964223780262747912021 46353305998712477038547)
              ·
                rfl

theorem cell23_7312092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 9].length) (baseStart_7312092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312092 prefixEnd_7312092 := by exact prefixLift 7312092
  have htrace : WordTrace (prefixWord ++ tailWord_7312092) baseStart_7312092 baseEnd_7312092 := by
    simpa [prefixWord, tailWord_7312092, baseEnd_7312092] using wordTrace_append hprefix tailTrace_7312092
  have hstable : (prefixWord ++ tailWord_7312092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312092).length < 2 ^ (prefixWord ++ tailWord_7312092).sum := by decide
  have hdescent : baseEnd_7312092 < baseStart_7312092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312112 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 3, 3, 2]
def baseStart_7312112 : Nat := 118140960795 + 7312112 * 2 ^ 59
def prefixEnd_7312112 : Nat := 4983230072969 + 3 ^ 40 * 7312112 * 2
def baseEnd_7312112 : Nat := 3754628055508800561872215

theorem tailTrace_7312112 : CollatzResearch.WordTrace tailWord_7312112 prefixEnd_7312112 3754628055508800561872215 := by
  unfold tailWord_7312112
  simp only [CollatzResearch.WordTrace]
  refine ⟨133347317242737254075961295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177796422990316338767948393 133347317242737254075961295)
  ·
    refine ⟨200020975864105881113941943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133347317242737254075961295 200020975864105881113941943)
    ·
      refine ⟨300031463796158821670912915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200020975864105881113941943 300031463796158821670912915)
      ·
        refine ⟨450047195694238232506369373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300031463796158821670912915 450047195694238232506369373)
        ·
          refine ⟨168767698385339337189888515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450047195694238232506369373 168767698385339337189888515)
          ·
            refine ⟨253151547578009005784832773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168767698385339337189888515 253151547578009005784832773)
            ·
              refine ⟨47465915170876688584656145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253151547578009005784832773 47465915170876688584656145)
              ·
                refine ⟨35599436378157516438492109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47465915170876688584656145 35599436378157516438492109)
                ·
                  refine ⟨13349788641809068664434541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35599436378157516438492109 13349788641809068664434541)
                  ·
                    refine ⟨5006170740678400749162953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13349788641809068664434541 5006170740678400749162953)
                    ·
                      refine ⟨3754628055508800561872215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5006170740678400749162953 3754628055508800561872215)
                      ·
                        rfl

theorem cell23_7312112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 3, 2].length) (baseStart_7312112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312112 prefixEnd_7312112 := by exact prefixLift 7312112
  have htrace : WordTrace (prefixWord ++ tailWord_7312112) baseStart_7312112 baseEnd_7312112 := by
    simpa [prefixWord, tailWord_7312112, baseEnd_7312112] using wordTrace_append hprefix tailTrace_7312112
  have hstable : (prefixWord ++ tailWord_7312112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312112).length < 2 ^ (prefixWord ++ tailWord_7312112).sum := by decide
  have hdescent : baseEnd_7312112 < baseStart_7312112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312145 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_7312145 : Nat := 118140960795 + 7312145 * 2 ^ 59
def prefixEnd_7312145 : Nat := 4983230072969 + 3 ^ 40 * 7312145 * 2
def baseEnd_7312145 : Nat := 3754645000370398932759563

theorem tailTrace_7312145 : CollatzResearch.WordTrace tailWord_7312145 prefixEnd_7312145 3754645000370398932759563 := by
  unfold tailWord_7312145
  simp only [CollatzResearch.WordTrace]
  refine ⟨266695838094354954787873889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177797225396236636525249259 266695838094354954787873889)
  ·
    refine ⟨200021878570766216090905417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266695838094354954787873889 200021878570766216090905417)
    ·
      refine ⟨150016408928074662068179063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200021878570766216090905417 150016408928074662068179063)
      ·
        refine ⟨225024613392111993102268595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150016408928074662068179063 225024613392111993102268595)
        ·
          refine ⟨337536920088167989653402893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225024613392111993102268595 337536920088167989653402893)
          ·
            refine ⟨126576345033062996120026085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337536920088167989653402893 126576345033062996120026085)
            ·
              refine ⟨23733064693699311772504891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126576345033062996120026085 23733064693699311772504891)
              ·
                refine ⟨35599597040548967658757337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23733064693699311772504891 35599597040548967658757337)
                ·
                  refine ⟨26699697780411725744068003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35599597040548967658757337 26699697780411725744068003)
                  ·
                    refine ⟨40049546670617588616102005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26699697780411725744068003 40049546670617588616102005)
                    ·
                      refine ⟨3754645000370398932759563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40049546670617588616102005 3754645000370398932759563)
                      ·
                        rfl

theorem cell23_7312145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_7312145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312145 prefixEnd_7312145 := by exact prefixLift 7312145
  have htrace : WordTrace (prefixWord ++ tailWord_7312145) baseStart_7312145 baseEnd_7312145 := by
    simpa [prefixWord, tailWord_7312145, baseEnd_7312145] using wordTrace_append hprefix tailTrace_7312145
  have hstable : (prefixWord ++ tailWord_7312145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312145).length < 2 ^ (prefixWord ++ tailWord_7312145).sum := by decide
  have hdescent : baseEnd_7312145 < baseStart_7312145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312162 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_7312162 : Nat := 118140960795 + 7312162 * 2 ^ 59
def prefixEnd_7312162 : Nat := 4983230072969 + 3 ^ 40 * 7312162 * 2
def baseEnd_7312162 : Nat := 3754653729541525366246985

theorem tailTrace_7312162 : CollatzResearch.WordTrace tailWord_7312162 prefixEnd_7312162 3754653729541525366246985 := by
  unfold tailWord_7312162
  simp only [CollatzResearch.WordTrace]
  refine ⟨66674114533823341672810685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177797638756862244460828493 66674114533823341672810685)
  ·
    refine ⟨25002792950183753127304007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66674114533823341672810685 25002792950183753127304007)
    ·
      refine ⟨37504189425275629690956011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25002792950183753127304007 37504189425275629690956011)
      ·
        refine ⟨56256284137913444536434017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37504189425275629690956011 56256284137913444536434017)
        ·
          refine ⟨42192213103435083402325513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56256284137913444536434017 42192213103435083402325513)
          ·
            refine ⟨31644159827576312551744135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42192213103435083402325513 31644159827576312551744135)
            ·
              refine ⟨47466239741364468827616203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31644159827576312551744135 47466239741364468827616203)
              ·
                refine ⟨71199359612046703241424305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47466239741364468827616203 71199359612046703241424305)
                ·
                  refine ⟨53399519709035027431068229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71199359612046703241424305 53399519709035027431068229)
                  ·
                    refine ⟨10012409945444067643325293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53399519709035027431068229 10012409945444067643325293)
                    ·
                      refine ⟨3754653729541525366246985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10012409945444067643325293 3754653729541525366246985)
                      ·
                        rfl

theorem cell23_7312162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_7312162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312162 prefixEnd_7312162 := by exact prefixLift 7312162
  have htrace : WordTrace (prefixWord ++ tailWord_7312162) baseStart_7312162 baseEnd_7312162 := by
    simpa [prefixWord, tailWord_7312162, baseEnd_7312162] using wordTrace_append hprefix tailTrace_7312162
  have hstable : (prefixWord ++ tailWord_7312162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312162).length < 2 ^ (prefixWord ++ tailWord_7312162).sum := by decide
  have hdescent : baseEnd_7312162 < baseStart_7312162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312165 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 7]
def baseStart_7312165 : Nat := 118140960795 + 7312165 * 2 ^ 59
def prefixEnd_7312165 : Nat := 4983230072969 + 3 ^ 40 * 7312165 * 2
def baseEnd_7312165 : Nat := 417183918887054317167719

theorem tailTrace_7312165 : CollatzResearch.WordTrace tailWord_7312165 prefixEnd_7312165 417183918887054317167719 := by
  unfold tailWord_7312165
  simp only [CollatzResearch.WordTrace]
  refine ⟨266696567554282498203601949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177797711702854998802401299 266696567554282498203601949)
  ·
    refine ⟨100011212832855936826350731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266696567554282498203601949 100011212832855936826350731)
    ·
      refine ⟨150016819249283905239526097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100011212832855936826350731 150016819249283905239526097)
      ·
        refine ⟨112512614436962928929644573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150016819249283905239526097 112512614436962928929644573)
        ·
          refine ⟨42192230413861098348616715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112512614436962928929644573 42192230413861098348616715)
          ·
            refine ⟨63288345620791647522925073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42192230413861098348616715 63288345620791647522925073)
            ·
              refine ⟨47466259215593735642193805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63288345620791647522925073 47466259215593735642193805)
              ·
                refine ⟨17799847205847650865822677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47466259215593735642193805 17799847205847650865822677)
                ·
                  refine ⟨417183918887054317167719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17799847205847650865822677 417183918887054317167719)
                  ·
                    rfl

theorem cell23_7312165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_7312165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312165 prefixEnd_7312165 := by exact prefixLift 7312165
  have htrace : WordTrace (prefixWord ++ tailWord_7312165) baseStart_7312165 baseEnd_7312165 := by
    simpa [prefixWord, tailWord_7312165, baseEnd_7312165] using wordTrace_append hprefix tailTrace_7312165
  have hstable : (prefixWord ++ tailWord_7312165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312165).length < 2 ^ (prefixWord ++ tailWord_7312165).sum := by decide
  have hdescent : baseEnd_7312165 < baseStart_7312165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312195 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 1, 7]
def baseStart_7312195 : Nat := 118140960795 + 7312195 * 2 ^ 59
def prefixEnd_7312195 : Nat := 4983230072969 + 3 ^ 40 * 7312195 * 2
def baseEnd_7312195 : Nat := 1251556891467707912378111

theorem tailTrace_7312195 : CollatzResearch.WordTrace tailWord_7312195 prefixEnd_7312195 1251556891467707912378111 := by
  unfold tailWord_7312195
  simp only [CollatzResearch.WordTrace]
  refine ⟨266697661744173813327194039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177798441162782542218129359 266697661744173813327194039)
  ·
    refine ⟨400046492616260719990791059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266697661744173813327194039 400046492616260719990791059)
    ·
      refine ⟨600069738924391079986186589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400046492616260719990791059 600069738924391079986186589)
      ·
        refine ⟨225026152096646654994819971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600069738924391079986186589 225026152096646654994819971)
        ·
          refine ⟨337539228144969982492229957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225026152096646654994819971 337539228144969982492229957)
          ·
            refine ⟨63288605277181871717293117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337539228144969982492229957 63288605277181871717293117)
            ·
              refine ⟨23733226978943201893984919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63288605277181871717293117 23733226978943201893984919)
              ·
                refine ⟨35599840468414802840977379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23733226978943201893984919 35599840468414802840977379)
                ·
                  refine ⟨53399760702622204261466069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35599840468414802840977379 53399760702622204261466069)
                  ·
                    refine ⟨1251556891467707912378111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53399760702622204261466069 1251556891467707912378111)
                    ·
                      rfl

theorem cell23_7312195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 7].length) (baseStart_7312195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312195 prefixEnd_7312195 := by exact prefixLift 7312195
  have htrace : WordTrace (prefixWord ++ tailWord_7312195) baseStart_7312195 baseEnd_7312195 := by
    simpa [prefixWord, tailWord_7312195, baseEnd_7312195] using wordTrace_append hprefix tailTrace_7312195
  have hstable : (prefixWord ++ tailWord_7312195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312195).length < 2 ^ (prefixWord ++ tailWord_7312195).sum := by decide
  have hdescent : baseEnd_7312195 < baseStart_7312195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312202 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_7312202 : Nat := 118140960795 + 7312202 * 2 ^ 59
def prefixEnd_7312202 : Nat := 4983230072969 + 3 ^ 40 * 7312202 * 2
def baseEnd_7312202 : Nat := 3754674268767705209746801

theorem tailTrace_7312202 : CollatzResearch.WordTrace tailWord_7312202 prefixEnd_7312202 3754674268767705209746801 := by
  unfold tailWord_7312202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66674479263787113380674715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177798611370098969015132573 66674479263787113380674715)
  ·
    refine ⟨100011718895680670071012073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66674479263787113380674715 100011718895680670071012073)
    ·
      refine ⟨75008789171760502553259055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100011718895680670071012073 75008789171760502553259055)
      ·
        refine ⟨112513183757640753829888583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75008789171760502553259055 112513183757640753829888583)
        ·
          refine ⟨168769775636461130744832875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112513183757640753829888583 168769775636461130744832875)
          ·
            refine ⟨253154663454691696117249313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168769775636461130744832875 253154663454691696117249313)
            ·
              refine ⟨189865997591018772087936985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253154663454691696117249313 189865997591018772087936985)
              ·
                refine ⟨142399498193264079065952739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189865997591018772087936985 142399498193264079065952739)
                ·
                  refine ⟨213599247289896118598929109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142399498193264079065952739 213599247289896118598929109)
                  ·
                    refine ⟨5006232358356940279662401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213599247289896118598929109 5006232358356940279662401)
                    ·
                      refine ⟨3754674268767705209746801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5006232358356940279662401 3754674268767705209746801)
                      ·
                        rfl

theorem cell23_7312202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_7312202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312202 prefixEnd_7312202 := by exact prefixLift 7312202
  have htrace : WordTrace (prefixWord ++ tailWord_7312202) baseStart_7312202 baseEnd_7312202 := by
    simpa [prefixWord, tailWord_7312202, baseEnd_7312202] using wordTrace_append hprefix tailTrace_7312202
  have hstable : (prefixWord ++ tailWord_7312202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312202).length < 2 ^ (prefixWord ++ tailWord_7312202).sum := by decide
  have hdescent : baseEnd_7312202 < baseStart_7312202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312232 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7312232 : Nat := 118140960795 + 7312232 * 2 ^ 59
def prefixEnd_7312232 : Nat := 4983230072969 + 3 ^ 40 * 7312232 * 2
def baseEnd_7312232 : Nat := 3754689673187340092371663

theorem tailTrace_7312232 : CollatzResearch.WordTrace tailWord_7312232 prefixEnd_7312232 3754689673187340092371663 := by
  unfold tailWord_7312232
  simp only [CollatzResearch.WordTrace]
  refine ⟨133349505622519884323145475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177799340830026512430860633 133349505622519884323145475)
  ·
    refine ⟨200024258433779826484718213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133349505622519884323145475 200024258433779826484718213)
    ·
      refine ⟨37504548456333717465884665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200024258433779826484718213 37504548456333717465884665)
      ·
        refine ⟨28128411342250288099413499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37504548456333717465884665 28128411342250288099413499)
        ·
          refine ⟨42192617013375432149120249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28128411342250288099413499 42192617013375432149120249)
          ·
            refine ⟨31644462760031574111840187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42192617013375432149120249 31644462760031574111840187)
            ·
              refine ⟨47466694140047361167760281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31644462760031574111840187 47466694140047361167760281)
              ·
                refine ⟨35600020605035520875820211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47466694140047361167760281 35600020605035520875820211)
                ·
                  refine ⟨53400030907553281313730317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35600020605035520875820211 53400030907553281313730317)
                  ·
                    refine ⟨20025011590332480492648869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53400030907553281313730317 20025011590332480492648869)
                    ·
                      refine ⟨3754689673187340092371663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20025011590332480492648869 3754689673187340092371663)
                      ·
                        rfl

theorem cell23_7312232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7312232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312232 prefixEnd_7312232 := by exact prefixLift 7312232
  have htrace : WordTrace (prefixWord ++ tailWord_7312232) baseStart_7312232 baseEnd_7312232 := by
    simpa [prefixWord, tailWord_7312232, baseEnd_7312232] using wordTrace_append hprefix tailTrace_7312232
  have hstable : (prefixWord ++ tailWord_7312232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312232).length < 2 ^ (prefixWord ++ tailWord_7312232).sum := by decide
  have hdescent : baseEnd_7312232 < baseStart_7312232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312252 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_7312252 : Nat := 118140960795 + 7312252 * 2 ^ 59
def prefixEnd_7312252 : Nat := 4983230072969 + 3 ^ 40 * 7312252 * 2
def baseEnd_7312252 : Nat := 3754699942800430014121571

theorem tailTrace_7312252 : CollatzResearch.WordTrace tailWord_7312252 prefixEnd_7312252 3754699942800430014121571 := by
  unfold tailWord_7312252
  simp only [CollatzResearch.WordTrace]
  refine ⟨133349870352483656031009505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177799827136644874708012673 133349870352483656031009505)
  ·
    refine ⟨100012402764362742023257129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133349870352483656031009505 100012402764362742023257129)
    ·
      refine ⟨75009302073272056517442847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100012402764362742023257129 75009302073272056517442847)
      ·
        refine ⟨112513953109908084776164271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75009302073272056517442847 112513953109908084776164271)
        ·
          refine ⟨168770929664862127164246407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112513953109908084776164271 168770929664862127164246407)
          ·
            refine ⟨253156394497293190746369611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168770929664862127164246407 253156394497293190746369611)
            ·
              refine ⟨379734591745939786119554417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253156394497293190746369611 379734591745939786119554417)
              ·
                refine ⟨284800943809454839589665813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379734591745939786119554417 284800943809454839589665813)
                ·
                  refine ⟨13350044241068195605765585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284800943809454839589665813 13350044241068195605765585)
                  ·
                    refine ⟨10012533180801146704324189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13350044241068195605765585 10012533180801146704324189)
                    ·
                      refine ⟨3754699942800430014121571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10012533180801146704324189 3754699942800430014121571)
                      ·
                        rfl

theorem cell23_7312252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_7312252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312252 prefixEnd_7312252 := by exact prefixLift 7312252
  have htrace : WordTrace (prefixWord ++ tailWord_7312252) baseStart_7312252 baseEnd_7312252 := by
    simpa [prefixWord, tailWord_7312252, baseEnd_7312252] using wordTrace_append hprefix tailTrace_7312252
  have hstable : (prefixWord ++ tailWord_7312252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312252).length < 2 ^ (prefixWord ++ tailWord_7312252).sum := by decide
  have hdescent : baseEnd_7312252 < baseStart_7312252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312255 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 8]
def baseStart_7312255 : Nat := 118140960795 + 7312255 * 2 ^ 59
def prefixEnd_7312255 : Nat := 4983230072969 + 3 ^ 40 * 7312255 * 2
def baseEnd_7312255 : Nat := 417189053693599278042673

theorem tailTrace_7312255 : CollatzResearch.WordTrace tailWord_7312255 prefixEnd_7312255 417189053693599278042673 := by
  unfold tailWord_7312255
  simp only [CollatzResearch.WordTrace]
  refine ⟨266699850123956443574378219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177799900082637629049585479 266699850123956443574378219)
  ·
    refine ⟨400049775185934665361567329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266699850123956443574378219 400049775185934665361567329)
    ·
      refine ⟨300037331389450999021175497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400049775185934665361567329 300037331389450999021175497)
      ·
        refine ⟨225027998542088249265881623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300037331389450999021175497 225027998542088249265881623)
        ·
          refine ⟨337541997813132373898822435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225027998542088249265881623 337541997813132373898822435)
          ·
            refine ⟨506312996719698560848233653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337541997813132373898822435 506312996719698560848233653)
            ·
              refine ⟨47466843442471740079521905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506312996719698560848233653 47466843442471740079521905)
              ·
                refine ⟨35600132581853805059641429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47466843442471740079521905 35600132581853805059641429)
                ·
                  refine ⟨417189053693599278042673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35600132581853805059641429 417189053693599278042673)
                  ·
                    rfl

theorem cell23_7312255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 8].length) (baseStart_7312255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312255 prefixEnd_7312255 := by exact prefixLift 7312255
  have htrace : WordTrace (prefixWord ++ tailWord_7312255) baseStart_7312255 baseEnd_7312255 := by
    simpa [prefixWord, tailWord_7312255, baseEnd_7312255] using wordTrace_append hprefix tailTrace_7312255
  have hstable : (prefixWord ++ tailWord_7312255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312255).length < 2 ^ (prefixWord ++ tailWord_7312255).sum := by decide
  have hdescent : baseEnd_7312255 < baseStart_7312255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312275 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6]
def baseStart_7312275 : Nat := 118140960795 + 7312275 * 2 ^ 59
def prefixEnd_7312275 : Nat := 4983230072969 + 3 ^ 40 * 7312275 * 2
def baseEnd_7312275 : Nat := 3754711752855483424133965

theorem tailTrace_7312275 : CollatzResearch.WordTrace tailWord_7312275 prefixEnd_7312275 3754711752855483424133965 := by
  unfold tailWord_7312275
  simp only [CollatzResearch.WordTrace]
  refine ⟨266700579583883986990106279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177800386389255991326737519 266700579583883986990106279)
  ·
    refine ⟨400050869375825980485159419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266700579583883986990106279 400050869375825980485159419)
    ·
      refine ⟨600076304063738970727739129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400050869375825980485159419 600076304063738970727739129)
      ·
        refine ⟨450057228047804228045804347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600076304063738970727739129 450057228047804228045804347)
        ·
          refine ⟨675085842071706342068706521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450057228047804228045804347 675085842071706342068706521)
          ·
            refine ⟨506314381553779756551529891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675085842071706342068706521 506314381553779756551529891)
            ·
              refine ⟨759471572330669634827294837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506314381553779756551529891 759471572330669634827294837)
              ·
                refine ⟨71200459906000278265058891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 759471572330669634827294837 71200459906000278265058891)
                ·
                  refine ⟨106800689859000417397588337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71200459906000278265058891 106800689859000417397588337)
                  ·
                    refine ⟨80100517394250313048191253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106800689859000417397588337 80100517394250313048191253)
                    ·
                      refine ⟨3754711752855483424133965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80100517394250313048191253 3754711752855483424133965)
                      ·
                        rfl

theorem cell23_7312275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_7312275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312275 prefixEnd_7312275 := by exact prefixLift 7312275
  have htrace : WordTrace (prefixWord ++ tailWord_7312275) baseStart_7312275 baseEnd_7312275 := by
    simpa [prefixWord, tailWord_7312275, baseEnd_7312275] using wordTrace_append hprefix tailTrace_7312275
  have hstable : (prefixWord ++ tailWord_7312275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312275).length < 2 ^ (prefixWord ++ tailWord_7312275).sum := by decide
  have hdescent : baseEnd_7312275 < baseStart_7312275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312289 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 6]
def baseStart_7312289 : Nat := 118140960795 + 7312289 * 2 ^ 59
def prefixEnd_7312289 : Nat := 4983230072969 + 3 ^ 40 * 7312289 * 2
def baseEnd_7312289 : Nat := 417190993509405152150989

theorem tailTrace_7312289 : CollatzResearch.WordTrace tailWord_7312289 prefixEnd_7312289 417190993509405152150989 := by
  unfold tailWord_7312289
  simp only [CollatzResearch.WordTrace]
  refine ⟨266701090205833267381115921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177800726803888844920743947 266701090205833267381115921)
  ·
    refine ⟨200025817654374950535836941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266701090205833267381115921 200025817654374950535836941)
    ·
      refine ⟨75009681620390606450938853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200025817654374950535836941 75009681620390606450938853)
      ·
        refine ⟨14064315303823238709551035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75009681620390606450938853 14064315303823238709551035)
        ·
          refine ⟨21096472955734858064326553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14064315303823238709551035 21096472955734858064326553)
          ·
            refine ⟨15822354716801143548244915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21096472955734858064326553 15822354716801143548244915)
            ·
              refine ⟨23733532075201715322367373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15822354716801143548244915 23733532075201715322367373)
              ·
                refine ⟨8900074528200643245887765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23733532075201715322367373 8900074528200643245887765)
                ·
                  refine ⟨417190993509405152150989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8900074528200643245887765 417190993509405152150989)
                  ·
                    rfl

theorem cell23_7312289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 6].length) (baseStart_7312289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312289 prefixEnd_7312289 := by exact prefixLift 7312289
  have htrace : WordTrace (prefixWord ++ tailWord_7312289) baseStart_7312289 baseEnd_7312289 := by
    simpa [prefixWord, tailWord_7312289, baseEnd_7312289] using wordTrace_append hprefix tailTrace_7312289
  have hstable : (prefixWord ++ tailWord_7312289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312289).length < 2 ^ (prefixWord ++ tailWord_7312289).sum := by decide
  have hdescent : baseEnd_7312289 < baseStart_7312289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312315 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 10]
def baseStart_7312315 : Nat := 118140960795 + 7312315 * 2 ^ 59
def prefixEnd_7312315 : Nat := 4983230072969 + 3 ^ 40 * 7312315 * 2
def baseEnd_7312315 : Nat := 1251577430693887755877927

theorem tailTrace_7312315 : CollatzResearch.WordTrace tailWord_7312315 prefixEnd_7312315 1251577430693887755877927 := by
  unfold tailWord_7312315
  simp only [CollatzResearch.WordTrace]
  refine ⟨266702038503739073821562399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177801359002492715881041599 266702038503739073821562399)
  ·
    refine ⟨400053057755608610732343599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266702038503739073821562399 400053057755608610732343599)
    ·
      refine ⟨600079586633412916098515399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400053057755608610732343599 600079586633412916098515399)
      ·
        refine ⟨900119379950119374147773099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600079586633412916098515399 900119379950119374147773099)
        ·
          refine ⟨1350179069925179061221659649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900119379950119374147773099 1350179069925179061221659649)
          ·
            refine ⟨1012634302443884295916244737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350179069925179061221659649 1012634302443884295916244737)
            ·
              refine ⟨759475726832913221937183553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012634302443884295916244737 759475726832913221937183553)
              ·
                refine ⟨569606795124684916452887665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759475726832913221937183553 569606795124684916452887665)
                ·
                  refine ⟨427205096343513687339665749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569606795124684916452887665 427205096343513687339665749)
                  ·
                    refine ⟨1251577430693887755877927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 427205096343513687339665749 1251577430693887755877927)
                    ·
                      rfl

theorem cell23_7312315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_7312315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312315 prefixEnd_7312315 := by exact prefixLift 7312315
  have htrace : WordTrace (prefixWord ++ tailWord_7312315) baseStart_7312315 baseEnd_7312315 := by
    simpa [prefixWord, tailWord_7312315, baseEnd_7312315] using wordTrace_append hprefix tailTrace_7312315
  have hstable : (prefixWord ++ tailWord_7312315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312315).length < 2 ^ (prefixWord ++ tailWord_7312315).sum := by decide
  have hdescent : baseEnd_7312315 < baseStart_7312315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312332 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_7312332 : Nat := 118140960795 + 7312332 * 2 ^ 59
def prefixEnd_7312332 : Nat := 4983230072969 + 3 ^ 40 * 7312332 * 2
def baseEnd_7312332 : Nat := 1251580340417596567040401

theorem tailTrace_7312332 : CollatzResearch.WordTrace tailWord_7312332 prefixEnd_7312332 1251580340417596567040401 := by
  unfold tailWord_7312332
  simp only [CollatzResearch.WordTrace]
  refine ⟨133351329272338742862465625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177801772363118323816620833 133351329272338742862465625)
  ·
    refine ⟨100013496954254057146849219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133351329272338742862465625 100013496954254057146849219)
    ·
      refine ⟨150020245431381085720273829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100013496954254057146849219 150020245431381085720273829)
      ·
        refine ⟨28128796018383953572551343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150020245431381085720273829 28128796018383953572551343)
        ·
          refine ⟨42193194027575930358827015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28128796018383953572551343 42193194027575930358827015)
          ·
            refine ⟨63289791041363895538240523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42193194027575930358827015 63289791041363895538240523)
            ·
              refine ⟨94934686562045843307360785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63289791041363895538240523 94934686562045843307360785)
              ·
                refine ⟨71201014921534382480520589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94934686562045843307360785 71201014921534382480520589)
                ·
                  refine ⟨26700380595575393430195221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71201014921534382480520589 26700380595575393430195221)
                  ·
                    refine ⟨1251580340417596567040401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26700380595575393430195221 1251580340417596567040401)
                    ·
                      rfl

theorem cell23_7312332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_7312332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312332 prefixEnd_7312332 := by exact prefixLift 7312332
  have htrace : WordTrace (prefixWord ++ tailWord_7312332) baseStart_7312332 baseEnd_7312332 := by
    simpa [prefixWord, tailWord_7312332, baseEnd_7312332] using wordTrace_append hprefix tailTrace_7312332
  have hstable : (prefixWord ++ tailWord_7312332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312332).length < 2 ^ (prefixWord ++ tailWord_7312332).sum := by decide
  have hdescent : baseEnd_7312332 < baseStart_7312332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312349 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_7312349 : Nat := 118140960795 + 7312349 * 2 ^ 59
def prefixEnd_7312349 : Nat := 4983230072969 + 3 ^ 40 * 7312349 * 2
def baseEnd_7312349 : Nat := 1251583250141305378202875

theorem tailTrace_7312349 : CollatzResearch.WordTrace tailWord_7312349 prefixEnd_7312349 1251583250141305378202875 := by
  unfold tailWord_7312349
  simp only [CollatzResearch.WordTrace]
  refine ⟨266703278585615897628300101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177802185723743931752200067 266703278585615897628300101)
  ·
    refine ⟨50006864734802980805306269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266703278585615897628300101 50006864734802980805306269)
    ·
      refine ⟨18752574275551117801989851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50006864734802980805306269 18752574275551117801989851)
      ·
        refine ⟨28128861413326676702984777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18752574275551117801989851 28128861413326676702984777)
        ·
          refine ⟨21096646059995007527238583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28128861413326676702984777 21096646059995007527238583)
          ·
            refine ⟨31644969089992511290857875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21096646059995007527238583 31644969089992511290857875)
            ·
              refine ⟨47467453634988766936286813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31644969089992511290857875 47467453634988766936286813)
              ·
                refine ⟨17800295113120787601107555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47467453634988766936286813 17800295113120787601107555)
                ·
                  refine ⟨26700442669681181401661333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17800295113120787601107555 26700442669681181401661333)
                  ·
                    refine ⟨1251583250141305378202875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26700442669681181401661333 1251583250141305378202875)
                    ·
                      rfl

theorem cell23_7312349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_7312349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312349 prefixEnd_7312349 := by exact prefixLift 7312349
  have htrace : WordTrace (prefixWord ++ tailWord_7312349) baseStart_7312349 baseEnd_7312349 := by
    simpa [prefixWord, tailWord_7312349, baseEnd_7312349] using wordTrace_append hprefix tailTrace_7312349
  have hstable : (prefixWord ++ tailWord_7312349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312349).length < 2 ^ (prefixWord ++ tailWord_7312349).sum := by decide
  have hdescent : baseEnd_7312349 < baseStart_7312349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312369 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_7312369 : Nat := 118140960795 + 7312369 * 2 ^ 59
def prefixEnd_7312369 : Nat := 4983230072969 + 3 ^ 40 * 7312369 * 2
def baseEnd_7312369 : Nat := 3754760020037006056358533

theorem tailTrace_7312369 : CollatzResearch.WordTrace tailWord_7312369 prefixEnd_7312369 3754760020037006056358533 := by
  unfold tailWord_7312369
  simp only [CollatzResearch.WordTrace]
  refine ⟨266704008045543441044028161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177802672030362294029352107 266704008045543441044028161)
  ·
    refine ⟨200028006034157580783021121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266704008045543441044028161 200028006034157580783021121)
    ·
      refine ⟨150021004525618185587265841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200028006034157580783021121 150021004525618185587265841)
      ·
        refine ⟨112515753394213639190449381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150021004525618185587265841 112515753394213639190449381)
        ·
          refine ⟨21096703761415057348209259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112515753394213639190449381 21096703761415057348209259)
          ·
            refine ⟨31645055642122586022313889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21096703761415057348209259 31645055642122586022313889)
            ·
              refine ⟨23733791731591939516735417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31645055642122586022313889 23733791731591939516735417)
              ·
                refine ⟨17800343798693954637551563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23733791731591939516735417 17800343798693954637551563)
                ·
                  refine ⟨26700515698040931956327345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17800343798693954637551563 26700515698040931956327345)
                  ·
                    refine ⟨20025386773530698967245509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26700515698040931956327345 20025386773530698967245509)
                    ·
                      refine ⟨3754760020037006056358533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20025386773530698967245509 3754760020037006056358533)
                      ·
                        rfl

theorem cell23_7312369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_7312369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312369 prefixEnd_7312369 := by exact prefixLift 7312369
  have htrace : WordTrace (prefixWord ++ tailWord_7312369) baseStart_7312369 baseEnd_7312369 := by
    simpa [prefixWord, tailWord_7312369, baseEnd_7312369] using wordTrace_append hprefix tailTrace_7312369
  have hstable : (prefixWord ++ tailWord_7312369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312369).length < 2 ^ (prefixWord ++ tailWord_7312369).sum := by decide
  have hdescent : baseEnd_7312369 < baseStart_7312369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312370 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_7312370 : Nat := 118140960795 + 7312370 * 2 ^ 59
def prefixEnd_7312370 : Nat := 4983230072969 + 3 ^ 40 * 7312370 * 2
def baseEnd_7312370 : Nat := 1251586844505886850815343

theorem tailTrace_7312370 : CollatzResearch.WordTrace tailWord_7312370 prefixEnd_7312370 1251586844505886850815343 := by
  unfold tailWord_7312370
  simp only [CollatzResearch.WordTrace]
  refine ⟨66676011129634954553703641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177802696345693212143209709 66676011129634954553703641)
  ·
    refine ⟨50007008347226215915277731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66676011129634954553703641 50007008347226215915277731)
    ·
      refine ⟨75010512520839323872916597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50007008347226215915277731 75010512520839323872916597)
      ·
        refine ⟨7032235548828686613085931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75010512520839323872916597 7032235548828686613085931)
        ·
          refine ⟨10548353323243029919628897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7032235548828686613085931 10548353323243029919628897)
          ·
            refine ⟨7911264992432272439721673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10548353323243029919628897 7911264992432272439721673)
            ·
              refine ⟨5933448744324204329791255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7911264992432272439721673 5933448744324204329791255)
              ·
                refine ⟨8900173116486306494686883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5933448744324204329791255 8900173116486306494686883)
                ·
                  refine ⟨13350259674729459742030325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8900173116486306494686883 13350259674729459742030325)
                  ·
                    refine ⟨1251586844505886850815343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13350259674729459742030325 1251586844505886850815343)
                    ·
                      rfl

theorem cell23_7312370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_7312370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312370 prefixEnd_7312370 := by exact prefixLift 7312370
  have htrace : WordTrace (prefixWord ++ tailWord_7312370) baseStart_7312370 baseEnd_7312370 := by
    simpa [prefixWord, tailWord_7312370, baseEnd_7312370] using wordTrace_append hprefix tailTrace_7312370
  have hstable : (prefixWord ++ tailWord_7312370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312370).length < 2 ^ (prefixWord ++ tailWord_7312370).sum := by decide
  have hdescent : baseEnd_7312370 < baseStart_7312370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312413 : List Nat := [1, 4, 2, 2, 4, 1, 2, 7]
def baseStart_7312413 : Nat := 118140960795 + 7312413 * 2 ^ 59
def prefixEnd_7312413 : Nat := 4983230072969 + 3 ^ 40 * 7312413 * 2
def baseEnd_7312413 : Nat := 139066022710585329044753

theorem tailTrace_7312413 : CollatzResearch.WordTrace tailWord_7312413 prefixEnd_7312413 139066022710585329044753 := by
  unfold tailWord_7312413
  simp only [CollatzResearch.WordTrace]
  refine ⟨266705612857384036558629893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177803741904922691039086595 266705612857384036558629893)
  ·
    refine ⟨50007302410759506854743105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266705612857384036558629893 50007302410759506854743105)
    ·
      refine ⟨37505476808069630141057329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50007302410759506854743105 37505476808069630141057329)
      ·
        refine ⟨28129107606052222605792997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37505476808069630141057329 28129107606052222605792997)
        ·
          refine ⟨5274207676134791738586187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28129107606052222605792997 5274207676134791738586187)
          ·
            refine ⟨7911311514202187607879281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5274207676134791738586187 7911311514202187607879281)
            ·
              refine ⟨5933483635651640705909461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7911311514202187607879281 5933483635651640705909461)
              ·
                refine ⟨139066022710585329044753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5933483635651640705909461 139066022710585329044753)
                ·
                  rfl

theorem cell23_7312413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 7].length) (baseStart_7312413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312413 prefixEnd_7312413 := by exact prefixLift 7312413
  have htrace : WordTrace (prefixWord ++ tailWord_7312413) baseStart_7312413 baseEnd_7312413 := by
    simpa [prefixWord, tailWord_7312413, baseEnd_7312413] using wordTrace_append hprefix tailTrace_7312413
  have hstable : (prefixWord ++ tailWord_7312413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312413).length < 2 ^ (prefixWord ++ tailWord_7312413).sum := by decide
  have hdescent : baseEnd_7312413 < baseStart_7312413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312423 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7312423 : Nat := 118140960795 + 7312423 * 2 ^ 59
def prefixEnd_7312423 : Nat := 4983230072969 + 3 ^ 40 * 7312423 * 2
def baseEnd_7312423 : Nat := 3754787747992348845083285

theorem tailTrace_7312423 : CollatzResearch.WordTrace tailWord_7312423 prefixEnd_7312423 3754787747992348845083285 := by
  unfold tailWord_7312423
  simp only [CollatzResearch.WordTrace]
  refine ⟨266705977587347808266493923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177803985058231872177662615 266705977587347808266493923)
  ·
    refine ⟨400058966381021712399740885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266705977587347808266493923 400058966381021712399740885)
    ·
      refine ⟨9376382024555196384368927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 400058966381021712399740885 9376382024555196384368927)
      ·
        refine ⟨14064573036832794576553391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9376382024555196384368927 14064573036832794576553391)
        ·
          refine ⟨21096859555249191864830087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14064573036832794576553391 21096859555249191864830087)
          ·
            refine ⟨31645289332873787797245131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21096859555249191864830087 31645289332873787797245131)
            ·
              refine ⟨47467933999310681695867697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31645289332873787797245131 47467933999310681695867697)
              ·
                refine ⟨35600950499483011271900773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47467933999310681695867697 35600950499483011271900773)
                ·
                  refine ⟨6675178218653064613481395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35600950499483011271900773 6675178218653064613481395)
                  ·
                    refine ⟨10012767327979596920222093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675178218653064613481395 10012767327979596920222093)
                    ·
                      refine ⟨3754787747992348845083285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10012767327979596920222093 3754787747992348845083285)
                      ·
                        rfl

theorem cell23_7312423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7312423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312423 prefixEnd_7312423 := by exact prefixLift 7312423
  have htrace : WordTrace (prefixWord ++ tailWord_7312423) baseStart_7312423 baseEnd_7312423 := by
    simpa [prefixWord, tailWord_7312423, baseEnd_7312423] using wordTrace_append hprefix tailTrace_7312423
  have hstable : (prefixWord ++ tailWord_7312423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312423).length < 2 ^ (prefixWord ++ tailWord_7312423).sum := by decide
  have hdescent : baseEnd_7312423 < baseStart_7312423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312509 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_7312509 : Nat := 118140960795 + 7312509 * 2 ^ 59
def prefixEnd_7312509 : Nat := 4983230072969 + 3 ^ 40 * 7312509 * 2
def baseEnd_7312509 : Nat := 3754831907328635508607889

theorem tailTrace_7312509 : CollatzResearch.WordTrace tailWord_7312509 prefixEnd_7312509 3754831907328635508607889 := by
  unfold tailWord_7312509
  simp only [CollatzResearch.WordTrace]
  refine ⟨266709114265036244954124581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177806076176690829969416387 266709114265036244954124581)
  ·
    refine ⟨50007958924694295928898359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266709114265036244954124581 50007958924694295928898359)
    ·
      refine ⟨75011938387041443893347539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50007958924694295928898359 75011938387041443893347539)
      ·
        refine ⟨112517907580562165840021309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75011938387041443893347539 112517907580562165840021309)
        ·
          refine ⟨42194215342710812190007991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112517907580562165840021309 42194215342710812190007991)
          ·
            refine ⟨63291323014066218285011987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42194215342710812190007991 63291323014066218285011987)
            ·
              refine ⟨94936984521099327427517981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63291323014066218285011987 94936984521099327427517981)
              ·
                refine ⟨35601369195412247785319243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94936984521099327427517981 35601369195412247785319243)
                ·
                  refine ⟨53402053793118371677978865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35601369195412247785319243 53402053793118371677978865)
                  ·
                    refine ⟨40051540344838778758484149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53402053793118371677978865 40051540344838778758484149)
                    ·
                      refine ⟨3754831907328635508607889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40051540344838778758484149 3754831907328635508607889)
                      ·
                        rfl

theorem cell23_7312509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_7312509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312509 prefixEnd_7312509 := by exact prefixLift 7312509
  have htrace : WordTrace (prefixWord ++ tailWord_7312509) baseStart_7312509 baseEnd_7312509 := by
    simpa [prefixWord, tailWord_7312509, baseEnd_7312509] using wordTrace_append hprefix tailTrace_7312509
  have hstable : (prefixWord ++ tailWord_7312509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312509).length < 2 ^ (prefixWord ++ tailWord_7312509).sum := by decide
  have hdescent : baseEnd_7312509 < baseStart_7312509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312519 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_7312519 : Nat := 118140960795 + 7312519 * 2 ^ 59
def prefixEnd_7312519 : Nat := 4983230072969 + 3 ^ 40 * 7312519 * 2
def baseEnd_7312519 : Nat := 3754837042135180469482843

theorem tailTrace_7312519 : CollatzResearch.WordTrace tailWord_7312519 prefixEnd_7312519 3754837042135180469482843 := by
  unfold tailWord_7312519
  simp only [CollatzResearch.WordTrace]
  refine ⟨266709478995000016661988611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177806319330000011107992407 266709478995000016661988611)
  ·
    refine ⟨400064218492500024992982917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266709478995000016661988611 400064218492500024992982917)
    ·
      refine ⟨75012040967343754686184297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400064218492500024992982917 75012040967343754686184297)
      ·
        refine ⟨56259030725507816014638223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75012040967343754686184297 56259030725507816014638223)
        ·
          refine ⟨84388546088261724021957335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56259030725507816014638223 84388546088261724021957335)
          ·
            refine ⟨126582819132392586032936003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84388546088261724021957335 126582819132392586032936003)
            ·
              refine ⟨189874228698588879049404005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126582819132392586032936003 189874228698588879049404005)
              ·
                refine ⟨35601417880985414821763251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189874228698588879049404005 35601417880985414821763251)
                ·
                  refine ⟨53402126821478122232644877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35601417880985414821763251 53402126821478122232644877)
                  ·
                    refine ⟨20025797558054295837241829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53402126821478122232644877 20025797558054295837241829)
                    ·
                      refine ⟨3754837042135180469482843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20025797558054295837241829 3754837042135180469482843)
                      ·
                        rfl

theorem cell23_7312519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_7312519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312519 prefixEnd_7312519 := by exact prefixLift 7312519
  have htrace : WordTrace (prefixWord ++ tailWord_7312519) baseStart_7312519 baseEnd_7312519 := by
    simpa [prefixWord, tailWord_7312519, baseEnd_7312519] using wordTrace_append hprefix tailTrace_7312519
  have hstable : (prefixWord ++ tailWord_7312519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312519).length < 2 ^ (prefixWord ++ tailWord_7312519).sum := by decide
  have hdescent : baseEnd_7312519 < baseStart_7312519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312536 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7312536 : Nat := 118140960795 + 7312536 * 2 ^ 59
def prefixEnd_7312536 : Nat := 4983230072969 + 3 ^ 40 * 7312536 * 2
def baseEnd_7312536 : Nat := 3754845771306306902970265

theorem tailTrace_7312536 : CollatzResearch.WordTrace tailWord_7312536 prefixEnd_7312536 3754845771306306902970265 := by
  unfold tailWord_7312536
  simp only [CollatzResearch.WordTrace]
  refine ⟨133355049517969214282678731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177806732690625619043571641 133355049517969214282678731)
  ·
    refine ⟨200032574276953821424018097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133355049517969214282678731 200032574276953821424018097)
    ·
      refine ⟨150024430707715366068013573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200032574276953821424018097 150024430707715366068013573)
      ·
        refine ⟨28129580757696631137752545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150024430707715366068013573 28129580757696631137752545)
        ·
          refine ⟨21097185568272473353314409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28129580757696631137752545 21097185568272473353314409)
          ·
            refine ⟨15822889176204355014985807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21097185568272473353314409 15822889176204355014985807)
            ·
              refine ⟨23734333764306532522478711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15822889176204355014985807 23734333764306532522478711)
              ·
                refine ⟨35601500646459798783718067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23734333764306532522478711 35601500646459798783718067)
                ·
                  refine ⟨53402250969689698175577101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35601500646459798783718067 53402250969689698175577101)
                  ·
                    refine ⟨20025844113633636815841413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53402250969689698175577101 20025844113633636815841413)
                    ·
                      refine ⟨3754845771306306902970265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20025844113633636815841413 3754845771306306902970265)
                      ·
                        rfl

theorem cell23_7312536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7312536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312536 prefixEnd_7312536 := by exact prefixLift 7312536
  have htrace : WordTrace (prefixWord ++ tailWord_7312536) baseStart_7312536 baseEnd_7312536 := by
    simpa [prefixWord, tailWord_7312536, baseEnd_7312536] using wordTrace_append hprefix tailTrace_7312536
  have hstable : (prefixWord ++ tailWord_7312536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312536).length < 2 ^ (prefixWord ++ tailWord_7312536).sum := by decide
  have hdescent : baseEnd_7312536 < baseStart_7312536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312549 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_7312549 : Nat := 118140960795 + 7312549 * 2 ^ 59
def prefixEnd_7312549 : Nat := 4983230072969 + 3 ^ 40 * 7312549 * 2
def baseEnd_7312549 : Nat := 3754852446554815352107705

theorem tailTrace_7312549 : CollatzResearch.WordTrace tailWord_7312549 prefixEnd_7312549 3754852446554815352107705 := by
  unfold tailWord_7312549
  simp only [CollatzResearch.WordTrace]
  refine ⟨266710573184891331785580701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177807048789927554523720467 266710573184891331785580701)
  ·
    refine ⟨100016464944334249419592763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266710573184891331785580701 100016464944334249419592763)
    ·
      refine ⟨150024697416501374129389145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100016464944334249419592763 150024697416501374129389145)
      ·
        refine ⟨112518523062376030597041859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150024697416501374129389145 112518523062376030597041859)
        ·
          refine ⟨168777784593564045895562789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112518523062376030597041859 168777784593564045895562789)
          ·
            refine ⟨31645834611293258605418023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168777784593564045895562789 31645834611293258605418023)
            ·
              refine ⟨47468751916939887908127035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31645834611293258605418023 47468751916939887908127035)
              ·
                refine ⟨71203127875409831862190553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47468751916939887908127035 71203127875409831862190553)
                ·
                  refine ⟨53402345906557373896642915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71203127875409831862190553 53402345906557373896642915)
                  ·
                    refine ⟨80103518859836060844964373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53402345906557373896642915 80103518859836060844964373)
                    ·
                      refine ⟨3754852446554815352107705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80103518859836060844964373 3754852446554815352107705)
                      ·
                        rfl

theorem cell23_7312549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_7312549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312549 prefixEnd_7312549 := by exact prefixLift 7312549
  have htrace : WordTrace (prefixWord ++ tailWord_7312549) baseStart_7312549 baseEnd_7312549 := by
    simpa [prefixWord, tailWord_7312549, baseEnd_7312549] using wordTrace_append hprefix tailTrace_7312549
  have hstable : (prefixWord ++ tailWord_7312549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312549).length < 2 ^ (prefixWord ++ tailWord_7312549).sum := by decide
  have hdescent : baseEnd_7312549 < baseStart_7312549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312563 : List Nat := [1, 1, 1, 2, 3, 2, 4, 4, 1, 4]
def baseStart_7312563 : Nat := 118140960795 + 7312563 * 2 ^ 59
def prefixEnd_7312563 : Nat := 4983230072969 + 3 ^ 40 * 7312563 * 2
def baseEnd_7312563 : Nat := 1251619878427992765777547

theorem tailTrace_7312563 : CollatzResearch.WordTrace tailWord_7312563 prefixEnd_7312563 1251619878427992765777547 := by
  unfold tailWord_7312563
  simp only [CollatzResearch.WordTrace]
  refine ⟨266711083806840612176590343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177807389204560408117726895 266711083806840612176590343)
  ·
    refine ⟨400066625710260918264885515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266711083806840612176590343 400066625710260918264885515)
    ·
      refine ⟨600099938565391377397328273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400066625710260918264885515 600099938565391377397328273)
      ·
        refine ⟨450074953924043533047996205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600099938565391377397328273 450074953924043533047996205)
        ·
          refine ⟨168778107721516324892998577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450074953924043533047996205 168778107721516324892998577)
          ·
            refine ⟨126583580791137243669748933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168778107721516324892998577 126583580791137243669748933)
            ·
              refine ⟨23734421398338233188077925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126583580791137243669748933 23734421398338233188077925)
              ·
                refine ⟨4450204012188418722764611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23734421398338233188077925 4450204012188418722764611)
                ·
                  refine ⟨6675306018282628084146917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450204012188418722764611 6675306018282628084146917)
                  ·
                    refine ⟨1251619878427992765777547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6675306018282628084146917 1251619878427992765777547)
                    ·
                      rfl

theorem cell23_7312563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 4].length) (baseStart_7312563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312563 prefixEnd_7312563 := by exact prefixLift 7312563
  have htrace : WordTrace (prefixWord ++ tailWord_7312563) baseStart_7312563 baseEnd_7312563 := by
    simpa [prefixWord, tailWord_7312563, baseEnd_7312563] using wordTrace_append hprefix tailTrace_7312563
  have hstable : (prefixWord ++ tailWord_7312563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312563).length < 2 ^ (prefixWord ++ tailWord_7312563).sum := by decide
  have hdescent : baseEnd_7312563 < baseStart_7312563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312597 : List Nat := [1, 3, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_7312597 : Nat := 118140960795 + 7312597 * 2 ^ 59
def prefixEnd_7312597 : Nat := 4983230072969 + 3 ^ 40 * 7312597 * 2
def baseEnd_7312597 : Nat := 1251625697875410388102495

theorem tailTrace_7312597 : CollatzResearch.WordTrace tailWord_7312597 prefixEnd_7312597 1251625697875410388102495 := by
  unfold tailWord_7312597
  simp only [CollatzResearch.WordTrace]
  refine ⟨266712323888717435983328045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177808215925811623988885363 266712323888717435983328045)
  ·
    refine ⟨100017121458269038493748017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266712323888717435983328045 100017121458269038493748017)
    ·
      refine ⟨75012841093701778870311013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100017121458269038493748017 75012841093701778870311013)
      ·
        refine ⟨14064907705069083538183315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75012841093701778870311013 14064907705069083538183315)
        ·
          refine ⟨21097361557603625307274973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14064907705069083538183315 21097361557603625307274973)
          ·
            refine ⟨7911510584101359490228115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21097361557603625307274973 7911510584101359490228115)
            ·
              refine ⟨11867265876152039235342173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911510584101359490228115 11867265876152039235342173)
              ·
                refine ⟨4450224703557014713253315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11867265876152039235342173 4450224703557014713253315)
                ·
                  refine ⟨6675337055335522069879973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450224703557014713253315 6675337055335522069879973)
                  ·
                    refine ⟨1251625697875410388102495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6675337055335522069879973 1251625697875410388102495)
                    ·
                      rfl

theorem cell23_7312597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_7312597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312597 prefixEnd_7312597 := by exact prefixLift 7312597
  have htrace : WordTrace (prefixWord ++ tailWord_7312597) baseStart_7312597 baseEnd_7312597 := by
    simpa [prefixWord, tailWord_7312597, baseEnd_7312597] using wordTrace_append hprefix tailTrace_7312597
  have hstable : (prefixWord ++ tailWord_7312597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312597).length < 2 ^ (prefixWord ++ tailWord_7312597).sum := by decide
  have hdescent : baseEnd_7312597 < baseStart_7312597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312620 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_7312620 : Nat := 118140960795 + 7312620 * 2 ^ 59
def prefixEnd_7312620 : Nat := 4983230072969 + 3 ^ 40 * 7312620 * 2
def baseEnd_7312620 : Nat := 3754888903681284574319879

theorem tailTrace_7312620 : CollatzResearch.WordTrace tailWord_7312620 prefixEnd_7312620 3754888903681284574319879 := by
  unfold tailWord_7312620
  simp only [CollatzResearch.WordTrace]
  refine ⟨133356581383817055455707657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177808775178422740607610209 133356581383817055455707657)
  ·
    refine ⟨100017436037862791591780743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133356581383817055455707657 100017436037862791591780743)
    ·
      refine ⟨150026154056794187387671115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100017436037862791591780743 150026154056794187387671115)
      ·
        refine ⟨225039231085191281081506673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150026154056794187387671115 225039231085191281081506673)
        ·
          refine ⟨168779423313893460811130005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225039231085191281081506673 168779423313893460811130005)
          ·
            refine ⟨7911535467838755975521719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168779423313893460811130005 7911535467838755975521719)
            ·
              refine ⟨11867303201758133963282579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911535467838755975521719 11867303201758133963282579)
              ·
                refine ⟨17800954802637200944923869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11867303201758133963282579 17800954802637200944923869)
                ·
                  refine ⟨6675358050988950354346451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17800954802637200944923869 6675358050988950354346451)
                  ·
                    refine ⟨10013037076483425531519677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675358050988950354346451 10013037076483425531519677)
                    ·
                      refine ⟨3754888903681284574319879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013037076483425531519677 3754888903681284574319879)
                      ·
                        rfl

theorem cell23_7312620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_7312620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312620 prefixEnd_7312620 := by exact prefixLift 7312620
  have htrace : WordTrace (prefixWord ++ tailWord_7312620) baseStart_7312620 baseEnd_7312620 := by
    simpa [prefixWord, tailWord_7312620, baseEnd_7312620] using wordTrace_append hprefix tailTrace_7312620
  have hstable : (prefixWord ++ tailWord_7312620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312620).length < 2 ^ (prefixWord ++ tailWord_7312620).sum := by decide
  have hdescent : baseEnd_7312620 < baseStart_7312620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312643 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 4]
def baseStart_7312643 : Nat := 118140960795 + 7312643 * 2 ^ 59
def prefixEnd_7312643 : Nat := 4983230072969 + 3 ^ 40 * 7312643 * 2
def baseEnd_7312643 : Nat := 3754900713736337984332273

theorem tailTrace_7312643 : CollatzResearch.WordTrace tailWord_7312643 prefixEnd_7312643 3754900713736337984332273 := by
  unfold tailWord_7312643
  simp only [CollatzResearch.WordTrace]
  refine ⟨266714001646550785839502583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177809334431033857226335055 266714001646550785839502583)
  ·
    refine ⟨400071002469826178759253875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266714001646550785839502583 400071002469826178759253875)
    ·
      refine ⟨600106503704739268138880813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400071002469826178759253875 600106503704739268138880813)
      ·
        refine ⟨225039938889277225552080305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600106503704739268138880813 225039938889277225552080305)
        ·
          refine ⟨168779954166957919164060229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225039938889277225552080305 168779954166957919164060229)
          ·
            refine ⟨31646241406304609843261293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168779954166957919164060229 31646241406304609843261293)
            ·
              refine ⟨11867340527364228691222985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31646241406304609843261293 11867340527364228691222985)
              ·
                refine ⟨8900505395523171518417239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11867340527364228691222985 8900505395523171518417239)
                ·
                  refine ⟨13350758093284757277625859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8900505395523171518417239 13350758093284757277625859)
                  ·
                    refine ⟨20026137139927135916438789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13350758093284757277625859 20026137139927135916438789)
                    ·
                      refine ⟨3754900713736337984332273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20026137139927135916438789 3754900713736337984332273)
                      ·
                        rfl

theorem cell23_7312643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_7312643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312643 prefixEnd_7312643 := by exact prefixLift 7312643
  have htrace : WordTrace (prefixWord ++ tailWord_7312643) baseStart_7312643 baseEnd_7312643 := by
    simpa [prefixWord, tailWord_7312643, baseEnd_7312643] using wordTrace_append hprefix tailTrace_7312643
  have hstable : (prefixWord ++ tailWord_7312643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312643).length < 2 ^ (prefixWord ++ tailWord_7312643).sum := by decide
  have hdescent : baseEnd_7312643 < baseStart_7312643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312649 : List Nat := [1, 2, 1, 1, 3, 3, 1, 11]
def baseStart_7312649 : Nat := 118140960795 + 7312649 * 2 ^ 59
def prefixEnd_7312649 : Nat := 4983230072969 + 3 ^ 40 * 7312649 * 2
def baseEnd_7312649 : Nat := 139070510911861665216935

theorem tailTrace_7312649 : CollatzResearch.WordTrace tailWord_7312649 prefixEnd_7312649 139070510911861665216935 := by
  unfold tailWord_7312649
  simp only [CollatzResearch.WordTrace]
  refine ⟨266714220484529048864221001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177809480323019365909480667 266714220484529048864221001)
  ·
    refine ⟨200035665363396786648165751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266714220484529048864221001 200035665363396786648165751)
    ·
      refine ⟨300053498045095179972248627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200035665363396786648165751 300053498045095179972248627)
      ·
        refine ⟨450080247067642769958372941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300053498045095179972248627 450080247067642769958372941)
        ·
          refine ⟨168780092650366038734389853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450080247067642769958372941 168780092650366038734389853)
          ·
            refine ⟨63292534743887264525396195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168780092650366038734389853 63292534743887264525396195)
            ·
              refine ⟨94938802115830896788094293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63292534743887264525396195 94938802115830896788094293)
              ·
                refine ⟨139070510911861665216935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 94938802115830896788094293 139070510911861665216935)
                ·
                  rfl

theorem cell23_7312649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 11].length) (baseStart_7312649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312649 prefixEnd_7312649 := by exact prefixLift 7312649
  have htrace : WordTrace (prefixWord ++ tailWord_7312649) baseStart_7312649 baseEnd_7312649 := by
    simpa [prefixWord, tailWord_7312649, baseEnd_7312649] using wordTrace_append hprefix tailTrace_7312649
  have hstable : (prefixWord ++ tailWord_7312649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312649).length < 2 ^ (prefixWord ++ tailWord_7312649).sum := by decide
  have hdescent : baseEnd_7312649 < baseStart_7312649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312671 : List Nat := [1, 1, 2, 4, 5, 1, 2, 2, 1, 1, 3]
def baseStart_7312671 : Nat := 118140960795 + 7312671 * 2 ^ 59
def prefixEnd_7312671 : Nat := 4983230072969 + 3 ^ 40 * 7312671 * 2
def baseEnd_7312671 : Nat := 3754915091194663874782145

theorem tailTrace_7312671 : CollatzResearch.WordTrace tailWord_7312671 prefixEnd_7312671 3754915091194663874782145 := by
  unfold tailWord_7312671
  simp only [CollatzResearch.WordTrace]
  refine ⟨266715022890449346621521867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177810015260299564414347911 266715022890449346621521867)
  ·
    refine ⟨400072534335674019932282801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266715022890449346621521867 400072534335674019932282801)
    ·
      refine ⟨300054400751755514949212101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400072534335674019932282801 300054400751755514949212101)
      ·
        refine ⟨56260200140954159052977269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300054400751755514949212101 56260200140954159052977269)
        ·
          refine ⟨5274393763214452411216619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56260200140954159052977269 5274393763214452411216619)
          ·
            refine ⟨7911590644821678616824929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5274393763214452411216619 7911590644821678616824929)
            ·
              refine ⟨5933692983616258962618697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7911590644821678616824929 5933692983616258962618697)
              ·
                refine ⟨4450269737712194221964023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5933692983616258962618697 4450269737712194221964023)
                ·
                  refine ⟨6675404606568291332946035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450269737712194221964023 6675404606568291332946035)
                  ·
                    refine ⟨10013106909852436999419053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675404606568291332946035 10013106909852436999419053)
                    ·
                      refine ⟨3754915091194663874782145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013106909852436999419053 3754915091194663874782145)
                      ·
                        rfl

theorem cell23_7312671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_7312671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312671 prefixEnd_7312671 := by exact prefixLift 7312671
  have htrace : WordTrace (prefixWord ++ tailWord_7312671) baseStart_7312671 baseEnd_7312671 := by
    simpa [prefixWord, tailWord_7312671, baseEnd_7312671] using wordTrace_append hprefix tailTrace_7312671
  have hstable : (prefixWord ++ tailWord_7312671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312671).length < 2 ^ (prefixWord ++ tailWord_7312671).sum := by decide
  have hdescent : baseEnd_7312671 < baseStart_7312671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312693 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_7312693 : Nat := 118140960795 + 7312693 * 2 ^ 59
def prefixEnd_7312693 : Nat := 4983230072969 + 3 ^ 40 * 7312693 * 2
def baseEnd_7312693 : Nat := 3754926387769062788707043

theorem tailTrace_7312693 : CollatzResearch.WordTrace tailWord_7312693 prefixEnd_7312693 3754926387769062788707043 := by
  unfold tailWord_7312693
  simp only [CollatzResearch.WordTrace]
  refine ⟨266715825296369644378822733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177810550197579762919215155 266715825296369644378822733)
  ·
    refine ⟨100018434486138616642058525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266715825296369644378822733 100018434486138616642058525)
    ·
      refine ⟨37506912932301981240771947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100018434486138616642058525 37506912932301981240771947)
      ·
        refine ⟨56260369398452971861157921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37506912932301981240771947 56260369398452971861157921)
        ·
          refine ⟨42195277048839728895868441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56260369398452971861157921 42195277048839728895868441)
          ·
            refine ⟨31646457786629796671901331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42195277048839728895868441 31646457786629796671901331)
            ·
              refine ⟨47469686679944695007851997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31646457786629796671901331 47469686679944695007851997)
              ·
                refine ⟨17801132504979260627944499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47469686679944695007851997 17801132504979260627944499)
                ·
                  refine ⟨26701698757468890941916749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17801132504979260627944499 26701698757468890941916749)
                  ·
                    refine ⟨10013137034050834103218781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26701698757468890941916749 10013137034050834103218781)
                    ·
                      refine ⟨3754926387769062788707043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013137034050834103218781 3754926387769062788707043)
                      ·
                        rfl

theorem cell23_7312693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_7312693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312693 prefixEnd_7312693 := by exact prefixLift 7312693
  have htrace : WordTrace (prefixWord ++ tailWord_7312693) baseStart_7312693 baseEnd_7312693 := by
    simpa [prefixWord, tailWord_7312693, baseEnd_7312693] using wordTrace_append hprefix tailTrace_7312693
  have hstable : (prefixWord ++ tailWord_7312693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312693).length < 2 ^ (prefixWord ++ tailWord_7312693).sum := by decide
  have hdescent : baseEnd_7312693 < baseStart_7312693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312720 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 1, 3, 2]
def baseStart_7312720 : Nat := 118140960795 + 7312720 * 2 ^ 59
def prefixEnd_7312720 : Nat := 4983230072969 + 3 ^ 40 * 7312720 * 2
def baseEnd_7312720 : Nat := 3754940251746734183069419

theorem tailTrace_7312720 : CollatzResearch.WordTrace tailWord_7312720 prefixEnd_7312720 3754940251746734183069419 := by
  unfold tailWord_7312720
  simp only [CollatzResearch.WordTrace]
  refine ⟨133358405033635913995027807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177811206711514551993370409 133358405033635913995027807)
  ·
    refine ⟨200037607550453870992541711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133358405033635913995027807 200037607550453870992541711)
    ·
      refine ⟨300056411325680806488812567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200037607550453870992541711 300056411325680806488812567)
      ·
        refine ⟨450084616988521209733218851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300056411325680806488812567 450084616988521209733218851)
        ·
          refine ⟨675126925482781814599828277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450084616988521209733218851 675126925482781814599828277)
          ·
            refine ⟨63293149264010795118733901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 675126925482781814599828277 63293149264010795118733901)
            ·
              refine ⟨23734930974004048169525213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63293149264010795118733901 23734930974004048169525213)
              ·
                refine ⟨8900599115251518063571955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23734930974004048169525213 8900599115251518063571955)
                ·
                  refine ⟨13350898672877277095357933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8900599115251518063571955 13350898672877277095357933)
                  ·
                    refine ⟨5006587002328978910759225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13350898672877277095357933 5006587002328978910759225)
                    ·
                      refine ⟨3754940251746734183069419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5006587002328978910759225 3754940251746734183069419)
                      ·
                        rfl

theorem cell23_7312720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 3, 2].length) (baseStart_7312720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312720 prefixEnd_7312720 := by exact prefixLift 7312720
  have htrace : WordTrace (prefixWord ++ tailWord_7312720) baseStart_7312720 baseEnd_7312720 := by
    simpa [prefixWord, tailWord_7312720, baseEnd_7312720] using wordTrace_append hprefix tailTrace_7312720
  have hstable : (prefixWord ++ tailWord_7312720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312720).length < 2 ^ (prefixWord ++ tailWord_7312720).sum := by decide
  have hdescent : baseEnd_7312720 < baseStart_7312720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312727 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_7312727 : Nat := 118140960795 + 7312727 * 2 ^ 59
def prefixEnd_7312727 : Nat := 4983230072969 + 3 ^ 40 * 7312727 * 2
def baseEnd_7312727 : Nat := 3754943846111315655681887

theorem tailTrace_7312727 : CollatzResearch.WordTrace tailWord_7312727 prefixEnd_7312727 3754943846111315655681887 := by
  unfold tailWord_7312727
  simp only [CollatzResearch.WordTrace]
  refine ⟨266717065378246468185560435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177811376918830978790373623 266717065378246468185560435)
  ·
    refine ⟨400075598067369702278340653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266717065378246468185560435 400075598067369702278340653)
    ·
      refine ⟨150028349275263638354377745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400075598067369702278340653 150028349275263638354377745)
      ·
        refine ⟨112521261956447728765783309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150028349275263638354377745 112521261956447728765783309)
        ·
          refine ⟨42195473233667898287168741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112521261956447728765783309 42195473233667898287168741)
          ·
            refine ⟨7911651231312730928844139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42195473233667898287168741 7911651231312730928844139)
            ·
              refine ⟨11867476846969096393266209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911651231312730928844139 11867476846969096393266209)
              ·
                refine ⟨8900607635226822294949657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11867476846969096393266209 8900607635226822294949657)
                ·
                  refine ⟨6675455726420116721212243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8900607635226822294949657 6675455726420116721212243)
                  ·
                    refine ⟨10013183589630175081818365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675455726420116721212243 10013183589630175081818365)
                    ·
                      refine ⟨3754943846111315655681887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013183589630175081818365 3754943846111315655681887)
                      ·
                        rfl

theorem cell23_7312727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_7312727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312727 prefixEnd_7312727 := by exact prefixLift 7312727
  have htrace : WordTrace (prefixWord ++ tailWord_7312727) baseStart_7312727 baseEnd_7312727 := by
    simpa [prefixWord, tailWord_7312727, baseEnd_7312727] using wordTrace_append hprefix tailTrace_7312727
  have hstable : (prefixWord ++ tailWord_7312727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312727).length < 2 ^ (prefixWord ++ tailWord_7312727).sum := by decide
  have hdescent : baseEnd_7312727 < baseStart_7312727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312744 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_7312744 : Nat := 118140960795 + 7312744 * 2 ^ 59
def prefixEnd_7312744 : Nat := 4983230072969 + 3 ^ 40 * 7312744 * 2
def baseEnd_7312744 : Nat := 3754952575282442089169309

theorem tailTrace_7312744 : CollatzResearch.WordTrace tailWord_7312744 prefixEnd_7312744 3754952575282442089169309 := by
  unfold tailWord_7312744
  simp only [CollatzResearch.WordTrace]
  refine ⟨133358842709592440044464643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177811790279456586725952857 133358842709592440044464643)
  ·
    refine ⟨200038264064388660066696965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133358842709592440044464643 200038264064388660066696965)
    ·
      refine ⟨37507174512072873762505681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200038264064388660066696965 37507174512072873762505681)
      ·
        refine ⟨28130380884054655321879261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37507174512072873762505681 28130380884054655321879261)
        ·
          refine ⟨10548892831520495745704723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28130380884054655321879261 10548892831520495745704723)
          ·
            refine ⟨15823339247280743618557085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10548892831520495745704723 15823339247280743618557085)
            ·
              refine ⟨5933752217730278856958907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15823339247280743618557085 5933752217730278856958907)
              ·
                refine ⟨8900628326595418285438361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5933752217730278856958907 8900628326595418285438361)
                ·
                  refine ⟨6675471244946563714078771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8900628326595418285438361 6675471244946563714078771)
                  ·
                    refine ⟨10013206867419845571118157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675471244946563714078771 10013206867419845571118157)
                    ·
                      refine ⟨3754952575282442089169309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013206867419845571118157 3754952575282442089169309)
                      ·
                        rfl

theorem cell23_7312744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_7312744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312744 prefixEnd_7312744 := by exact prefixLift 7312744
  have htrace : WordTrace (prefixWord ++ tailWord_7312744) baseStart_7312744 baseEnd_7312744 := by
    simpa [prefixWord, tailWord_7312744, baseEnd_7312744] using wordTrace_append hprefix tailTrace_7312744
  have hstable : (prefixWord ++ tailWord_7312744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312744).length < 2 ^ (prefixWord ++ tailWord_7312744).sum := by decide
  have hdescent : baseEnd_7312744 < baseStart_7312744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312770 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7312770 : Nat := 118140960795 + 7312770 * 2 ^ 59
def prefixEnd_7312770 : Nat := 4983230072969 + 3 ^ 40 * 7312770 * 2
def baseEnd_7312770 : Nat := 3754965925779458987444189

theorem tailTrace_7312770 : CollatzResearch.WordTrace tailWord_7312770 prefixEnd_7312770 3754965925779458987444189 := by
  unfold tailWord_7312770
  simp only [CollatzResearch.WordTrace]
  refine ⟨66679658429272671632343941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177812422478060457686250509 66679658429272671632343941)
  ·
    refine ⟨12502435955488625931064489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66679658429272671632343941 12502435955488625931064489)
    ·
      refine ⟨9376826966616469448298367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12502435955488625931064489 9376826966616469448298367)
      ·
        refine ⟨14065240449924704172447551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9376826966616469448298367 14065240449924704172447551)
        ·
          refine ⟨21097860674887056258671327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14065240449924704172447551 21097860674887056258671327)
          ·
            refine ⟨31646791012330584388006991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21097860674887056258671327 31646791012330584388006991)
            ·
              refine ⟨47470186518495876582010487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31646791012330584388006991 47470186518495876582010487)
              ·
                refine ⟨71205279777743814873015731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47470186518495876582010487 71205279777743814873015731)
                ·
                  refine ⟨106807919666615722309523597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71205279777743814873015731 106807919666615722309523597)
                  ·
                    refine ⟨40052969874980895866071349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106807919666615722309523597 40052969874980895866071349)
                    ·
                      refine ⟨3754965925779458987444189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40052969874980895866071349 3754965925779458987444189)
                      ·
                        rfl

theorem cell23_7312770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7312770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312770 prefixEnd_7312770 := by exact prefixLift 7312770
  have htrace : WordTrace (prefixWord ++ tailWord_7312770) baseStart_7312770 baseEnd_7312770 := by
    simpa [prefixWord, tailWord_7312770, baseEnd_7312770] using wordTrace_append hprefix tailTrace_7312770
  have hstable : (prefixWord ++ tailWord_7312770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312770).length < 2 ^ (prefixWord ++ tailWord_7312770).sum := by decide
  have hdescent : baseEnd_7312770 < baseStart_7312770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312826 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_7312826 : Nat := 118140960795 + 7312826 * 2 ^ 59
def prefixEnd_7312826 : Nat := 4983230072969 + 3 ^ 40 * 7312826 * 2
def baseEnd_7312826 : Nat := 3754994680696110768343931

theorem tailTrace_7312826 : CollatzResearch.WordTrace tailWord_7312826 prefixEnd_7312826 3754994680696110768343931 := by
  unfold tailWord_7312826
  simp only [CollatzResearch.WordTrace]
  refine ⟨66680169051221952023353583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177813784136591872062276221 66680169051221952023353583)
  ·
    refine ⟨100020253576832928035030375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66680169051221952023353583 100020253576832928035030375)
    ·
      refine ⟨150030380365249392052545563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100020253576832928035030375 150030380365249392052545563)
      ·
        refine ⟨225045570547874088078818345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150030380365249392052545563 225045570547874088078818345)
        ·
          refine ⟨168784177910905566059113759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225045570547874088078818345 168784177910905566059113759)
          ·
            refine ⟨253176266866358349088670639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168784177910905566059113759 253176266866358349088670639)
            ·
              refine ⟨379764400299537523633005959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253176266866358349088670639 379764400299537523633005959)
              ·
                refine ⟨569646600449306285449508939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379764400299537523633005959 569646600449306285449508939)
                ·
                  refine ⟨854469900673959428174263409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569646600449306285449508939 854469900673959428174263409)
                  ·
                    refine ⟨640852425505469571130697557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 854469900673959428174263409 640852425505469571130697557)
                    ·
                      refine ⟨3754994680696110768343931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 640852425505469571130697557 3754994680696110768343931)
                      ·
                        rfl

theorem cell23_7312826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_7312826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312826 prefixEnd_7312826 := by exact prefixLift 7312826
  have htrace : WordTrace (prefixWord ++ tailWord_7312826) baseStart_7312826 baseEnd_7312826 := by
    simpa [prefixWord, tailWord_7312826, baseEnd_7312826] using wordTrace_append hprefix tailTrace_7312826
  have hstable : (prefixWord ++ tailWord_7312826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312826).length < 2 ^ (prefixWord ++ tailWord_7312826).sum := by decide
  have hdescent : baseEnd_7312826 < baseStart_7312826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312840 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_7312840 : Nat := 118140960795 + 7312840 * 2 ^ 59
def prefixEnd_7312840 : Nat := 4983230072969 + 3 ^ 40 * 7312840 * 2
def baseEnd_7312840 : Nat := 3755001869425273713568867

theorem tailTrace_7312840 : CollatzResearch.WordTrace tailWord_7312840 prefixEnd_7312840 3755001869425273713568867 := by
  unfold tailWord_7312840
  simp only [CollatzResearch.WordTrace]
  refine ⟨133360593413418544242211987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177814124551224725656282649 133360593413418544242211987)
  ·
    refine ⟨200040890120127816363317981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133360593413418544242211987 200040890120127816363317981)
    ·
      refine ⟨75015333795047931136244243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200040890120127816363317981 75015333795047931136244243)
      ·
        refine ⟨112523000692571896704366365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75015333795047931136244243 112523000692571896704366365)
        ·
          refine ⟨42196125259714461264137387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112523000692571896704366365 42196125259714461264137387)
          ·
            refine ⟨63294187889571691896206081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42196125259714461264137387 63294187889571691896206081)
            ·
              refine ⟨47470640917178768922154561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63294187889571691896206081 47470640917178768922154561)
              ·
                refine ⟨35602980687884076691615921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47470640917178768922154561 35602980687884076691615921)
                ·
                  refine ⟨26702235515913057518711941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35602980687884076691615921 26702235515913057518711941)
                  ·
                    refine ⟨5006669159233698284758489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26702235515913057518711941 5006669159233698284758489)
                    ·
                      refine ⟨3755001869425273713568867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5006669159233698284758489 3755001869425273713568867)
                      ·
                        rfl

theorem cell23_7312840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_7312840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312840 prefixEnd_7312840 := by exact prefixLift 7312840
  have htrace : WordTrace (prefixWord ++ tailWord_7312840) baseStart_7312840 baseEnd_7312840 := by
    simpa [prefixWord, tailWord_7312840, baseEnd_7312840] using wordTrace_append hprefix tailTrace_7312840
  have hstable : (prefixWord ++ tailWord_7312840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312840).length < 2 ^ (prefixWord ++ tailWord_7312840).sum := by decide
  have hdescent : baseEnd_7312840 < baseStart_7312840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312863 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 6]
def baseStart_7312863 : Nat := 118140960795 + 7312863 * 2 ^ 59
def prefixEnd_7312863 : Nat := 4983230072969 + 3 ^ 40 * 7312863 * 2
def baseEnd_7312863 : Nat := 417223742164480791509029

theorem tailTrace_7312863 : CollatzResearch.WordTrace tailWord_7312863 prefixEnd_7312863 417223742164480791509029 := by
  unfold tailWord_7312863
  simp only [CollatzResearch.WordTrace]
  refine ⟨266722025705753763412511243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177814683803835842275007495 266722025705753763412511243)
  ·
    refine ⟨400083038558630645118766865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266722025705753763412511243 400083038558630645118766865)
    ·
      refine ⟨300062278918972983839075149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400083038558630645118766865 300062278918972983839075149)
      ·
        refine ⟨112523354594614868939653181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300062278918972983839075149 112523354594614868939653181)
        ·
          refine ⟨42196257972980575852369943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112523354594614868939653181 42196257972980575852369943)
          ·
            refine ⟨63294386959470863778554915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42196257972980575852369943 63294386959470863778554915)
            ·
              refine ⟨94941580439206295667832373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63294386959470863778554915 94941580439206295667832373)
              ·
                refine ⟨8900773166175590218859285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94941580439206295667832373 8900773166175590218859285)
                ·
                  refine ⟨417223742164480791509029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8900773166175590218859285 417223742164480791509029)
                  ·
                    rfl

theorem cell23_7312863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 6].length) (baseStart_7312863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312863 prefixEnd_7312863 := by exact prefixLift 7312863
  have htrace : WordTrace (prefixWord ++ tailWord_7312863) baseStart_7312863 baseEnd_7312863 := by
    simpa [prefixWord, tailWord_7312863, baseEnd_7312863] using wordTrace_append hprefix tailTrace_7312863
  have hstable : (prefixWord ++ tailWord_7312863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312863).length < 2 ^ (prefixWord ++ tailWord_7312863).sum := by decide
  have hdescent : baseEnd_7312863 < baseStart_7312863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312874 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_7312874 : Nat := 118140960795 + 7312874 * 2 ^ 59
def prefixEnd_7312874 : Nat := 4983230072969 + 3 ^ 40 * 7312874 * 2
def baseEnd_7312874 : Nat := 3755019327767526580543711

theorem tailTrace_7312874 : CollatzResearch.WordTrace tailWord_7312874 prefixEnd_7312874 3755019327767526580543711 := by
  unfold tailWord_7312874
  simp only [CollatzResearch.WordTrace]
  refine ⟨66680606727178478072790419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177814951272475941527441117 66680606727178478072790419)
  ·
    refine ⟨100020910090767717109185629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66680606727178478072790419 100020910090767717109185629)
    ·
      refine ⟨37507841284037893915944611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100020910090767717109185629 37507841284037893915944611)
      ·
        refine ⟨56261761926056840873916917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37507841284037893915944611 56261761926056840873916917)
        ·
          refine ⟨5274540180567828831929711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56261761926056840873916917 5274540180567828831929711)
          ·
            refine ⟨7911810270851743247894567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5274540180567828831929711 7911810270851743247894567)
            ·
              refine ⟨11867715406277614871841851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911810270851743247894567 11867715406277614871841851)
              ·
                refine ⟨17801573109416422307762777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11867715406277614871841851 17801573109416422307762777)
                ·
                  refine ⟨13351179832062316730822083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17801573109416422307762777 13351179832062316730822083)
                  ·
                    refine ⟨20026769748093475096233125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13351179832062316730822083 20026769748093475096233125)
                    ·
                      refine ⟨3755019327767526580543711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20026769748093475096233125 3755019327767526580543711)
                      ·
                        rfl

theorem cell23_7312874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_7312874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312874 prefixEnd_7312874 := by exact prefixLift 7312874
  have htrace : WordTrace (prefixWord ++ tailWord_7312874) baseStart_7312874 baseEnd_7312874 := by
    simpa [prefixWord, tailWord_7312874, baseEnd_7312874] using wordTrace_append hprefix tailTrace_7312874
  have hstable : (prefixWord ++ tailWord_7312874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312874).length < 2 ^ (prefixWord ++ tailWord_7312874).sum := by decide
  have hdescent : baseEnd_7312874 < baseStart_7312874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312877 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7312877 : Nat := 118140960795 + 7312877 * 2 ^ 59
def prefixEnd_7312877 : Nat := 4983230072969 + 3 ^ 40 * 7312877 * 2
def baseEnd_7312877 : Nat := 3755020868209490068806197

theorem tailTrace_7312877 : CollatzResearch.WordTrace tailWord_7312877 prefixEnd_7312877 3755020868209490068806197 := by
  unfold tailWord_7312877
  simp only [CollatzResearch.WordTrace]
  refine ⟨266722536327703043803520885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177815024218468695869013923 266722536327703043803520885)
  ·
    refine ⟨25005237780722160356580083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266722536327703043803520885 25005237780722160356580083)
    ·
      refine ⟨37507856671083240534870125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25005237780722160356580083 37507856671083240534870125)
      ·
        refine ⟨14065446251656215200576297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37507856671083240534870125 14065446251656215200576297)
        ·
          refine ⟨10549084688742161400432223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14065446251656215200576297 10549084688742161400432223)
          ·
            refine ⟨15823627033113242100648335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549084688742161400432223 15823627033113242100648335)
            ·
              refine ⟨23735440549669863150972503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15823627033113242100648335 23735440549669863150972503)
              ·
                refine ⟨35603160824504794726458755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23735440549669863150972503 35603160824504794726458755)
                ·
                  refine ⟨53404741236757192089688133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35603160824504794726458755 53404741236757192089688133)
                  ·
                    refine ⟨10013388981891973516816525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53404741236757192089688133 10013388981891973516816525)
                    ·
                      refine ⟨3755020868209490068806197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013388981891973516816525 3755020868209490068806197)
                      ·
                        rfl

theorem cell23_7312877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7312877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312877 prefixEnd_7312877 := by exact prefixLift 7312877
  have htrace : WordTrace (prefixWord ++ tailWord_7312877) baseStart_7312877 baseEnd_7312877 := by
    simpa [prefixWord, tailWord_7312877, baseEnd_7312877] using wordTrace_append hprefix tailTrace_7312877
  have hstable : (prefixWord ++ tailWord_7312877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312877).length < 2 ^ (prefixWord ++ tailWord_7312877).sum := by decide
  have hdescent : baseEnd_7312877 < baseStart_7312877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312890 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_7312890 : Nat := 118140960795 + 7312890 * 2 ^ 59
def prefixEnd_7312890 : Nat := 4983230072969 + 3 ^ 40 * 7312890 * 2
def baseEnd_7312890 : Nat := 3755027543457998517943637

theorem tailTrace_7312890 : CollatzResearch.WordTrace tailWord_7312890 prefixEnd_7312890 3755027543457998517943637 := by
  unfold tailWord_7312890
  simp only [CollatzResearch.WordTrace]
  refine ⟨66680752619163986755936031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177815340317770631349162749 66680752619163986755936031)
  ·
    refine ⟨100021128928745980133904047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66680752619163986755936031 100021128928745980133904047)
    ·
      refine ⟨150031693393118970200856071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100021128928745980133904047 150031693393118970200856071)
      ·
        refine ⟨225047540089678455301284107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150031693393118970200856071 225047540089678455301284107)
        ·
          refine ⟨337571310134517682951926161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225047540089678455301284107 337571310134517682951926161)
          ·
            refine ⟨253178482600888262213944621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337571310134517682951926161 253178482600888262213944621)
            ·
              refine ⟨94941930975333098330229233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253178482600888262213944621 94941930975333098330229233)
              ·
                refine ⟨71206448231499823747671925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94941930975333098330229233 71206448231499823747671925)
                ·
                  refine ⟨6675604521703108476344243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71206448231499823747671925 6675604521703108476344243)
                  ·
                    refine ⟨10013406782554662714516365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675604521703108476344243 10013406782554662714516365)
                    ·
                      refine ⟨3755027543457998517943637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013406782554662714516365 3755027543457998517943637)
                      ·
                        rfl

theorem cell23_7312890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_7312890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312890 prefixEnd_7312890 := by exact prefixLift 7312890
  have htrace : WordTrace (prefixWord ++ tailWord_7312890) baseStart_7312890 baseEnd_7312890 := by
    simpa [prefixWord, tailWord_7312890, baseEnd_7312890] using wordTrace_append hprefix tailTrace_7312890
  have hstable : (prefixWord ++ tailWord_7312890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312890).length < 2 ^ (prefixWord ++ tailWord_7312890).sum := by decide
  have hdescent : baseEnd_7312890 < baseStart_7312890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312897 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 6]
def baseStart_7312897 : Nat := 118140960795 + 7312897 * 2 ^ 59
def prefixEnd_7312897 : Nat := 4983230072969 + 3 ^ 40 * 7312897 * 2
def baseEnd_7312897 : Nat := 417225681980286665617345

theorem tailTrace_7312897 : CollatzResearch.WordTrace tailWord_7312897 prefixEnd_7312897 417225681980286665617345 := by
  unfold tailWord_7312897
  simp only [CollatzResearch.WordTrace]
  refine ⟨266723265787630587219248945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177815510525087058146165963 266723265787630587219248945)
  ·
    refine ⟨200042449340722940414436709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266723265787630587219248945 200042449340722940414436709)
    ·
      refine ⟨37507959251385551327706883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200042449340722940414436709 37507959251385551327706883)
      ·
        refine ⟨56261938877078326991560325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37507959251385551327706883 56261938877078326991560325)
        ·
          refine ⟨10549113539452186310917561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56261938877078326991560325 10549113539452186310917561)
          ·
            refine ⟨7911835154589139733188171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10549113539452186310917561 7911835154589139733188171)
            ·
              refine ⟨11867752731883709599782257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911835154589139733188171 11867752731883709599782257)
              ·
                refine ⟨8900814548912782199836693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11867752731883709599782257 8900814548912782199836693)
                ·
                  refine ⟨417225681980286665617345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8900814548912782199836693 417225681980286665617345)
                  ·
                    rfl

theorem cell23_7312897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 6].length) (baseStart_7312897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312897 prefixEnd_7312897 := by exact prefixLift 7312897
  have htrace : WordTrace (prefixWord ++ tailWord_7312897) baseStart_7312897 baseEnd_7312897 := by
    simpa [prefixWord, tailWord_7312897, baseEnd_7312897] using wordTrace_append hprefix tailTrace_7312897
  have hstable : (prefixWord ++ tailWord_7312897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312897).length < 2 ^ (prefixWord ++ tailWord_7312897).sum := by decide
  have hdescent : baseEnd_7312897 < baseStart_7312897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312930 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_7312930 : Nat := 118140960795 + 7312930 * 2 ^ 59
def prefixEnd_7312930 : Nat := 4983230072969 + 3 ^ 40 * 7312930 * 2
def baseEnd_7312930 : Nat := 3755048082684178361443453

theorem tailTrace_7312930 : CollatzResearch.WordTrace tailWord_7312930 prefixEnd_7312930 3755048082684178361443453 := by
  unfold tailWord_7312930
  simp only [CollatzResearch.WordTrace]
  refine ⟨66681117349127758463800061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177816312931007355903466829 66681117349127758463800061)
  ·
    refine ⟨25005419005922909423925023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66681117349127758463800061 25005419005922909423925023)
    ·
      refine ⟨37508128508884364135887535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25005419005922909423925023 37508128508884364135887535)
      ·
        refine ⟨56262192763326546203831303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37508128508884364135887535 56262192763326546203831303)
        ·
          refine ⟨84393289144989819305746955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56262192763326546203831303 84393289144989819305746955)
          ·
            refine ⟨126589933717484728958620433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84393289144989819305746955 126589933717484728958620433)
            ·
              refine ⟨94942450288113546718965325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126589933717484728958620433 94942450288113546718965325)
              ·
                refine ⟨35603418858042580019611997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94942450288113546718965325 35603418858042580019611997)
                ·
                  refine ⟨13351282071765967507354499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35603418858042580019611997 13351282071765967507354499)
                  ·
                    refine ⟨20026923107648951261031749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13351282071765967507354499 20026923107648951261031749)
                    ·
                      refine ⟨3755048082684178361443453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20026923107648951261031749 3755048082684178361443453)
                      ·
                        rfl

theorem cell23_7312930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_7312930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312930 prefixEnd_7312930 := by exact prefixLift 7312930
  have htrace : WordTrace (prefixWord ++ tailWord_7312930) baseStart_7312930 baseEnd_7312930 := by
    simpa [prefixWord, tailWord_7312930, baseEnd_7312930] using wordTrace_append hprefix tailTrace_7312930
  have hstable : (prefixWord ++ tailWord_7312930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312930).length < 2 ^ (prefixWord ++ tailWord_7312930).sum := by decide
  have hdescent : baseEnd_7312930 < baseStart_7312930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312933 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_7312933 : Nat := 118140960795 + 7312933 * 2 ^ 59
def prefixEnd_7312933 : Nat := 4983230072969 + 3 ^ 40 * 7312933 * 2
def baseEnd_7312933 : Nat := 3755049623126141849705939

theorem tailTrace_7312933 : CollatzResearch.WordTrace tailWord_7312933 prefixEnd_7312933 3755049623126141849705939 := by
  unfold tailWord_7312933
  simp only [CollatzResearch.WordTrace]
  refine ⟨266724578815500165367559453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177816385877000110245039635 266724578815500165367559453)
  ·
    refine ⟨100021717055812562012834795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266724578815500165367559453 100021717055812562012834795)
    ·
      refine ⟨150032575583718843019252193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100021717055812562012834795 150032575583718843019252193)
      ·
        refine ⟨112524431687789132264439145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150032575583718843019252193 112524431687789132264439145)
        ·
          refine ⟨84393323765841849198329359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112524431687789132264439145 84393323765841849198329359)
          ·
            refine ⟨126589985648762773797494039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84393323765841849198329359 126589985648762773797494039)
            ·
              refine ⟨189884978473144160696241059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126589985648762773797494039 189884978473144160696241059)
              ·
                refine ⟨284827467709716241044361589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189884978473144160696241059 284827467709716241044361589)
                ·
                  refine ⟨26702575097785897597908899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284827467709716241044361589 26702575097785897597908899)
                  ·
                    refine ⟨40053862646678846396863349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26702575097785897597908899 40053862646678846396863349)
                    ·
                      refine ⟨3755049623126141849705939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40053862646678846396863349 3755049623126141849705939)
                      ·
                        rfl

theorem cell23_7312933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_7312933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312933 prefixEnd_7312933 := by exact prefixLift 7312933
  have htrace : WordTrace (prefixWord ++ tailWord_7312933) baseStart_7312933 baseEnd_7312933 := by
    simpa [prefixWord, tailWord_7312933, baseEnd_7312933] using wordTrace_append hprefix tailTrace_7312933
  have hstable : (prefixWord ++ tailWord_7312933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312933).length < 2 ^ (prefixWord ++ tailWord_7312933).sum := by decide
  have hdescent : baseEnd_7312933 < baseStart_7312933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312953 : List Nat := [1, 2, 1, 5, 1, 2, 11]
def baseStart_7312953 : Nat := 118140960795 + 7312953 * 2 ^ 59
def prefixEnd_7312953 : Nat := 4983230072969 + 3 ^ 40 * 7312953 * 2
def baseEnd_7312953 : Nat := 46358764107891750264887

theorem tailTrace_7312953 : CollatzResearch.WordTrace tailWord_7312953 prefixEnd_7312953 46358764107891750264887 := by
  unfold tailWord_7312953
  simp only [CollatzResearch.WordTrace]
  refine ⟨266725308275427708783287513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177816872183618472522191675 266725308275427708783287513)
  ·
    refine ⟨200043981206570781587465635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266725308275427708783287513 200043981206570781587465635)
    ·
      refine ⟨300065971809856172381198453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200043981206570781587465635 300065971809856172381198453)
      ·
        refine ⟨28131184857174016160737355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300065971809856172381198453 28131184857174016160737355)
        ·
          refine ⟨42196777285761024241106033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28131184857174016160737355 42196777285761024241106033)
          ·
            refine ⟨31647582964320768180829525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42196777285761024241106033 31647582964320768180829525)
            ·
              refine ⟨46358764107891750264887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31647582964320768180829525 46358764107891750264887)
              ·
                rfl

theorem cell23_7312953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 11].length) (baseStart_7312953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312953 prefixEnd_7312953 := by exact prefixLift 7312953
  have htrace : WordTrace (prefixWord ++ tailWord_7312953) baseStart_7312953 baseEnd_7312953 := by
    simpa [prefixWord, tailWord_7312953, baseEnd_7312953] using wordTrace_append hprefix tailTrace_7312953
  have hstable : (prefixWord ++ tailWord_7312953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312953).length < 2 ^ (prefixWord ++ tailWord_7312953).sum := by decide
  have hdescent : baseEnd_7312953 < baseStart_7312953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7312997 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_7312997 : Nat := 118140960795 + 7312997 * 2 ^ 59
def prefixEnd_7312997 : Nat := 4983230072969 + 3 ^ 40 * 7312997 * 2
def baseEnd_7312997 : Nat := 3755082485888029599305645

theorem tailTrace_7312997 : CollatzResearch.WordTrace tailWord_7312997 prefixEnd_7312997 3755082485888029599305645 := by
  unfold tailWord_7312997
  simp only [CollatzResearch.WordTrace]
  refine ⟨266726913087268304297889245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177817942058178869531926163 266726913087268304297889245)
  ·
    refine ⟨100022592407725614111708467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266726913087268304297889245 100022592407725614111708467)
    ·
      refine ⟨150033888611588421167562701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100022592407725614111708467 150033888611588421167562701)
      ·
        refine ⟨56262708229345657937836013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150033888611588421167562701 56262708229345657937836013)
        ·
          refine ⟨21098515586004621726688505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56262708229345657937836013 21098515586004621726688505)
          ·
            refine ⟨15823886689503466295016379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21098515586004621726688505 15823886689503466295016379)
            ·
              refine ⟨23735830034255199442524569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15823886689503466295016379 23735830034255199442524569)
              ·
                refine ⟨17801872525691399581893427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23735830034255199442524569 17801872525691399581893427)
                ·
                  refine ⟨26702808788537099372840141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17801872525691399581893427 26702808788537099372840141)
                  ·
                    refine ⟨10013553295701412264815053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26702808788537099372840141 10013553295701412264815053)
                    ·
                      refine ⟨3755082485888029599305645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013553295701412264815053 3755082485888029599305645)
                      ·
                        rfl

theorem cell23_7312997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_7312997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7312997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7312997 prefixEnd_7312997 := by exact prefixLift 7312997
  have htrace : WordTrace (prefixWord ++ tailWord_7312997) baseStart_7312997 baseEnd_7312997 := by
    simpa [prefixWord, tailWord_7312997, baseEnd_7312997] using wordTrace_append hprefix tailTrace_7312997
  have hstable : (prefixWord ++ tailWord_7312997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7312997).length < 2 ^ (prefixWord ++ tailWord_7312997).sum := by decide
  have hdescent : baseEnd_7312997 < baseStart_7312997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7312997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313058 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_7313058 : Nat := 118140960795 + 7313058 * 2 ^ 59
def prefixEnd_7313058 : Nat := 4983230072969 + 3 ^ 40 * 7313058 * 2
def baseEnd_7313058 : Nat := 3755113808207953860642865

theorem tailTrace_7313058 : CollatzResearch.WordTrace tailWord_7313058 prefixEnd_7313058 3755113808207953860642865 := by
  unfold tailWord_7313058
  simp only [CollatzResearch.WordTrace]
  refine ⟨66682284485011827928964957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177819425293364874477239885 66682284485011827928964957)
  ·
    refine ⟨25005856681879435473361859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66682284485011827928964957 25005856681879435473361859)
    ·
      refine ⟨37508785022819153210042789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25005856681879435473361859 37508785022819153210042789)
      ·
        refine ⟨7032897191778591226883023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37508785022819153210042789 7032897191778591226883023)
        ·
          refine ⟨10549345787667886840324535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7032897191778591226883023 10549345787667886840324535)
          ·
            refine ⟨15824018681501830260486803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549345787667886840324535 15824018681501830260486803)
            ·
              refine ⟨23736028022252745390730205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15824018681501830260486803 23736028022252745390730205)
              ·
                refine ⟨8901010508344779521523827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23736028022252745390730205 8901010508344779521523827)
                ·
                  refine ⟨13351515762517169282285741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8901010508344779521523827 13351515762517169282285741)
                  ·
                    refine ⟨5006818410943938480857153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13351515762517169282285741 5006818410943938480857153)
                    ·
                      refine ⟨3755113808207953860642865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5006818410943938480857153 3755113808207953860642865)
                      ·
                        rfl

theorem cell23_7313058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_7313058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313058 prefixEnd_7313058 := by exact prefixLift 7313058
  have htrace : WordTrace (prefixWord ++ tailWord_7313058) baseStart_7313058 baseEnd_7313058 := by
    simpa [prefixWord, tailWord_7313058, baseEnd_7313058] using wordTrace_append hprefix tailTrace_7313058
  have hstable : (prefixWord ++ tailWord_7313058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313058).length < 2 ^ (prefixWord ++ tailWord_7313058).sum := by decide
  have hdescent : baseEnd_7313058 < baseStart_7313058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313154 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_7313154 : Nat := 118140960795 + 7313154 * 2 ^ 59
def prefixEnd_7313154 : Nat := 4983230072969 + 3 ^ 40 * 7313154 * 2
def baseEnd_7313154 : Nat := 1251721034116928495014141

theorem tailTrace_7313154 : CollatzResearch.WordTrace tailWord_7313154 prefixEnd_7313154 1251721034116928495014141 := by
  unfold tailWord_7313154
  simp only [CollatzResearch.WordTrace]
  refine ⟨66683159836924880027838629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177821759565133013407569677 66683159836924880027838629)
  ·
    refine ⟨12503092469423415005219743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66683159836924880027838629 12503092469423415005219743)
    ·
      refine ⟨18754638704135122507829615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12503092469423415005219743 18754638704135122507829615)
      ·
        refine ⟨28131958056202683761744423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18754638704135122507829615 28131958056202683761744423)
        ·
          refine ⟨42197937084304025642616635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28131958056202683761744423 42197937084304025642616635)
          ·
            refine ⟨63296905626456038463924953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42197937084304025642616635 63296905626456038463924953)
            ·
              refine ⟨47472679219842028847943715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63296905626456038463924953 47472679219842028847943715)
              ·
                refine ⟨71209018829763043271915573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47472679219842028847943715 71209018829763043271915573)
                ·
                  refine ⟨6675845515290285306742085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71209018829763043271915573 6675845515290285306742085)
                  ·
                    refine ⟨1251721034116928495014141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6675845515290285306742085 1251721034116928495014141)
                    ·
                      rfl

theorem cell23_7313154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_7313154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313154 prefixEnd_7313154 := by exact prefixLift 7313154
  have htrace : WordTrace (prefixWord ++ tailWord_7313154) baseStart_7313154 baseEnd_7313154 := by
    simpa [prefixWord, tailWord_7313154, baseEnd_7313154] using wordTrace_append hprefix tailTrace_7313154
  have hstable : (prefixWord ++ tailWord_7313154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313154).length < 2 ^ (prefixWord ++ tailWord_7313154).sum := by decide
  have hdescent : baseEnd_7313154 < baseStart_7313154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313188 : List Nat := [2, 3, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_7313188 : Nat := 118140960795 + 7313188 * 2 ^ 59
def prefixEnd_7313188 : Nat := 4983230072969 + 3 ^ 40 * 7313188 * 2
def baseEnd_7313188 : Nat := 1251726853564346117339089

theorem tailTrace_7313188 : CollatzResearch.WordTrace tailWord_7313188 prefixEnd_7313188 1251726853564346117339089 := by
  unfold tailWord_7313188
  simp only [CollatzResearch.WordTrace]
  refine ⟨133366939714788171959046109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177822586286384229278728145 133366939714788171959046109)
  ·
    refine ⟨50012602393045564484642291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133366939714788171959046109 50012602393045564484642291)
    ·
      refine ⟨75018903589568346726963437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50012602393045564484642291 75018903589568346726963437)
      ·
        refine ⟨28132088846088130022611289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75018903589568346726963437 28132088846088130022611289)
        ·
          refine ⟨21099066634566097516958467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28132088846088130022611289 21099066634566097516958467)
          ·
            refine ⟨31648599951849146275437701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21099066634566097516958467 31648599951849146275437701)
            ·
              refine ⟨5934112490971714926644569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31648599951849146275437701 5934112490971714926644569)
              ·
                refine ⟨4450584368228786194983427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934112490971714926644569 4450584368228786194983427)
                ·
                  refine ⟨6675876552343179292475141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450584368228786194983427 6675876552343179292475141)
                  ·
                    refine ⟨1251726853564346117339089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6675876552343179292475141 1251726853564346117339089)
                    ·
                      rfl

theorem cell23_7313188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_7313188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313188 prefixEnd_7313188 := by exact prefixLift 7313188
  have htrace : WordTrace (prefixWord ++ tailWord_7313188) baseStart_7313188 baseEnd_7313188 := by
    simpa [prefixWord, tailWord_7313188, baseEnd_7313188] using wordTrace_append hprefix tailTrace_7313188
  have hstable : (prefixWord ++ tailWord_7313188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313188).length < 2 ^ (prefixWord ++ tailWord_7313188).sum := by decide
  have hdescent : baseEnd_7313188 < baseStart_7313188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313214 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_7313214 : Nat := 118140960795 + 7313214 * 2 ^ 59
def prefixEnd_7313214 : Nat := 4983230072969 + 3 ^ 40 * 7313214 * 2
def baseEnd_7313214 : Nat := 1251731303730018416764049

theorem tailTrace_7313214 : CollatzResearch.WordTrace tailWord_7313214 prefixEnd_7313214 1251731303730018416764049 := by
  unfold tailWord_7313214
  simp only [CollatzResearch.WordTrace]
  refine ⟨33341853465935268794817337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177823218484988100239025797 33341853465935268794817337)
  ·
    refine ⟨25006390099451451596113003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33341853465935268794817337 25006390099451451596113003)
    ·
      refine ⟨37509585149177177394169505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25006390099451451596113003 37509585149177177394169505)
      ·
        refine ⟨28132188861882883045627129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37509585149177177394169505 28132188861882883045627129)
        ·
          refine ⟨21099141646412162284220347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28132188861882883045627129 21099141646412162284220347)
          ·
            refine ⟨31648712469618243426330521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21099141646412162284220347 31648712469618243426330521)
            ·
              refine ⟨23736534352213682569747891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31648712469618243426330521 23736534352213682569747891)
              ·
                refine ⟨35604801528320523854621837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23736534352213682569747891 35604801528320523854621837)
                ·
                  refine ⟨13351800573120196445483189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35604801528320523854621837 13351800573120196445483189)
                  ·
                    refine ⟨1251731303730018416764049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13351800573120196445483189 1251731303730018416764049)
                    ·
                      rfl

theorem cell23_7313214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_7313214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313214 prefixEnd_7313214 := by exact prefixLift 7313214
  have htrace : WordTrace (prefixWord ++ tailWord_7313214) baseStart_7313214 baseEnd_7313214 := by
    simpa [prefixWord, tailWord_7313214, baseEnd_7313214] using wordTrace_append hprefix tailTrace_7313214
  have hstable : (prefixWord ++ tailWord_7313214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313214).length < 2 ^ (prefixWord ++ tailWord_7313214).sum := by decide
  have hdescent : baseEnd_7313214 < baseStart_7313214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313284 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_7313284 : Nat := 118140960795 + 7313284 * 2 ^ 59
def prefixEnd_7313284 : Nat := 4983230072969 + 3 ^ 40 * 7313284 * 2
def baseEnd_7313284 : Nat := 3755229854835869976416825

theorem tailTrace_7313284 : CollatzResearch.WordTrace tailWord_7313284 prefixEnd_7313284 3755229854835869976416825 := by
  unfold tailWord_7313284
  simp only [CollatzResearch.WordTrace]
  refine ⟨133368690418614276156793453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177824920558152368209057937 133368690418614276156793453)
  ·
    refine ⟨50013258906980353558797545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133368690418614276156793453 50013258906980353558797545)
    ·
      refine ⟨37509944180235265169098159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50013258906980353558797545 37509944180235265169098159)
      ·
        refine ⟨56264916270352897753647239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37509944180235265169098159 56264916270352897753647239)
        ·
          refine ⟨84397374405529346630470859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56264916270352897753647239 84397374405529346630470859)
          ·
            refine ⟨126596061608294019945706289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84397374405529346630470859 126596061608294019945706289)
            ·
              refine ⟨94947046206220514959279717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126596061608294019945706289 94947046206220514959279717)
              ·
                refine ⟨17802571163666346554864947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94947046206220514959279717 17802571163666346554864947)
                ·
                  refine ⟨26703856745499519832297421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17802571163666346554864947 26703856745499519832297421)
                  ·
                    refine ⟨10013946279562319937111533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26703856745499519832297421 10013946279562319937111533)
                    ·
                      refine ⟨3755229854835869976416825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013946279562319937111533 3755229854835869976416825)
                      ·
                        rfl

theorem cell23_7313284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_7313284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313284 prefixEnd_7313284 := by exact prefixLift 7313284
  have htrace : WordTrace (prefixWord ++ tailWord_7313284) baseStart_7313284 baseEnd_7313284 := by
    simpa [prefixWord, tailWord_7313284, baseEnd_7313284] using wordTrace_append hprefix tailTrace_7313284
  have hstable : (prefixWord ++ tailWord_7313284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313284).length < 2 ^ (prefixWord ++ tailWord_7313284).sum := by decide
  have hdescent : baseEnd_7313284 < baseStart_7313284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313301 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_7313301 : Nat := 118140960795 + 7313301 * 2 ^ 59
def prefixEnd_7313301 : Nat := 4983230072969 + 3 ^ 40 * 7313301 * 2
def baseEnd_7313301 : Nat := 3755238584006996409904247

theorem tailTrace_7313301 : CollatzResearch.WordTrace tailWord_7313301 prefixEnd_7313301 3755238584006996409904247 := by
  unfold tailWord_7313301
  simp only [CollatzResearch.WordTrace]
  refine ⟨266738000878166964216955757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177825333918777976144637171 266738000878166964216955757)
  ·
    refine ⟨100026750329312611581358409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266738000878166964216955757 100026750329312611581358409)
    ·
      refine ⟨75020062746984458686018807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100026750329312611581358409 75020062746984458686018807)
      ·
        refine ⟨112530094120476688029028211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75020062746984458686018807 112530094120476688029028211)
        ·
          refine ⟨168795141180715032043542317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112530094120476688029028211 168795141180715032043542317)
          ·
            refine ⟨63298177942768137016328369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168795141180715032043542317 63298177942768137016328369)
            ·
              refine ⟨47473633457076102762246277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63298177942768137016328369 47473633457076102762246277)
              ·
                refine ⟨8901306273201769267921177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47473633457076102762246277 8901306273201769267921177)
                ·
                  refine ⟨6675979704901326950940883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8901306273201769267921177 6675979704901326950940883)
                  ·
                    refine ⟨10013969557351990426411325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675979704901326950940883 10013969557351990426411325)
                    ·
                      refine ⟨3755238584006996409904247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10013969557351990426411325 3755238584006996409904247)
                      ·
                        rfl

theorem cell23_7313301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_7313301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313301 prefixEnd_7313301 := by exact prefixLift 7313301
  have htrace : WordTrace (prefixWord ++ tailWord_7313301) baseStart_7313301 baseEnd_7313301 := by
    simpa [prefixWord, tailWord_7313301, baseEnd_7313301] using wordTrace_append hprefix tailTrace_7313301
  have hstable : (prefixWord ++ tailWord_7313301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313301).length < 2 ^ (prefixWord ++ tailWord_7313301).sum := by decide
  have hdescent : baseEnd_7313301 < baseStart_7313301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313317 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_7313317 : Nat := 118140960795 + 7313317 * 2 ^ 59
def prefixEnd_7313317 : Nat := 4983230072969 + 3 ^ 40 * 7313317 * 2
def baseEnd_7313317 : Nat := 1251748933232489449101391

theorem tailTrace_7313317 : CollatzResearch.WordTrace tailWord_7313317 prefixEnd_7313317 1251748933232489449101391 := by
  unfold tailWord_7313317
  simp only [CollatzResearch.WordTrace]
  refine ⟨266738584446108998949538205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177825722964072665966358803 266738584446108998949538205)
  ·
    refine ⟨100026969167290874606076827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266738584446108998949538205 100026969167290874606076827)
    ·
      refine ⟨150040453750936311909115241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100026969167290874606076827 150040453750936311909115241)
      ·
        refine ⟨112530340313202233931836431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150040453750936311909115241 112530340313202233931836431)
        ·
          refine ⟨168795510469803350897754647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112530340313202233931836431 168795510469803350897754647)
          ·
            refine ⟨253193265704705026346631971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168795510469803350897754647 253193265704705026346631971)
            ·
              refine ⟨379789898557057539519947957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253193265704705026346631971 379789898557057539519947957)
              ·
                refine ⟨35605302989724144329995121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379789898557057539519947957 35605302989724144329995121)
                ·
                  refine ⟨26703977242293108247496341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35605302989724144329995121 26703977242293108247496341)
                  ·
                    refine ⟨1251748933232489449101391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26703977242293108247496341 1251748933232489449101391)
                    ·
                      rfl

theorem cell23_7313317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_7313317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313317 prefixEnd_7313317 := by exact prefixLift 7313317
  have htrace : WordTrace (prefixWord ++ tailWord_7313317) baseStart_7313317 baseEnd_7313317 := by
    simpa [prefixWord, tailWord_7313317, baseEnd_7313317] using wordTrace_append hprefix tailTrace_7313317
  have hstable : (prefixWord ++ tailWord_7313317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313317).length < 2 ^ (prefixWord ++ tailWord_7313317).sum := by decide
  have hdescent : baseEnd_7313317 < baseStart_7313317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313327 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_7313327 : Nat := 118140960795 + 7313327 * 2 ^ 59
def prefixEnd_7313327 : Nat := 4983230072969 + 3 ^ 40 * 7313327 * 2
def baseEnd_7313327 : Nat := 3755251934504013308179127

theorem tailTrace_7313327 : CollatzResearch.WordTrace tailWord_7313327 prefixEnd_7313327 3755251934504013308179127 := by
  unfold tailWord_7313327
  simp only [CollatzResearch.WordTrace]
  refine ⟨266738949176072770657402235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177825966117381847104934823 266738949176072770657402235)
  ·
    refine ⟨400108423764109155986103353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266738949176072770657402235 400108423764109155986103353)
    ·
      refine ⟨300081317823081866989577515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400108423764109155986103353 300081317823081866989577515)
      ·
        refine ⟨450121976734622800484366273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300081317823081866989577515 450121976734622800484366273)
        ·
          refine ⟨337591482550967100363274705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450121976734622800484366273 337591482550967100363274705)
          ·
            refine ⟨253193611913225325272456029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337591482550967100363274705 253193611913225325272456029)
            ·
              refine ⟨94947604467459496977171011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253193611913225325272456029 94947604467459496977171011)
              ·
                refine ⟨142421406701189245465756517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94947604467459496977171011 142421406701189245465756517)
                ·
                  refine ⟨26704013756472983524829347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142421406701189245465756517 26704013756472983524829347)
                  ·
                    refine ⟨40056020634709475287244021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26704013756472983524829347 40056020634709475287244021)
                    ·
                      refine ⟨3755251934504013308179127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40056020634709475287244021 3755251934504013308179127)
                      ·
                        rfl

theorem cell23_7313327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_7313327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313327 prefixEnd_7313327 := by exact prefixLift 7313327
  have htrace : WordTrace (prefixWord ++ tailWord_7313327) baseStart_7313327 baseEnd_7313327 := by
    simpa [prefixWord, tailWord_7313327, baseEnd_7313327] using wordTrace_append hprefix tailTrace_7313327
  have hstable : (prefixWord ++ tailWord_7313327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313327).length < 2 ^ (prefixWord ++ tailWord_7313327).sum := by decide
  have hdescent : baseEnd_7313327 < baseStart_7313327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313341 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_7313341 : Nat := 118140960795 + 7313341 * 2 ^ 59
def prefixEnd_7313341 : Nat := 4983230072969 + 3 ^ 40 * 7313341 * 2
def baseEnd_7313341 : Nat := 3755259123233176253404063

theorem tailTrace_7313341 : CollatzResearch.WordTrace tailWord_7313341 prefixEnd_7313341 3755259123233176253404063 := by
  unfold tailWord_7313341
  simp only [CollatzResearch.WordTrace]
  refine ⟨266739459798022051048411877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177826306532014700698941251 266739459798022051048411877)
  ·
    refine ⟨50013648712129134571577227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266739459798022051048411877 50013648712129134571577227)
    ·
      refine ⟨75020473068193701857365841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50013648712129134571577227 75020473068193701857365841)
      ·
        refine ⟨56265354801145276393024381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75020473068193701857365841 56265354801145276393024381)
        ·
          refine ⟨21099508050429478647384143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56265354801145276393024381 21099508050429478647384143)
          ·
            refine ⟨31649262075644217971076215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21099508050429478647384143 31649262075644217971076215)
            ·
              refine ⟨47473893113466326956614323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31649262075644217971076215 47473893113466326956614323)
              ·
                refine ⟨71210839670199490434921485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47473893113466326956614323 71210839670199490434921485)
                ·
                  refine ⟨26704064876324808913095557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71210839670199490434921485 26704064876324808913095557)
                  ·
                    refine ⟨5007012164310901671205417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26704064876324808913095557 5007012164310901671205417)
                    ·
                      refine ⟨3755259123233176253404063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007012164310901671205417 3755259123233176253404063)
                      ·
                        rfl

theorem cell23_7313341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_7313341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313341 prefixEnd_7313341 := by exact prefixLift 7313341
  have htrace : WordTrace (prefixWord ++ tailWord_7313341) baseStart_7313341 baseEnd_7313341 := by
    simpa [prefixWord, tailWord_7313341, baseEnd_7313341] using wordTrace_append hprefix tailTrace_7313341
  have hstable : (prefixWord ++ tailWord_7313341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313341).length < 2 ^ (prefixWord ++ tailWord_7313341).sum := by decide
  have hdescent : baseEnd_7313341 < baseStart_7313341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313364 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 7]
def baseStart_7313364 : Nat := 118140960795 + 7313364 * 2 ^ 59
def prefixEnd_7313364 : Nat := 4983230072969 + 3 ^ 40 * 7313364 * 2
def baseEnd_7313364 : Nat := 417252325920914407046273

theorem tailTrace_7313364 : CollatzResearch.WordTrace tailWord_7313364 prefixEnd_7313364 417252325920914407046273 := by
  unfold tailWord_7313364
  simp only [CollatzResearch.WordTrace]
  refine ⟨133370149338469362988249573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177826865784625817317666097 133370149338469362988249573)
  ·
    refine ⟨25006903000963005560296795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133370149338469362988249573 25006903000963005560296795)
    ·
      refine ⟨37510354501444508340445193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25006903000963005560296795 37510354501444508340445193)
      ·
        refine ⟨28132765876083381255333895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37510354501444508340445193 28132765876083381255333895)
        ·
          refine ⟨42199148814125071883000843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28132765876083381255333895 42199148814125071883000843)
          ·
            refine ⟨63298723221187607824501265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42199148814125071883000843 63298723221187607824501265)
            ·
              refine ⟨47474042415890705868375949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63298723221187607824501265 47474042415890705868375949)
              ·
                refine ⟨17802765905959014700640981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47474042415890705868375949 17802765905959014700640981)
                ·
                  refine ⟨417252325920914407046273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17802765905959014700640981 417252325920914407046273)
                  ·
                    rfl

theorem cell23_7313364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_7313364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313364 prefixEnd_7313364 := by exact prefixLift 7313364
  have htrace : WordTrace (prefixWord ++ tailWord_7313364) baseStart_7313364 baseEnd_7313364 := by
    simpa [prefixWord, tailWord_7313364, baseEnd_7313364] using wordTrace_append hprefix tailTrace_7313364
  have hstable : (prefixWord ++ tailWord_7313364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313364).length < 2 ^ (prefixWord ++ tailWord_7313364).sum := by decide
  have hdescent : baseEnd_7313364 < baseStart_7313364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313387 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7]
def baseStart_7313387 : Nat := 118140960795 + 7313387 * 2 ^ 59
def prefixEnd_7313387 : Nat := 4983230072969 + 3 ^ 40 * 7313387 * 2
def baseEnd_7313387 : Nat := 3755282743343283073428851

theorem tailTrace_7313387 : CollatzResearch.WordTrace tailWord_7313387 prefixEnd_7313387 3755282743343283073428851 := by
  unfold tailWord_7313387
  simp only [CollatzResearch.WordTrace]
  refine ⟨266741137555855400904586415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177827425037236933936390943 266741137555855400904586415)
  ·
    refine ⟨400111706333783101356879623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266741137555855400904586415 400111706333783101356879623)
    ·
      refine ⟨600167559500674652035319435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400111706333783101356879623 600167559500674652035319435)
      ·
        refine ⟨900251339251011978052979153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600167559500674652035319435 900251339251011978052979153)
        ·
          refine ⟨675188504438258983539734365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900251339251011978052979153 675188504438258983539734365)
          ·
            refine ⟨253195689164347118827400387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675188504438258983539734365 253195689164347118827400387)
            ·
              refine ⟨379793533746520678241100581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253195689164347118827400387 379793533746520678241100581)
              ·
                refine ⟨71211287577472627170206359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379793533746520678241100581 71211287577472627170206359)
                ·
                  refine ⟨106816931366208940755309539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71211287577472627170206359 106816931366208940755309539)
                  ·
                    refine ⟨160225397049313411132964309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106816931366208940755309539 160225397049313411132964309)
                    ·
                      refine ⟨3755282743343283073428851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160225397049313411132964309 3755282743343283073428851)
                      ·
                        rfl

theorem cell23_7313387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_7313387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313387 prefixEnd_7313387 := by exact prefixLift 7313387
  have htrace : WordTrace (prefixWord ++ tailWord_7313387) baseStart_7313387 baseEnd_7313387 := by
    simpa [prefixWord, tailWord_7313387, baseEnd_7313387] using wordTrace_append hprefix tailTrace_7313387
  have hstable : (prefixWord ++ tailWord_7313387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313387).length < 2 ^ (prefixWord ++ tailWord_7313387).sum := by decide
  have hdescent : baseEnd_7313387 < baseStart_7313387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313407 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 10]
def baseStart_7313407 : Nat := 118140960795 + 7313407 * 2 ^ 59
def prefixEnd_7313407 : Nat := 4983230072969 + 3 ^ 40 * 7313407 * 2
def baseEnd_7313407 : Nat := 1251764337652124331726253

theorem tailTrace_7313407 : CollatzResearch.WordTrace tailWord_7313407 prefixEnd_7313407 1251764337652124331726253 := by
  unfold tailWord_7313407
  simp only [CollatzResearch.WordTrace]
  refine ⟨266741867015782944320314475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177827911343855296213542983 266741867015782944320314475)
  ·
    refine ⟨400112800523674416480471713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266741867015782944320314475 400112800523674416480471713)
    ·
      refine ⟨300084600392755812360353785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400112800523674416480471713 300084600392755812360353785)
      ·
        refine ⟨225063450294566859270265339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300084600392755812360353785 225063450294566859270265339)
        ·
          refine ⟨337595175441850288905398009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225063450294566859270265339 337595175441850288905398009)
          ·
            refine ⟨253196381581387716679048507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337595175441850288905398009 253196381581387716679048507)
            ·
              refine ⟨379794572372081575018572761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253196381581387716679048507 379794572372081575018572761)
              ·
                refine ⟨284845929279061181263929571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379794572372081575018572761 284845929279061181263929571)
                ·
                  refine ⟨427268893918591771895894357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284845929279061181263929571 427268893918591771895894357)
                  ·
                    refine ⟨1251764337652124331726253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 427268893918591771895894357 1251764337652124331726253)
                    ·
                      rfl

theorem cell23_7313407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_7313407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313407 prefixEnd_7313407 := by exact prefixLift 7313407
  have htrace : WordTrace (prefixWord ++ tailWord_7313407) baseStart_7313407 baseEnd_7313407 := by
    simpa [prefixWord, tailWord_7313407, baseEnd_7313407] using wordTrace_append hprefix tailTrace_7313407
  have hstable : (prefixWord ++ tailWord_7313407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313407).length < 2 ^ (prefixWord ++ tailWord_7313407).sum := by decide
  have hdescent : baseEnd_7313407 < baseStart_7313407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313424 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 7, 4]
def baseStart_7313424 : Nat := 118140960795 + 7313424 * 2 ^ 59
def prefixEnd_7313424 : Nat := 4983230072969 + 3 ^ 40 * 7313424 * 2
def baseEnd_7313424 : Nat := 1251767247375833142888727

theorem tailTrace_7313424 : CollatzResearch.WordTrace tailWord_7313424 prefixEnd_7313424 1251767247375833142888727 := by
  unfold tailWord_7313424
  simp only [CollatzResearch.WordTrace]
  refine ⟨133371243528360678111841663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177828324704480904149122217 133371243528360678111841663)
  ·
    refine ⟨200056865292541017167762495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133371243528360678111841663 200056865292541017167762495)
    ·
      refine ⟨300085297938811525751643743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200056865292541017167762495 300085297938811525751643743)
      ·
        refine ⟨450127946908217288627465615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300085297938811525751643743 450127946908217288627465615)
        ·
          refine ⟨675191920362325932941198423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450127946908217288627465615 675191920362325932941198423)
          ·
            refine ⟨1012787880543488899411797635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675191920362325932941198423 1012787880543488899411797635)
            ·
              refine ⟨1519181820815233349117696453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012787880543488899411797635 1519181820815233349117696453)
              ·
                refine ⟨284846591402856252959568085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1519181820815233349117696453 284846591402856252959568085)
                ·
                  refine ⟨6676091986004443428739877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 284846591402856252959568085 6676091986004443428739877)
                  ·
                    refine ⟨1251767247375833142888727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676091986004443428739877 1251767247375833142888727)
                    ·
                      rfl

theorem cell23_7313424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_7313424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313424 prefixEnd_7313424 := by exact prefixLift 7313424
  have htrace : WordTrace (prefixWord ++ tailWord_7313424) baseStart_7313424 baseEnd_7313424 := by
    simpa [prefixWord, tailWord_7313424, baseEnd_7313424] using wordTrace_append hprefix tailTrace_7313424
  have hstable : (prefixWord ++ tailWord_7313424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313424).length < 2 ^ (prefixWord ++ tailWord_7313424).sum := by decide
  have hdescent : baseEnd_7313424 < baseStart_7313424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313508 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_7313508 : Nat := 118140960795 + 7313508 * 2 ^ 59
def prefixEnd_7313508 : Nat := 4983230072969 + 3 ^ 40 * 7313508 * 2
def baseEnd_7313508 : Nat := 3755344874502477100015795

theorem tailTrace_7313508 : CollatzResearch.WordTrace tailWord_7313508 prefixEnd_7313508 3755344874502477100015795 := by
  unfold tailWord_7313508
  simp only [CollatzResearch.WordTrace]
  refine ⟨133372775394208519284870589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177830367192278025713160785 133372775394208519284870589)
  ·
    refine ⟨50014790772828194731826471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133372775394208519284870589 50014790772828194731826471)
    ·
      refine ⟨75022186159242292097739707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50014790772828194731826471 75022186159242292097739707)
      ·
        refine ⟨112533279238863438146609561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75022186159242292097739707 112533279238863438146609561)
        ·
          refine ⟨84399959429147578609957171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112533279238863438146609561 84399959429147578609957171)
          ·
            refine ⟨126599939143721367914935757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84399959429147578609957171 126599939143721367914935757)
            ·
              refine ⟨47474977178895512968100909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126599939143721367914935757 47474977178895512968100909)
              ·
                refine ⟨17803116442085817363037841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47474977178895512968100909 17803116442085817363037841)
                ·
                  refine ⟨13352337331564363022278381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17803116442085817363037841 13352337331564363022278381)
                  ·
                    refine ⟨5007126499336636133354393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13352337331564363022278381 5007126499336636133354393)
                    ·
                      refine ⟨3755344874502477100015795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007126499336636133354393 3755344874502477100015795)
                      ·
                        rfl

theorem cell23_7313508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_7313508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313508 prefixEnd_7313508 := by exact prefixLift 7313508
  have htrace : WordTrace (prefixWord ++ tailWord_7313508) baseStart_7313508 baseEnd_7313508 := by
    simpa [prefixWord, tailWord_7313508, baseEnd_7313508] using wordTrace_append hprefix tailTrace_7313508
  have hstable : (prefixWord ++ tailWord_7313508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313508).length < 2 ^ (prefixWord ++ tailWord_7313508).sum := by decide
  have hdescent : baseEnd_7313508 < baseStart_7313508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313532 : List Nat := [2, 2, 2, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_7313532 : Nat := 118140960795 + 7313532 * 2 ^ 59
def prefixEnd_7313532 : Nat := 4983230072969 + 3 ^ 40 * 7313532 * 2
def baseEnd_7313532 : Nat := 3755357198038185006115685

theorem tailTrace_7313532 : CollatzResearch.WordTrace tailWord_7313532 prefixEnd_7313532 3755357198038185006115685 := by
  unfold tailWord_7313532
  simp only [CollatzResearch.WordTrace]
  refine ⟨133373213070165045334307425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177830950760220060445743233 133373213070165045334307425)
  ·
    refine ⟨100029909802623784000730569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133373213070165045334307425 100029909802623784000730569)
    ·
      refine ⟨75022432351967838000547927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100029909802623784000730569 75022432351967838000547927)
      ·
        refine ⟨112533648527951757000821891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75022432351967838000547927 112533648527951757000821891)
        ·
          refine ⟨168800472791927635501232837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112533648527951757000821891 168800472791927635501232837)
          ·
            refine ⟨31650088648486431656481157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168800472791927635501232837 31650088648486431656481157)
            ·
              refine ⟨5934391621591205935590217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31650088648486431656481157 5934391621591205935590217)
              ·
                refine ⟨4450793716193404451692663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934391621591205935590217 4450793716193404451692663)
                ·
                  refine ⟨6676190574290106677538995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450793716193404451692663 6676190574290106677538995)
                  ·
                    refine ⟨10014285861435160016308493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6676190574290106677538995 10014285861435160016308493)
                    ·
                      refine ⟨3755357198038185006115685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10014285861435160016308493 3755357198038185006115685)
                      ·
                        rfl

theorem cell23_7313532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_7313532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313532 prefixEnd_7313532 := by exact prefixLift 7313532
  have htrace : WordTrace (prefixWord ++ tailWord_7313532) baseStart_7313532 baseEnd_7313532 := by
    simpa [prefixWord, tailWord_7313532, baseEnd_7313532] using wordTrace_append hprefix tailTrace_7313532
  have hstable : (prefixWord ++ tailWord_7313532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313532).length < 2 ^ (prefixWord ++ tailWord_7313532).sum := by decide
  have hdescent : baseEnd_7313532 < baseStart_7313532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313572 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_7313572 : Nat := 118140960795 + 7313572 * 2 ^ 59
def prefixEnd_7313572 : Nat := 4983230072969 + 3 ^ 40 * 7313572 * 2
def baseEnd_7313572 : Nat := 3755377737264364849615501

theorem tailTrace_7313572 : CollatzResearch.WordTrace tailWord_7313572 prefixEnd_7313572 3755377737264364849615501 := by
  unfold tailWord_7313572
  simp only [CollatzResearch.WordTrace]
  refine ⟨133373942530092588750035485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177831923373456785000047313 133373942530092588750035485)
  ·
    refine ⟨50015228448784720781263307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133373942530092588750035485 50015228448784720781263307)
    ·
      refine ⟨75022842673177081171894961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50015228448784720781263307 75022842673177081171894961)
      ·
        refine ⟨56267132004882810878921221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75022842673177081171894961 56267132004882810878921221)
        ·
          refine ⟨10550087250915527039797729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56267132004882810878921221 10550087250915527039797729)
          ·
            refine ⟨7912565438186645279848297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10550087250915527039797729 7912565438186645279848297)
            ·
              refine ⟨5934424078639983959886223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912565438186645279848297 5934424078639983959886223)
              ·
                refine ⟨8901636117959975939829335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934424078639983959886223 8901636117959975939829335)
                ·
                  refine ⟨13352454176939963909744003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8901636117959975939829335 13352454176939963909744003)
                  ·
                    refine ⟨20028681265409945864616005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13352454176939963909744003 20028681265409945864616005)
                    ·
                      refine ⟨3755377737264364849615501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20028681265409945864616005 3755377737264364849615501)
                      ·
                        rfl

theorem cell23_7313572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_7313572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313572 prefixEnd_7313572 := by exact prefixLift 7313572
  have htrace : WordTrace (prefixWord ++ tailWord_7313572) baseStart_7313572 baseEnd_7313572 := by
    simpa [prefixWord, tailWord_7313572, baseEnd_7313572] using wordTrace_append hprefix tailTrace_7313572
  have hstable : (prefixWord ++ tailWord_7313572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313572).length < 2 ^ (prefixWord ++ tailWord_7313572).sum := by decide
  have hdescent : baseEnd_7313572 < baseStart_7313572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313578 : List Nat := [3, 1, 5, 1, 2, 1, 10]
def baseStart_7313578 : Nat := 118140960795 + 7313578 * 2 ^ 59
def prefixEnd_7313578 : Nat := 4983230072969 + 3 ^ 40 * 7313578 * 2
def baseEnd_7313578 : Nat := 46362726149978911433833

theorem tailTrace_7313578 : CollatzResearch.WordTrace tailWord_7313578 prefixEnd_7313578 46362726149978911433833 := by
  unfold tailWord_7313578
  simp only [CollatzResearch.WordTrace]
  refine ⟨66687025974540860131197347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177832069265442293683192925 66687025974540860131197347)
  ·
    refine ⟨100030538961811290196796021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66687025974540860131197347 100030538961811290196796021)
    ·
      refine ⟨9377863027669808455949627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100030538961811290196796021 9377863027669808455949627)
      ·
        refine ⟨14066794541504712683924441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377863027669808455949627 14066794541504712683924441)
        ·
          refine ⟨10550095906128534512943331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14066794541504712683924441 10550095906128534512943331)
          ·
            refine ⟨15825143859192801769414997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550095906128534512943331 15825143859192801769414997)
            ·
              refine ⟨46362726149978911433833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15825143859192801769414997 46362726149978911433833)
              ·
                rfl

theorem cell23_7313578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 10].length) (baseStart_7313578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313578 prefixEnd_7313578 := by exact prefixLift 7313578
  have htrace : WordTrace (prefixWord ++ tailWord_7313578) baseStart_7313578 baseEnd_7313578 := by
    simpa [prefixWord, tailWord_7313578, baseEnd_7313578] using wordTrace_append hprefix tailTrace_7313578
  have hstable : (prefixWord ++ tailWord_7313578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313578).length < 2 ^ (prefixWord ++ tailWord_7313578).sum := by decide
  have hdescent : baseEnd_7313578 < baseStart_7313578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313582 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7313582 : Nat := 118140960795 + 7313582 * 2 ^ 59
def prefixEnd_7313582 : Nat := 4983230072969 + 3 ^ 40 * 7313582 * 2
def baseEnd_7313582 : Nat := 1251794290690303270163485

theorem tailTrace_7313582 : CollatzResearch.WordTrace tailWord_7313582 prefixEnd_7313582 1251794290690303270163485 := by
  unfold tailWord_7313582
  simp only [CollatzResearch.WordTrace]
  refine ⟨33343531223768618650991875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177832166526765966138623333 33343531223768618650991875)
  ·
    refine ⟨50015296835652927976487813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33343531223768618650991875 50015296835652927976487813)
    ·
      refine ⟨9377868156684923995591465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50015296835652927976487813 9377868156684923995591465)
      ·
        refine ⟨7033401117513692996693599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9377868156684923995591465 7033401117513692996693599)
        ·
          refine ⟨10550101676270539495040399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033401117513692996693599 10550101676270539495040399)
          ·
            refine ⟨15825152514405809242560599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550101676270539495040399 15825152514405809242560599)
            ·
              refine ⟨23737728771608713863840899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15825152514405809242560599 23737728771608713863840899)
              ·
                refine ⟨35606593157413070795761349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23737728771608713863840899 35606593157413070795761349)
                ·
                  refine ⟨6676236217014950774205253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35606593157413070795761349 6676236217014950774205253)
                  ·
                    refine ⟨1251794290690303270163485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676236217014950774205253 1251794290690303270163485)
                    ·
                      rfl

theorem cell23_7313582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7313582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313582 prefixEnd_7313582 := by exact prefixLift 7313582
  have htrace : WordTrace (prefixWord ++ tailWord_7313582) baseStart_7313582 baseEnd_7313582 := by
    simpa [prefixWord, tailWord_7313582, baseEnd_7313582] using wordTrace_append hprefix tailTrace_7313582
  have hstable : (prefixWord ++ tailWord_7313582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313582).length < 2 ^ (prefixWord ++ tailWord_7313582).sum := by decide
  have hdescent : baseEnd_7313582 < baseStart_7313582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313584 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_7313584 : Nat := 118140960795 + 7313584 * 2 ^ 59
def prefixEnd_7313584 : Nat := 4983230072969 + 3 ^ 40 * 7313584 * 2
def baseEnd_7313584 : Nat := 3755383899032218802665445

theorem tailTrace_7313584 : CollatzResearch.WordTrace tailWord_7313584 prefixEnd_7313584 3755383899032218802665445 := by
  unfold tailWord_7313584
  simp only [CollatzResearch.WordTrace]
  refine ⟨133374161368070851774753903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177832215157427802366338537 133374161368070851774753903)
  ·
    refine ⟨200061242052106277662130855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133374161368070851774753903 200061242052106277662130855)
    ·
      refine ⟨300091863078159416493196283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200061242052106277662130855 300091863078159416493196283)
      ·
        refine ⟨450137794617239124739794425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300091863078159416493196283 450137794617239124739794425)
        ·
          refine ⟨337603345962929343554845819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450137794617239124739794425 337603345962929343554845819)
          ·
            refine ⟨506405018944394015332268729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337603345962929343554845819 506405018944394015332268729)
            ·
              refine ⟨379803764208295511499201547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506405018944394015332268729 379803764208295511499201547)
              ·
                refine ⟨569705646312443267248802321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379803764208295511499201547 569705646312443267248802321)
                ·
                  refine ⟨427279234734332450436601741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569705646312443267248802321 427279234734332450436601741)
                  ·
                    refine ⟨160229713025374668913725653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 427279234734332450436601741 160229713025374668913725653)
                    ·
                      refine ⟨3755383899032218802665445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160229713025374668913725653 3755383899032218802665445)
                      ·
                        rfl

theorem cell23_7313584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_7313584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313584 prefixEnd_7313584 := by exact prefixLift 7313584
  have htrace : WordTrace (prefixWord ++ tailWord_7313584) baseStart_7313584 baseEnd_7313584 := by
    simpa [prefixWord, tailWord_7313584, baseEnd_7313584] using wordTrace_append hprefix tailTrace_7313584
  have hstable : (prefixWord ++ tailWord_7313584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313584).length < 2 ^ (prefixWord ++ tailWord_7313584).sum := by decide
  have hdescent : baseEnd_7313584 < baseStart_7313584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313589 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7313589 : Nat := 118140960795 + 7313589 * 2 ^ 59
def prefixEnd_7313589 : Nat := 4983230072969 + 3 ^ 40 * 7313589 * 2
def baseEnd_7313589 : Nat := 3755386466435491283102923

theorem tailTrace_7313589 : CollatzResearch.WordTrace tailWord_7313589 prefixEnd_7313589 3755386466435491283102923 := by
  unfold tailWord_7313589
  simp only [CollatzResearch.WordTrace]
  refine ⟨266748505101123589403439821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177832336734082392935626547 266748505101123589403439821)
  ·
    refine ⟨100030689412921346026289933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266748505101123589403439821 100030689412921346026289933)
    ·
      refine ⟨37511508529845504759858725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100030689412921346026289933 37511508529845504759858725)
      ·
        refine ⟨7033407849346032142473511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37511508529845504759858725 7033407849346032142473511)
        ·
          refine ⟨10550111774019048213710267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033407849346032142473511 10550111774019048213710267)
          ·
            refine ⟨15825167661028572320565401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550111774019048213710267 15825167661028572320565401)
            ·
              refine ⟨11868875745771429240424051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15825167661028572320565401 11868875745771429240424051)
              ·
                refine ⟨17803313618657143860636077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11868875745771429240424051 17803313618657143860636077)
                ·
                  refine ⟨6676242606996428947738529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17803313618657143860636077 6676242606996428947738529)
                  ·
                    refine ⟨5007181955247321710803897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6676242606996428947738529 5007181955247321710803897)
                    ·
                      refine ⟨3755386466435491283102923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007181955247321710803897 3755386466435491283102923)
                      ·
                        rfl

theorem cell23_7313589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7313589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313589 prefixEnd_7313589 := by exact prefixLift 7313589
  have htrace : WordTrace (prefixWord ++ tailWord_7313589) baseStart_7313589 baseEnd_7313589 := by
    simpa [prefixWord, tailWord_7313589, baseEnd_7313589] using wordTrace_append hprefix tailTrace_7313589
  have hstable : (prefixWord ++ tailWord_7313589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313589).length < 2 ^ (prefixWord ++ tailWord_7313589).sum := by decide
  have hdescent : baseEnd_7313589 < baseStart_7313589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313602 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7313602 : Nat := 118140960795 + 7313602 * 2 ^ 59
def prefixEnd_7313602 : Nat := 4983230072969 + 3 ^ 40 * 7313602 * 2
def baseEnd_7313602 : Nat := 3755393141683999732240363

theorem tailTrace_7313602 : CollatzResearch.WordTrace tailWord_7313602 prefixEnd_7313602 3755393141683999732240363 := by
  unfold tailWord_7313602
  simp only [CollatzResearch.WordTrace]
  refine ⟨66687244812519123155915765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177832652833384328415775373 66687244812519123155915765)
  ·
    refine ⟨6251929201173667795867103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66687244812519123155915765 6251929201173667795867103)
    ·
      refine ⟨9377893801760501693800655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251929201173667795867103 9377893801760501693800655)
      ·
        refine ⟨14066840702640752540700983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377893801760501693800655 14066840702640752540700983)
        ·
          refine ⟨21100261053961128811051475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066840702640752540700983 21100261053961128811051475)
          ·
            refine ⟨31650391580941693216577213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21100261053961128811051475 31650391580941693216577213)
            ·
              refine ⟨11868896842853134956216455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31650391580941693216577213 11868896842853134956216455)
              ·
                refine ⟨17803345264279702434324683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11868896842853134956216455 17803345264279702434324683)
                ·
                  refine ⟨26705017896419553651487025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17803345264279702434324683 26705017896419553651487025)
                  ·
                    refine ⟨20028763422314665238615269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26705017896419553651487025 20028763422314665238615269)
                    ·
                      refine ⟨3755393141683999732240363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20028763422314665238615269 3755393141683999732240363)
                      ·
                        rfl

theorem cell23_7313602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7313602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313602 prefixEnd_7313602 := by exact prefixLift 7313602
  have htrace : WordTrace (prefixWord ++ tailWord_7313602) baseStart_7313602 baseEnd_7313602 := by
    simpa [prefixWord, tailWord_7313602, baseEnd_7313602] using wordTrace_append hprefix tailTrace_7313602
  have hstable : (prefixWord ++ tailWord_7313602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313602).length < 2 ^ (prefixWord ++ tailWord_7313602).sum := by decide
  have hdescent : baseEnd_7313602 < baseStart_7313602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313612 : List Nat := [2, 2, 1, 6, 2, 1, 2, 7]
def baseStart_7313612 : Nat := 118140960795 + 7313612 * 2 ^ 59
def prefixEnd_7313612 : Nat := 4983230072969 + 3 ^ 40 * 7313612 * 2
def baseEnd_7313612 : Nat := 139088825055205359004271

theorem tailTrace_7313612 : CollatzResearch.WordTrace tailWord_7313612 prefixEnd_7313612 139088825055205359004271 := by
  unfold tailWord_7313612
  simp only [CollatzResearch.WordTrace]
  refine ⟨133374671990020132165763545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177832895986693509554351393 133374671990020132165763545)
  ·
    refine ⟨100031003992515099124322659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133374671990020132165763545 100031003992515099124322659)
    ·
      refine ⟨150046505988772648686483989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100031003992515099124322659 150046505988772648686483989)
      ·
        refine ⟨7033429968223717907178937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150046505988772648686483989 7033429968223717907178937)
        ·
          refine ⟨5275072476167788430384203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7033429968223717907178937 5275072476167788430384203)
          ·
            refine ⟨7912608714251682645576305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275072476167788430384203 7912608714251682645576305)
            ·
              refine ⟨5934456535688761984182229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912608714251682645576305 5934456535688761984182229)
              ·
                refine ⟨139088825055205359004271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5934456535688761984182229 139088825055205359004271)
                ·
                  rfl

theorem cell23_7313612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 7].length) (baseStart_7313612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313612 prefixEnd_7313612 := by exact prefixLift 7313612
  have htrace : WordTrace (prefixWord ++ tailWord_7313612) baseStart_7313612 baseEnd_7313612 := by
    simpa [prefixWord, tailWord_7313612, baseEnd_7313612] using wordTrace_append hprefix tailTrace_7313612
  have hstable : (prefixWord ++ tailWord_7313612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313612).length < 2 ^ (prefixWord ++ tailWord_7313612).sum := by decide
  have hdescent : baseEnd_7313612 < baseStart_7313612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313615 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 1, 3, 2]
def baseStart_7313615 : Nat := 118140960795 + 7313615 * 2 ^ 59
def prefixEnd_7313615 : Nat := 4983230072969 + 3 ^ 40 * 7313615 * 2
def baseEnd_7313615 : Nat := 3755399816932508181377803

theorem tailTrace_7313615 : CollatzResearch.WordTrace tailWord_7313615 prefixEnd_7313615 3755399816932508181377803 := by
  unfold tailWord_7313615
  simp only [CollatzResearch.WordTrace]
  refine ⟨266749453399029395843886299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177832968932686263895924199 266749453399029395843886299)
  ·
    refine ⟨400124180098544093765829449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266749453399029395843886299 400124180098544093765829449)
    ·
      refine ⟨300093135073908070324372087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400124180098544093765829449 300093135073908070324372087)
      ·
        refine ⟨450139702610862105486558131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300093135073908070324372087 450139702610862105486558131)
        ·
          refine ⟨675209553916293158229837197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450139702610862105486558131 675209553916293158229837197)
          ·
            refine ⟨253203582718609934336188949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675209553916293158229837197 253203582718609934336188949)
            ·
              refine ⟨11868917939934840672008857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253203582718609934336188949 11868917939934840672008857)
              ·
                refine ⟨8901688454951130504006643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11868917939934840672008857 8901688454951130504006643)
                ·
                  refine ⟨13352532682426695756009965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8901688454951130504006643 13352532682426695756009965)
                  ·
                    refine ⟨5007199755910010908503737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13352532682426695756009965 5007199755910010908503737)
                    ·
                      refine ⟨3755399816932508181377803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007199755910010908503737 3755399816932508181377803)
                      ·
                        rfl

theorem cell23_7313615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 3, 2].length) (baseStart_7313615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313615 prefixEnd_7313615 := by exact prefixLift 7313615
  have htrace : WordTrace (prefixWord ++ tailWord_7313615) baseStart_7313615 baseEnd_7313615 := by
    simpa [prefixWord, tailWord_7313615, baseEnd_7313615] using wordTrace_append hprefix tailTrace_7313615
  have hstable : (prefixWord ++ tailWord_7313615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313615).length < 2 ^ (prefixWord ++ tailWord_7313615).sum := by decide
  have hdescent : baseEnd_7313615 < baseStart_7313615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313622 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7313622 : Nat := 118140960795 + 7313622 * 2 ^ 59
def prefixEnd_7313622 : Nat := 4983230072969 + 3 ^ 40 * 7313622 * 2
def baseEnd_7313622 : Nat := 3755403411297089653990271

theorem tailTrace_7313622 : CollatzResearch.WordTrace tailWord_7313622 prefixEnd_7313622 3755403411297089653990271 := by
  unfold tailWord_7313622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16671856794375252252461945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177833139140002690692927413 16671856794375252252461945)
  ·
    refine ⟨12503892595781439189346459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16671856794375252252461945 12503892595781439189346459)
    ·
      refine ⟨18755838893672158784019689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12503892595781439189346459 18755838893672158784019689)
      ·
        refine ⟨14066879170254119088014767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18755838893672158784019689 14066879170254119088014767)
        ·
          refine ⟨21100318755381178632022151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066879170254119088014767 21100318755381178632022151)
          ·
            refine ⟨31650478133071767948033227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21100318755381178632022151 31650478133071767948033227)
            ·
              refine ⟨47475717199607651922049841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31650478133071767948033227 47475717199607651922049841)
              ·
                refine ⟨35606787899705738941537381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47475717199607651922049841 35606787899705738941537381)
                ·
                  refine ⟨6676272731194826051538259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35606787899705738941537381 6676272731194826051538259)
                  ·
                    refine ⟨10014409096792239077307389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6676272731194826051538259 10014409096792239077307389)
                    ·
                      refine ⟨3755403411297089653990271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10014409096792239077307389 3755403411297089653990271)
                      ·
                        rfl

theorem cell23_7313622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7313622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313622 prefixEnd_7313622 := by exact prefixLift 7313622
  have htrace : WordTrace (prefixWord ++ tailWord_7313622) baseStart_7313622 baseEnd_7313622 := by
    simpa [prefixWord, tailWord_7313622, baseEnd_7313622] using wordTrace_append hprefix tailTrace_7313622
  have hstable : (prefixWord ++ tailWord_7313622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313622).length < 2 ^ (prefixWord ++ tailWord_7313622).sum := by decide
  have hdescent : baseEnd_7313622 < baseStart_7313622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313631 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 3]
def baseStart_7313631 : Nat := 118140960795 + 7313631 * 2 ^ 59
def prefixEnd_7313631 : Nat := 4983230072969 + 3 ^ 40 * 7313631 * 2
def baseEnd_7313631 : Nat := 3755408032622980118777729

theorem tailTrace_7313631 : CollatzResearch.WordTrace tailWord_7313631 prefixEnd_7313631 3755408032622980118777729 := by
  unfold tailWord_7313631
  simp only [CollatzResearch.WordTrace]
  refine ⟨266750036966971430576468747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177833357977980953717645831 266750036966971430576468747)
  ·
    refine ⟨400125055450457145864703121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266750036966971430576468747 400125055450457145864703121)
    ·
      refine ⟨300093791587842859398527341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400125055450457145864703121 300093791587842859398527341)
      ·
        refine ⟨112535171845441072274447753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300093791587842859398527341 112535171845441072274447753)
        ·
          refine ⟨84401378884080804205835815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112535171845441072274447753 84401378884080804205835815)
          ·
            refine ⟨126602068326121206308753723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84401378884080804205835815 126602068326121206308753723)
            ·
              refine ⟨189903102489181809463130585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126602068326121206308753723 189903102489181809463130585)
              ·
                refine ⟨142427326866886357097347939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189903102489181809463130585 142427326866886357097347939)
                ·
                  refine ⟨213640990300329535646021909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142427326866886357097347939 213640990300329535646021909)
                  ·
                    refine ⟨10014421420327946983407277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213640990300329535646021909 10014421420327946983407277)
                    ·
                      refine ⟨3755408032622980118777729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10014421420327946983407277 3755408032622980118777729)
                      ·
                        rfl

theorem cell23_7313631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_7313631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313631 prefixEnd_7313631 := by exact prefixLift 7313631
  have htrace : WordTrace (prefixWord ++ tailWord_7313631) baseStart_7313631 baseEnd_7313631 := by
    simpa [prefixWord, tailWord_7313631, baseEnd_7313631] using wordTrace_append hprefix tailTrace_7313631
  have hstable : (prefixWord ++ tailWord_7313631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313631).length < 2 ^ (prefixWord ++ tailWord_7313631).sum := by decide
  have hdescent : baseEnd_7313631 < baseStart_7313631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313691 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5]
def baseStart_7313691 : Nat := 118140960795 + 7313691 * 2 ^ 59
def prefixEnd_7313691 : Nat := 4983230072969 + 3 ^ 40 * 7313691 * 2
def baseEnd_7313691 : Nat := 3755438841462249884027453

theorem tailTrace_7313691 : CollatzResearch.WordTrace tailWord_7313691 prefixEnd_7313691 3755438841462249884027453 := by
  unfold tailWord_7313691
  simp only [CollatzResearch.WordTrace]
  refine ⟨266752225346754060823652927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177834816897836040549101951 266752225346754060823652927)
  ·
    refine ⟨400128338020131091235479391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266752225346754060823652927 400128338020131091235479391)
    ·
      refine ⟨600192507030196636853219087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400128338020131091235479391 600192507030196636853219087)
      ·
        refine ⟨900288760545294955279828631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600192507030196636853219087 900288760545294955279828631)
        ·
          refine ⟨1350433140817942432919742947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900288760545294955279828631 1350433140817942432919742947)
          ·
            refine ⟨2025649711226913649379614421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350433140817942432919742947 2025649711226913649379614421)
            ·
              refine ⟨47476165106880788657334713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2025649711226913649379614421 47476165106880788657334713)
              ·
                refine ⟨35607123830160591493001035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47476165106880788657334713 35607123830160591493001035)
                ·
                  refine ⟨53410685745240887239501553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35607123830160591493001035 53410685745240887239501553)
                  ·
                    refine ⟨40058014308930665429626165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53410685745240887239501553 40058014308930665429626165)
                    ·
                      refine ⟨3755438841462249884027453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40058014308930665429626165 3755438841462249884027453)
                      ·
                        rfl

theorem cell23_7313691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_7313691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313691 prefixEnd_7313691 := by exact prefixLift 7313691
  have htrace : WordTrace (prefixWord ++ tailWord_7313691) baseStart_7313691 baseEnd_7313691 := by
    simpa [prefixWord, tailWord_7313691, baseEnd_7313691] using wordTrace_append hprefix tailTrace_7313691
  have hstable : (prefixWord ++ tailWord_7313691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313691).length < 2 ^ (prefixWord ++ tailWord_7313691).sum := by decide
  have hdescent : baseEnd_7313691 < baseStart_7313691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313748 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_7313748 : Nat := 118140960795 + 7313748 * 2 ^ 59
def prefixEnd_7313748 : Nat := 4983230072969 + 3 ^ 40 * 7313748 * 2
def baseEnd_7313748 : Nat := 3755468109859556161014691

theorem tailTrace_7313748 : CollatzResearch.WordTrace tailWord_7313748 prefixEnd_7313748 3755468109859556161014691 := by
  unfold tailWord_7313748
  simp only [CollatzResearch.WordTrace]
  refine ⟨133377152153773779779238949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177836202871698373038985265 133377152153773779779238949)
  ·
    refine ⟨25008216028832583708607303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133377152153773779779238949 25008216028832583708607303)
    ·
      refine ⟨37512324043248875562910955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25008216028832583708607303 37512324043248875562910955)
      ·
        refine ⟨56268486064873313344366433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37512324043248875562910955 56268486064873313344366433)
        ·
          refine ⟨42201364548654985008274825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56268486064873313344366433 42201364548654985008274825)
          ·
            refine ⟨31651023411491238756206119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42201364548654985008274825 31651023411491238756206119)
            ·
              refine ⟨47476535117236858134309179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31651023411491238756206119 47476535117236858134309179)
              ·
                refine ⟨71214802675855287201463769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47476535117236858134309179 71214802675855287201463769)
                ·
                  refine ⟨53411102006891465401097827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71214802675855287201463769 53411102006891465401097827)
                  ·
                    refine ⟨80116653010337198101646741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53411102006891465401097827 80116653010337198101646741)
                    ·
                      refine ⟨3755468109859556161014691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80116653010337198101646741 3755468109859556161014691)
                      ·
                        rfl

theorem cell23_7313748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_7313748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313748 prefixEnd_7313748 := by exact prefixLift 7313748
  have htrace : WordTrace (prefixWord ++ tailWord_7313748) baseStart_7313748 baseEnd_7313748 := by
    simpa [prefixWord, tailWord_7313748, baseEnd_7313748] using wordTrace_append hprefix tailTrace_7313748
  have hstable : (prefixWord ++ tailWord_7313748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313748).length < 2 ^ (prefixWord ++ tailWord_7313748).sum := by decide
  have hdescent : baseEnd_7313748 < baseStart_7313748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313762 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_7313762 : Nat := 118140960795 + 7313762 * 2 ^ 59
def prefixEnd_7313762 : Nat := 4983230072969 + 3 ^ 40 * 7313762 * 2
def baseEnd_7313762 : Nat := 1251825099529573035413209

theorem tailTrace_7313762 : CollatzResearch.WordTrace tailWord_7313762 prefixEnd_7313762 1251825099529573035413209 := by
  unfold tailWord_7313762
  simp only [CollatzResearch.WordTrace]
  refine ⟨66688703732374209987371885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177836543286331226632991693 66688703732374209987371885)
  ·
    refine ⟨25008263899640328745264457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66688703732374209987371885 25008263899640328745264457)
    ·
      refine ⟨18756197924730246558948343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25008263899640328745264457 18756197924730246558948343)
      ·
        refine ⟨28134296887095369838422515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18756197924730246558948343 28134296887095369838422515)
        ·
          refine ⟨42201445330643054757633773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28134296887095369838422515 42201445330643054757633773)
          ·
            refine ⟨15825541998991145534112665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42201445330643054757633773 15825541998991145534112665)
            ·
              refine ⟨11869156499243359150584499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15825541998991145534112665 11869156499243359150584499)
              ·
                refine ⟨17803734748865038725876749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11869156499243359150584499 17803734748865038725876749)
                ·
                  refine ⟨6676400530824389522203781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17803734748865038725876749 6676400530824389522203781)
                  ·
                    refine ⟨1251825099529573035413209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676400530824389522203781 1251825099529573035413209)
                    ·
                      rfl

theorem cell23_7313762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_7313762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313762 prefixEnd_7313762 := by exact prefixLift 7313762
  have htrace : WordTrace (prefixWord ++ tailWord_7313762) baseStart_7313762 baseEnd_7313762 := by
    simpa [prefixWord, tailWord_7313762, baseEnd_7313762] using wordTrace_append hprefix tailTrace_7313762
  have hstable : (prefixWord ++ tailWord_7313762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313762).length < 2 ^ (prefixWord ++ tailWord_7313762).sum := by decide
  have hdescent : baseEnd_7313762 < baseStart_7313762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313842 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_7313842 : Nat := 118140960795 + 7313842 * 2 ^ 59
def prefixEnd_7313842 : Nat := 4983230072969 + 3 ^ 40 * 7313842 * 2
def baseEnd_7313842 : Nat := 3755516377041078793239259

theorem tailTrace_7313842 : CollatzResearch.WordTrace tailWord_7313842 prefixEnd_7313842 3755516377041078793239259 := by
  unfold tailWord_7313842
  simp only [CollatzResearch.WordTrace]
  refine ⟨66689433192301753403099945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177838488512804675741599853 66689433192301753403099945)
  ·
    refine ⟨50017074894226315052324959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66689433192301753403099945 50017074894226315052324959)
    ·
      refine ⟨75025612341339472578487439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50017074894226315052324959 75025612341339472578487439)
      ·
        refine ⟨112538418512009208867731159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75025612341339472578487439 112538418512009208867731159)
        ·
          refine ⟨168807627768013813301596739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112538418512009208867731159 168807627768013813301596739)
          ·
            refine ⟨253211441652020719952395109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168807627768013813301596739 253211441652020719952395109)
            ·
              refine ⟨47477145309753884991074083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253211441652020719952395109 47477145309753884991074083)
              ·
                refine ⟨71215717964630827486611125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47477145309753884991074083 71215717964630827486611125)
                ·
                  refine ⟨6676473559184140076869793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71215717964630827486611125 6676473559184140076869793)
                  ·
                    refine ⟨5007355169388105057652345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6676473559184140076869793 5007355169388105057652345)
                    ·
                      refine ⟨3755516377041078793239259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007355169388105057652345 3755516377041078793239259)
                      ·
                        rfl

theorem cell23_7313842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_7313842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313842 prefixEnd_7313842 := by exact prefixLift 7313842
  have htrace : WordTrace (prefixWord ++ tailWord_7313842) baseStart_7313842 baseEnd_7313842 := by
    simpa [prefixWord, tailWord_7313842, baseEnd_7313842] using wordTrace_append hprefix tailTrace_7313842
  have hstable : (prefixWord ++ tailWord_7313842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313842).length < 2 ^ (prefixWord ++ tailWord_7313842).sum := by decide
  have hdescent : baseEnd_7313842 < baseStart_7313842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313859 : List Nat := [1, 1, 1, 3, 1, 1, 3, 7, 1, 2, 2]
def baseStart_7313859 : Nat := 118140960795 + 7313859 * 2 ^ 59
def prefixEnd_7313859 : Nat := 4983230072969 + 3 ^ 40 * 7313859 * 2
def baseEnd_7313859 : Nat := 3755525106212205226726681

theorem tailTrace_7313859 : CollatzResearch.WordTrace tailWord_7313859 prefixEnd_7313859 3755525106212205226726681 := by
  unfold tailWord_7313859
  simp only [CollatzResearch.WordTrace]
  refine ⟨266758352810145425515768631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177838901873430283677179087 266758352810145425515768631)
  ·
    refine ⟨400137529215218138273652947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266758352810145425515768631 400137529215218138273652947)
    ·
      refine ⟨600206293822827207410479421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400137529215218138273652947 600206293822827207410479421)
      ·
        refine ⟨225077360183560202778929783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600206293822827207410479421 225077360183560202778929783)
        ·
          refine ⟨337616040275340304168394675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225077360183560202778929783 337616040275340304168394675)
          ·
            refine ⟨506424060413010456252592013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337616040275340304168394675 506424060413010456252592013)
            ·
              refine ⟨189909022654878921094722005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506424060413010456252592013 189909022654878921094722005)
              ·
                refine ⟨4450992718473724713157547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 189909022654878921094722005 4450992718473724713157547)
                ·
                  refine ⟨6676489077710587069736321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450992718473724713157547 6676489077710587069736321)
                  ·
                    refine ⟨5007366808282940302302241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6676489077710587069736321 5007366808282940302302241)
                    ·
                      refine ⟨3755525106212205226726681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007366808282940302302241 3755525106212205226726681)
                      ·
                        rfl

theorem cell23_7313859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_7313859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313859 prefixEnd_7313859 := by exact prefixLift 7313859
  have htrace : WordTrace (prefixWord ++ tailWord_7313859) baseStart_7313859 baseEnd_7313859 := by
    simpa [prefixWord, tailWord_7313859, baseEnd_7313859] using wordTrace_append hprefix tailTrace_7313859
  have hstable : (prefixWord ++ tailWord_7313859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313859).length < 2 ^ (prefixWord ++ tailWord_7313859).sum := by decide
  have hdescent : baseEnd_7313859 < baseStart_7313859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313875 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 3]
def baseStart_7313875 : Nat := 118140960795 + 7313875 * 2 ^ 59
def prefixEnd_7313875 : Nat := 4983230072969 + 3 ^ 40 * 7313875 * 2
def baseEnd_7313875 : Nat := 3755533321902677164126607

theorem tailTrace_7313875 : CollatzResearch.WordTrace tailWord_7313875 prefixEnd_7313875 3755533321902677164126607 := by
  unfold tailWord_7313875
  simp only [CollatzResearch.WordTrace]
  refine ⟨266758936378087460248351079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177839290918724973498900719 266758936378087460248351079)
  ·
    refine ⟨400138404567131190372526619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266758936378087460248351079 400138404567131190372526619)
    ·
      refine ⟨600207606850696785558789929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400138404567131190372526619 600207606850696785558789929)
      ·
        refine ⟨450155705138022589169092447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600207606850696785558789929 450155705138022589169092447)
        ·
          refine ⟨675233557707033883753638671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450155705138022589169092447 675233557707033883753638671)
          ·
            refine ⟨1012850336560550825630458007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675233557707033883753638671 1012850336560550825630458007)
            ·
              refine ⟨1519275504840826238445687011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012850336560550825630458007 1519275504840826238445687011)
              ·
                refine ⟨2278913257261239357668530517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519275504840826238445687011 2278913257261239357668530517)
                ·
                  refine ⟨6676503683382537180669523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2278913257261239357668530517 6676503683382537180669523)
                  ·
                    refine ⟨10014755525073805771004285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6676503683382537180669523 10014755525073805771004285)
                    ·
                      refine ⟨3755533321902677164126607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10014755525073805771004285 3755533321902677164126607)
                      ·
                        rfl

theorem cell23_7313875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 3].length) (baseStart_7313875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313875 prefixEnd_7313875 := by exact prefixLift 7313875
  have htrace : WordTrace (prefixWord ++ tailWord_7313875) baseStart_7313875 baseEnd_7313875 := by
    simpa [prefixWord, tailWord_7313875, baseEnd_7313875] using wordTrace_append hprefix tailTrace_7313875
  have hstable : (prefixWord ++ tailWord_7313875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313875).length < 2 ^ (prefixWord ++ tailWord_7313875).sum := by decide
  have hdescent : baseEnd_7313875 < baseStart_7313875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313943 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7313943 : Nat := 118140960795 + 7313943 * 2 ^ 59
def prefixEnd_7313943 : Nat := 4983230072969 + 3 ^ 40 * 7313943 * 2
def baseEnd_7313943 : Nat := 3755568238587182898076295

theorem tailTrace_7313943 : CollatzResearch.WordTrace tailWord_7313943 prefixEnd_7313943 3755568238587182898076295 := by
  unfold tailWord_7313943
  simp only [CollatzResearch.WordTrace]
  refine ⟨266761416541841107861826483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177840944361227405241217655 266761416541841107861826483)
  ·
    refine ⟨400142124812761661792739725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266761416541841107861826483 400142124812761661792739725)
    ·
      refine ⟨150053296804785623172277397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400142124812761661792739725 150053296804785623172277397)
      ·
        refine ⟨7033748287724326086200503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150053296804785623172277397 7033748287724326086200503)
        ·
          refine ⟨10550622431586489129300755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033748287724326086200503 10550622431586489129300755)
          ·
            refine ⟨15825933647379733693951133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550622431586489129300755 15825933647379733693951133)
            ·
              refine ⟨5934725117767400135231675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15825933647379733693951133 5934725117767400135231675)
              ·
                refine ⟨8902087676651100202847513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934725117767400135231675 8902087676651100202847513)
                ·
                  refine ⟨6676565757488325152135635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8902087676651100202847513 6676565757488325152135635)
                  ·
                    refine ⟨10014848636232487728203453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6676565757488325152135635 10014848636232487728203453)
                    ·
                      refine ⟨3755568238587182898076295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10014848636232487728203453 3755568238587182898076295)
                      ·
                        rfl

theorem cell23_7313943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7313943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313943 prefixEnd_7313943 := by exact prefixLift 7313943
  have htrace : WordTrace (prefixWord ++ tailWord_7313943) baseStart_7313943 baseEnd_7313943 := by
    simpa [prefixWord, tailWord_7313943, baseEnd_7313943] using wordTrace_append hprefix tailTrace_7313943
  have hstable : (prefixWord ++ tailWord_7313943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313943).length < 2 ^ (prefixWord ++ tailWord_7313943).sum := by decide
  have hdescent : baseEnd_7313943 < baseStart_7313943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313949 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_7313949 : Nat := 118140960795 + 7313949 * 2 ^ 59
def prefixEnd_7313949 : Nat := 4983230072969 + 3 ^ 40 * 7313949 * 2
def baseEnd_7313949 : Nat := 3755571319471109874601267

theorem tailTrace_7313949 : CollatzResearch.WordTrace tailWord_7313949 prefixEnd_7313949 3755571319471109874601267 := by
  unfold tailWord_7313949
  simp only [CollatzResearch.WordTrace]
  refine ⟨266761635379819370886544901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177841090253212913924363267 266761635379819370886544901)
  ·
    refine ⟨50017806633716132041227169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266761635379819370886544901 50017806633716132041227169)
    ·
      refine ⟨37513354975287099030920377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50017806633716132041227169 37513354975287099030920377)
      ·
        refine ⟨28135016231465324273190283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37513354975287099030920377 28135016231465324273190283)
        ·
          refine ⟨42202524347197986409785425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28135016231465324273190283 42202524347197986409785425)
          ·
            refine ⟨31651893260398489807339069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42202524347197986409785425 31651893260398489807339069)
            ·
              refine ⟨11869459972649433677752151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31651893260398489807339069 11869459972649433677752151)
              ·
                refine ⟨17804189958974150516628227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11869459972649433677752151 17804189958974150516628227)
                ·
                  refine ⟨26706284938461225774942341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17804189958974150516628227 26706284938461225774942341)
                  ·
                    refine ⟨5007428425961479832801689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26706284938461225774942341 5007428425961479832801689)
                    ·
                      refine ⟨3755571319471109874601267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007428425961479832801689 3755571319471109874601267)
                      ·
                        rfl

theorem cell23_7313949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_7313949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313949 prefixEnd_7313949 := by exact prefixLift 7313949
  have htrace : WordTrace (prefixWord ++ tailWord_7313949) baseStart_7313949 baseEnd_7313949 := by
    simpa [prefixWord, tailWord_7313949, baseEnd_7313949] using wordTrace_append hprefix tailTrace_7313949
  have hstable : (prefixWord ++ tailWord_7313949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313949).length < 2 ^ (prefixWord ++ tailWord_7313949).sum := by decide
  have hdescent : baseEnd_7313949 < baseStart_7313949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313955 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 7]
def baseStart_7313955 : Nat := 118140960795 + 7313955 * 2 ^ 59
def prefixEnd_7313955 : Nat := 4983230072969 + 3 ^ 40 * 7313955 * 2
def baseEnd_7313955 : Nat := 417286044483892983458471

theorem tailTrace_7313955 : CollatzResearch.WordTrace tailWord_7313955 prefixEnd_7313955 417286044483892983458471 := by
  unfold tailWord_7313955
  simp only [CollatzResearch.WordTrace]
  refine ⟨266761854217797633911263319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177841236145198422607508879 266761854217797633911263319)
  ·
    refine ⟨400142781326696450866894979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266761854217797633911263319 400142781326696450866894979)
    ·
      refine ⟨600214171990044676300342469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400142781326696450866894979 600214171990044676300342469)
      ·
        refine ⟨112540157248133376806314213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 600214171990044676300342469 112540157248133376806314213)
        ·
          refine ⟨21101279484025008151183915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112540157248133376806314213 21101279484025008151183915)
          ·
            refine ⟨31651919226037512226775873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21101279484025008151183915 31651919226037512226775873)
            ·
              refine ⟨23738939419528134170081905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31651919226037512226775873 23738939419528134170081905)
              ·
                refine ⟨17804204564646100627561429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23738939419528134170081905 17804204564646100627561429)
                ·
                  refine ⟨417286044483892983458471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17804204564646100627561429 417286044483892983458471)
                  ·
                    rfl

theorem cell23_7313955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 7].length) (baseStart_7313955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313955 prefixEnd_7313955 := by exact prefixLift 7313955
  have htrace : WordTrace (prefixWord ++ tailWord_7313955) baseStart_7313955 baseEnd_7313955 := by
    simpa [prefixWord, tailWord_7313955, baseEnd_7313955] using wordTrace_append hprefix tailTrace_7313955
  have hstable : (prefixWord ++ tailWord_7313955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313955).length < 2 ^ (prefixWord ++ tailWord_7313955).sum := by decide
  have hdescent : baseEnd_7313955 < baseStart_7313955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7313989 : List Nat := [1, 3, 1, 1, 1, 6, 3, 2, 5]
def baseStart_7313989 : Nat := 118140960795 + 7313989 * 2 ^ 59
def prefixEnd_7313989 : Nat := 4983230072969 + 3 ^ 40 * 7313989 * 2
def baseEnd_7313989 : Nat := 417287984299698857566787

theorem tailTrace_7313989 : CollatzResearch.WordTrace tailWord_7313989 prefixEnd_7313989 417287984299698857566787 := by
  unfold tailWord_7313989
  simp only [CollatzResearch.WordTrace]
  refine ⟨266763094299674457718001021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177842062866449638478667347 266763094299674457718001021)
  ·
    refine ⟨100036160362377921644250383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266763094299674457718001021 100036160362377921644250383)
    ·
      refine ⟨150054240543566882466375575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100036160362377921644250383 150054240543566882466375575)
      ·
        refine ⟨225081360815350323699563363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150054240543566882466375575 225081360815350323699563363)
        ·
          refine ⟨337622041223025485549345045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225081360815350323699563363 337622041223025485549345045)
          ·
            refine ⟨15826033182329319635125549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 337622041223025485549345045 15826033182329319635125549)
            ·
              refine ⟨5934762443373494863172081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15826033182329319635125549 5934762443373494863172081)
              ·
                refine ⟨4451071832530121147379061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934762443373494863172081 4451071832530121147379061)
                ·
                  refine ⟨417287984299698857566787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451071832530121147379061 417287984299698857566787)
                  ·
                    rfl

theorem cell23_7313989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_7313989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7313989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7313989 prefixEnd_7313989 := by exact prefixLift 7313989
  have htrace : WordTrace (prefixWord ++ tailWord_7313989) baseStart_7313989 baseEnd_7313989 := by
    simpa [prefixWord, tailWord_7313989, baseEnd_7313989] using wordTrace_append hprefix tailTrace_7313989
  have hstable : (prefixWord ++ tailWord_7313989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7313989).length < 2 ^ (prefixWord ++ tailWord_7313989).sum := by decide
  have hdescent : baseEnd_7313989 < baseStart_7313989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7313989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314005 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7314005 : Nat := 118140960795 + 7314005 * 2 ^ 59
def prefixEnd_7314005 : Nat := 4983230072969 + 3 ^ 40 * 7314005 * 2
def baseEnd_7314005 : Nat := 3755600074387761655501009

theorem tailTrace_7314005 : CollatzResearch.WordTrace tailWord_7314005 prefixEnd_7314005 3755600074387761655501009 := by
  unfold tailWord_7314005
  simp only [CollatzResearch.WordTrace]
  refine ⟨266763677867616492450583469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177842451911744328300388979 266763677867616492450583469)
  ·
    refine ⟨100036379200356184668968801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266763677867616492450583469 100036379200356184668968801)
    ·
      refine ⟨75027284400267138501726601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100036379200356184668968801 75027284400267138501726601)
      ·
        refine ⟨56270463300200353876294951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75027284400267138501726601 56270463300200353876294951)
        ·
          refine ⟨84405694950300530814442427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56270463300200353876294951 84405694950300530814442427)
          ·
            refine ⟨126608542425450796221663641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84405694950300530814442427 126608542425450796221663641)
            ·
              refine ⟨94956406819088097166247731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126608542425450796221663641 94956406819088097166247731)
              ·
                refine ⟨142434610228632145749371597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94956406819088097166247731 142434610228632145749371597)
                ·
                  refine ⟨53412978835737054656014349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142434610228632145749371597 53412978835737054656014349)
                  ·
                    refine ⟨20029867063401395496005381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53412978835737054656014349 20029867063401395496005381)
                    ·
                      refine ⟨3755600074387761655501009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20029867063401395496005381 3755600074387761655501009)
                      ·
                        rfl

theorem cell23_7314005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7314005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314005 prefixEnd_7314005 := by exact prefixLift 7314005
  have htrace : WordTrace (prefixWord ++ tailWord_7314005) baseStart_7314005 baseEnd_7314005 := by
    simpa [prefixWord, tailWord_7314005, baseEnd_7314005] using wordTrace_append hprefix tailTrace_7314005
  have hstable : (prefixWord ++ tailWord_7314005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314005).length < 2 ^ (prefixWord ++ tailWord_7314005).sum := by decide
  have hdescent : baseEnd_7314005 < baseStart_7314005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314062 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_7314062 : Nat := 118140960795 + 7314062 * 2 ^ 59
def prefixEnd_7314062 : Nat := 4983230072969 + 3 ^ 40 * 7314062 * 2
def baseEnd_7314062 : Nat := 417292149198340881387583

theorem tailTrace_7314062 : CollatzResearch.WordTrace tailWord_7314062 prefixEnd_7314062 417292149198340881387583 := by
  unfold tailWord_7314062
  simp only [CollatzResearch.WordTrace]
  refine ⟨33345719603551248898176055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177843837885606660790272293 33345719603551248898176055)
  ·
    refine ⟨50018579405326873347264083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33345719603551248898176055 50018579405326873347264083)
    ·
      refine ⟨75027869107990310020896125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50018579405326873347264083 75027869107990310020896125)
      ·
        refine ⟨28135450915496366257836047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75027869107990310020896125 28135450915496366257836047)
        ·
          refine ⟨42203176373244549386754071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28135450915496366257836047 42203176373244549386754071)
          ·
            refine ⟨63304764559866824080131107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42203176373244549386754071 63304764559866824080131107)
            ·
              refine ⟨94957146839800236120196661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63304764559866824080131107 94957146839800236120196661)
              ·
                refine ⟨8902232516231272136268437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94957146839800236120196661 8902232516231272136268437)
                ·
                  refine ⟨417292149198340881387583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8902232516231272136268437 417292149198340881387583)
                  ·
                    rfl

theorem cell23_7314062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_7314062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314062 prefixEnd_7314062 := by exact prefixLift 7314062
  have htrace : WordTrace (prefixWord ++ tailWord_7314062) baseStart_7314062 baseEnd_7314062 := by
    simpa [prefixWord, tailWord_7314062, baseEnd_7314062] using wordTrace_append hprefix tailTrace_7314062
  have hstable : (prefixWord ++ tailWord_7314062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314062).length < 2 ^ (prefixWord ++ tailWord_7314062).sum := by decide
  have hdescent : baseEnd_7314062 < baseStart_7314062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314076 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7314076 : Nat := 118140960795 + 7314076 * 2 ^ 59
def prefixEnd_7314076 : Nat := 4983230072969 + 3 ^ 40 * 7314076 * 2
def baseEnd_7314076 : Nat := 3755636531514230877713183

theorem tailTrace_7314076 : CollatzResearch.WordTrace tailWord_7314076 prefixEnd_7314076 3755636531514230877713183 := by
  unfold tailWord_7314076
  simp only [CollatzResearch.WordTrace]
  refine ⟨133383133725179635788209041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177844178300239514384278721 133383133725179635788209041)
  ·
    refine ⟨100037350293884726841156781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133383133725179635788209041 100037350293884726841156781)
    ·
      refine ⟨37514006360206772565433793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100037350293884726841156781 37514006360206772565433793)
      ·
        refine ⟨28135504770155079424075345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37514006360206772565433793 28135504770155079424075345)
        ·
          refine ⟨21101628577616309568056509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28135504770155079424075345 21101628577616309568056509)
          ·
            refine ⟨7913110716606116088021191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21101628577616309568056509 7913110716606116088021191)
            ·
              refine ⟨11869666074909174132031787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913110716606116088021191 11869666074909174132031787)
              ·
                refine ⟨17804499112363761198047681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11869666074909174132031787 17804499112363761198047681)
                ·
                  refine ⟨13353374334272820898535761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17804499112363761198047681 13353374334272820898535761)
                  ·
                    refine ⟨10015030750704615673901821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13353374334272820898535761 10015030750704615673901821)
                    ·
                      refine ⟨3755636531514230877713183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10015030750704615673901821 3755636531514230877713183)
                      ·
                        rfl

theorem cell23_7314076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7314076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314076 prefixEnd_7314076 := by exact prefixLift 7314076
  have htrace : WordTrace (prefixWord ++ tailWord_7314076) baseStart_7314076 baseEnd_7314076 := by
    simpa [prefixWord, tailWord_7314076, baseEnd_7314076] using wordTrace_append hprefix tailTrace_7314076
  have hstable : (prefixWord ++ tailWord_7314076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314076).length < 2 ^ (prefixWord ++ tailWord_7314076).sum := by decide
  have hdescent : baseEnd_7314076 < baseStart_7314076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314085 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_7314085 : Nat := 118140960795 + 7314085 * 2 ^ 59
def prefixEnd_7314085 : Nat := 4983230072969 + 3 ^ 40 * 7314085 * 2
def baseEnd_7314085 : Nat := 3755641152840121342500641

theorem tailTrace_7314085 : CollatzResearch.WordTrace tailWord_7314085 prefixEnd_7314085 3755641152840121342500641 := by
  unfold tailWord_7314085
  simp only [CollatzResearch.WordTrace]
  refine ⟨266766595707326666113495709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177844397138217777408997139 266766595707326666113495709)
  ·
    refine ⟨100037473390247499792560891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266766595707326666113495709 100037473390247499792560891)
    ·
      refine ⟨150056210085371249688841337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100037473390247499792560891 150056210085371249688841337)
      ·
        refine ⟨112542157564028437266631003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150056210085371249688841337 112542157564028437266631003)
        ·
          refine ⟨168813236346042655899946505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112542157564028437266631003 168813236346042655899946505)
          ·
            refine ⟨126609927259531991924959879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168813236346042655899946505 126609927259531991924959879)
            ·
              refine ⟨189914890889297987887439819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126609927259531991924959879 189914890889297987887439819)
              ·
                refine ⟨284872336333946981831159729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189914890889297987887439819 284872336333946981831159729)
                ·
                  refine ⟨213654252250460236373369797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284872336333946981831159729 213654252250460236373369797)
                  ·
                    refine ⟨40060172296961294320006837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213654252250460236373369797 40060172296961294320006837)
                    ·
                      refine ⟨3755641152840121342500641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40060172296961294320006837 3755641152840121342500641)
                      ·
                        rfl

theorem cell23_7314085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_7314085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314085 prefixEnd_7314085 := by exact prefixLift 7314085
  have htrace : WordTrace (prefixWord ++ tailWord_7314085) baseStart_7314085 baseEnd_7314085 := by
    simpa [prefixWord, tailWord_7314085, baseEnd_7314085] using wordTrace_append hprefix tailTrace_7314085
  have hstable : (prefixWord ++ tailWord_7314085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314085).length < 2 ^ (prefixWord ++ tailWord_7314085).sum := by decide
  have hdescent : baseEnd_7314085 < baseStart_7314085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314106 : List Nat := [3, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3]
def baseStart_7314106 : Nat := 118140960795 + 7314106 * 2 ^ 59
def prefixEnd_7314106 : Nat := 4983230072969 + 3 ^ 40 * 7314106 * 2
def baseEnd_7314106 : Nat := 3755651935933865760338045

theorem tailTrace_7314106 : CollatzResearch.WordTrace tailWord_7314106 prefixEnd_7314106 3755651935933865760338045 := by
  unfold tailWord_7314106
  simp only [CollatzResearch.WordTrace]
  refine ⟨66691840410062646675002543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177844907760167057800006781 66691840410062646675002543)
  ·
    refine ⟨100037760615093970012503815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66691840410062646675002543 100037760615093970012503815)
    ·
      refine ⟨150056640922640955018755723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100037760615093970012503815 150056640922640955018755723)
      ·
        refine ⟨225084961383961432528133585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150056640922640955018755723 225084961383961432528133585)
        ·
          refine ⟨168813721037971074396100189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225084961383961432528133585 168813721037971074396100189)
          ·
            refine ⟨63305145389239152898537571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168813721037971074396100189 63305145389239152898537571)
            ·
              refine ⟨94957718083858729347806357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63305145389239152898537571 94957718083858729347806357)
              ·
                refine ⟨4451143035180877938178423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94957718083858729347806357 4451143035180877938178423)
                ·
                  refine ⟨6676714552771316907267635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451143035180877938178423 6676714552771316907267635)
                  ·
                    refine ⟨10015071829156975360901453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6676714552771316907267635 10015071829156975360901453)
                    ·
                      refine ⟨3755651935933865760338045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10015071829156975360901453 3755651935933865760338045)
                      ·
                        rfl

theorem cell23_7314106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_7314106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314106 prefixEnd_7314106 := by exact prefixLift 7314106
  have htrace : WordTrace (prefixWord ++ tailWord_7314106) baseStart_7314106 baseEnd_7314106 := by
    simpa [prefixWord, tailWord_7314106, baseEnd_7314106] using wordTrace_append hprefix tailTrace_7314106
  have hstable : (prefixWord ++ tailWord_7314106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314106).length < 2 ^ (prefixWord ++ tailWord_7314106).sum := by decide
  have hdescent : baseEnd_7314106 < baseStart_7314106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314113 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 6]
def baseStart_7314113 : Nat := 118140960795 + 7314113 * 2 ^ 59
def prefixEnd_7314113 : Nat := 4983230072969 + 3 ^ 40 * 7314113 * 2
def baseEnd_7314113 : Nat := 417295058922049692550057

theorem tailTrace_7314113 : CollatzResearch.WordTrace tailWord_7314113 prefixEnd_7314113 417295058922049692550057 := by
  unfold tailWord_7314113
  simp only [CollatzResearch.WordTrace]
  refine ⟨266767616951225226895514993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177845077967483484597009995 266767616951225226895514993)
  ·
    refine ⟨200075712713418920171636245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266767616951225226895514993 200075712713418920171636245)
    ·
      refine ⟨9378549033441511883045449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 200075712713418920171636245 9378549033441511883045449)
      ·
        refine ⟨7033911775081133912284087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9378549033441511883045449 7033911775081133912284087)
        ·
          refine ⟨10550867662621700868426131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033911775081133912284087 10550867662621700868426131)
          ·
            refine ⟨15826301493932551302639197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550867662621700868426131 15826301493932551302639197)
            ·
              refine ⟨5934863060224706738489699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15826301493932551302639197 5934863060224706738489699)
              ·
                refine ⟨8902294590337060107734549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934863060224706738489699 8902294590337060107734549)
                ·
                  refine ⟨417295058922049692550057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8902294590337060107734549 417295058922049692550057)
                  ·
                    rfl

theorem cell23_7314113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 6].length) (baseStart_7314113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314113 prefixEnd_7314113 := by exact prefixLift 7314113
  have htrace : WordTrace (prefixWord ++ tailWord_7314113) baseStart_7314113 baseEnd_7314113 := by
    simpa [prefixWord, tailWord_7314113, baseEnd_7314113] using wordTrace_append hprefix tailTrace_7314113
  have hstable : (prefixWord ++ tailWord_7314113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314113).length < 2 ^ (prefixWord ++ tailWord_7314113).sum := by decide
  have hdescent : baseEnd_7314113 < baseStart_7314113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314129 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_7314129 : Nat := 118140960795 + 7314129 * 2 ^ 59
def prefixEnd_7314129 : Nat := 4983230072969 + 3 ^ 40 * 7314129 * 2
def baseEnd_7314129 : Nat := 3755663745988919170350439

theorem tailTrace_7314129 : CollatzResearch.WordTrace tailWord_7314129 prefixEnd_7314129 3755663745988919170350439 := by
  unfold tailWord_7314129
  simp only [CollatzResearch.WordTrace]
  refine ⟨266768200519167261628097441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177845467012778174418731627 266768200519167261628097441)
  ·
    refine ⟨200076150389375446221073081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266768200519167261628097441 200076150389375446221073081)
    ·
      refine ⟨150057112792031584665804811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200076150389375446221073081 150057112792031584665804811)
      ·
        refine ⟨225085669188047376998707217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150057112792031584665804811 225085669188047376998707217)
        ·
          refine ⟨168814251891035532749030413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225085669188047376998707217 168814251891035532749030413)
          ·
            refine ⟨63305344459138324780886405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168814251891035532749030413 63305344459138324780886405)
            ·
              refine ⟨11869752086088435896416201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63305344459138324780886405 11869752086088435896416201)
              ·
                refine ⟨8902314064566326922312151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11869752086088435896416201 8902314064566326922312151)
                ·
                  refine ⟨13353471096849490383468227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8902314064566326922312151 13353471096849490383468227)
                  ·
                    refine ⟨20030206645274235575202341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13353471096849490383468227 20030206645274235575202341)
                    ·
                      refine ⟨3755663745988919170350439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20030206645274235575202341 3755663745988919170350439)
                      ·
                        rfl

theorem cell23_7314129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_7314129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314129 prefixEnd_7314129 := by exact prefixLift 7314129
  have htrace : WordTrace (prefixWord ++ tailWord_7314129) baseStart_7314129 baseEnd_7314129 := by
    simpa [prefixWord, tailWord_7314129, baseEnd_7314129] using wordTrace_append hprefix tailTrace_7314129
  have hstable : (prefixWord ++ tailWord_7314129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314129).length < 2 ^ (prefixWord ++ tailWord_7314129).sum := by decide
  have hdescent : baseEnd_7314129 < baseStart_7314129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314140 : List Nat := [2, 2, 5, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7314140 : Nat := 118140960795 + 7314140 * 2 ^ 59
def prefixEnd_7314140 : Nat := 4983230072969 + 3 ^ 40 * 7314140 * 2
def baseEnd_7314140 : Nat := 3755669394276118627312889

theorem tailTrace_7314140 : CollatzResearch.WordTrace tailWord_7314140 prefixEnd_7314140 3755669394276118627312889 := by
  unfold tailWord_7314140
  simp only [CollatzResearch.WordTrace]
  refine ⟨133384300861063705253373937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177845734481418273671165249 133384300861063705253373937)
  ·
    refine ⟨100038225645797778940030453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133384300861063705253373937 100038225645797778940030453)
    ·
      refine ⟨9378583654293541775627855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100038225645797778940030453 9378583654293541775627855)
      ·
        refine ⟨14067875481440312663441783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9378583654293541775627855 14067875481440312663441783)
        ·
          refine ⟨21101813222160468995162675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14067875481440312663441783 21101813222160468995162675)
          ·
            refine ⟨31652719833240703492744013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21101813222160468995162675 31652719833240703492744013)
            ·
              refine ⟨11869769937465263809779005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31652719833240703492744013 11869769937465263809779005)
              ·
                refine ⟨4451163726549473928667127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11869769937465263809779005 4451163726549473928667127)
                ·
                  refine ⟨6676745589824210893000691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451163726549473928667127 6676745589824210893000691)
                  ·
                    refine ⟨10015118384736316339501037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6676745589824210893000691 10015118384736316339501037)
                    ·
                      refine ⟨3755669394276118627312889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10015118384736316339501037 3755669394276118627312889)
                      ·
                        rfl

theorem cell23_7314140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7314140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314140 prefixEnd_7314140 := by exact prefixLift 7314140
  have htrace : WordTrace (prefixWord ++ tailWord_7314140) baseStart_7314140 baseEnd_7314140 := by
    simpa [prefixWord, tailWord_7314140, baseEnd_7314140] using wordTrace_append hprefix tailTrace_7314140
  have hstable : (prefixWord ++ tailWord_7314140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314140).length < 2 ^ (prefixWord ++ tailWord_7314140).sum := by decide
  have hdescent : baseEnd_7314140 < baseStart_7314140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314149 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7314149 : Nat := 118140960795 + 7314149 * 2 ^ 59
def prefixEnd_7314149 : Nat := 4983230072969 + 3 ^ 40 * 7314149 * 2
def baseEnd_7314149 : Nat := 3755674015602009092100347

theorem tailTrace_7314149 : CollatzResearch.WordTrace tailWord_7314149 prefixEnd_7314149 3755674015602009092100347 := by
  unfold tailWord_7314149
  simp only [CollatzResearch.WordTrace]
  refine ⟨266768929979094805043825501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177845953319396536695883667 266768929979094805043825501)
  ·
    refine ⟨100038348742160551891434563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266768929979094805043825501 100038348742160551891434563)
    ·
      refine ⟨150057523113240827837151845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100038348742160551891434563 150057523113240827837151845)
      ·
        refine ⟨28135785583732655219465971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150057523113240827837151845 28135785583732655219465971)
        ·
          refine ⟨42203678375598982829198957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28135785583732655219465971 42203678375598982829198957)
          ·
            refine ⟨15826379390849618560949609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42203678375598982829198957 15826379390849618560949609)
            ·
              refine ⟨11869784543137213920712207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15826379390849618560949609 11869784543137213920712207)
              ·
                refine ⟨17804676814705820881068311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11869784543137213920712207 17804676814705820881068311)
                ·
                  refine ⟨26707015222058731321602467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17804676814705820881068311 26707015222058731321602467)
                  ·
                    refine ⟨40060522833088096982403701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26707015222058731321602467 40060522833088096982403701)
                    ·
                      refine ⟨3755674015602009092100347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40060522833088096982403701 3755674015602009092100347)
                      ·
                        rfl

theorem cell23_7314149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7314149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314149 prefixEnd_7314149 := by exact prefixLift 7314149
  have htrace : WordTrace (prefixWord ++ tailWord_7314149) baseStart_7314149 baseEnd_7314149 := by
    simpa [prefixWord, tailWord_7314149, baseEnd_7314149] using wordTrace_append hprefix tailTrace_7314149
  have hstable : (prefixWord ++ tailWord_7314149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314149).length < 2 ^ (prefixWord ++ tailWord_7314149).sum := by decide
  have hdescent : baseEnd_7314149 < baseStart_7314149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314183 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_7314183 : Nat := 118140960795 + 7314183 * 2 ^ 59
def prefixEnd_7314183 : Nat := 4983230072969 + 3 ^ 40 * 7314183 * 2
def baseEnd_7314183 : Nat := 3755691473944261959075191

theorem tailTrace_7314183 : CollatzResearch.WordTrace tailWord_7314183 prefixEnd_7314183 3755691473944261959075191 := by
  unfold tailWord_7314183
  simp only [CollatzResearch.WordTrace]
  refine ⟨266770170060971628850563203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177846780040647752567042135 266770170060971628850563203)
  ·
    refine ⟨400155255091457443275844805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266770170060971628850563203 400155255091457443275844805)
    ·
      refine ⟨75029110329648270614220901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400155255091457443275844805 75029110329648270614220901)
      ·
        refine ⟨14067958186809050740166419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75029110329648270614220901 14067958186809050740166419)
        ·
          refine ⟨21101937280213576110249629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14067958186809050740166419 21101937280213576110249629)
          ·
            refine ⟨7913226480080091041343611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21101937280213576110249629 7913226480080091041343611)
            ·
              refine ⟨11869839720120136562015417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913226480080091041343611 11869839720120136562015417)
              ·
                refine ⟨8902379790090102421511563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11869839720120136562015417 8902379790090102421511563)
                ·
                  refine ⟨13353569685135153632267345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8902379790090102421511563 13353569685135153632267345)
                  ·
                    refine ⟨10015177263851365224200509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13353569685135153632267345 10015177263851365224200509)
                    ·
                      refine ⟨3755691473944261959075191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10015177263851365224200509 3755691473944261959075191)
                      ·
                        rfl

theorem cell23_7314183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_7314183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314183 prefixEnd_7314183 := by exact prefixLift 7314183
  have htrace : WordTrace (prefixWord ++ tailWord_7314183) baseStart_7314183 baseEnd_7314183 := by
    simpa [prefixWord, tailWord_7314183, baseEnd_7314183] using wordTrace_append hprefix tailTrace_7314183
  have hstable : (prefixWord ++ tailWord_7314183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314183).length < 2 ^ (prefixWord ++ tailWord_7314183).sum := by decide
  have hdescent : baseEnd_7314183 < baseStart_7314183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314229 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7314229 : Nat := 118140960795 + 7314229 * 2 ^ 59
def prefixEnd_7314229 : Nat := 4983230072969 + 3 ^ 40 * 7314229 * 2
def baseEnd_7314229 : Nat := 1251905031351456259699993

theorem tailTrace_7314229 : CollatzResearch.WordTrace tailWord_7314229 prefixEnd_7314229 1251905031351456259699993 := by
  unfold tailWord_7314229
  simp only [CollatzResearch.WordTrace]
  refine ⟨266771847818804978706737741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177847898545869985804491827 266771847818804978706737741)
  ·
    refine ⟨100039442932051867015026653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266771847818804978706737741 100039442932051867015026653)
    ·
      refine ⟨37514791099519450130634995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100039442932051867015026653 37514791099519450130634995)
      ·
        refine ⟨56272186649279175195952493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37514791099519450130634995 56272186649279175195952493)
        ·
          refine ⟨21102069993479690698482185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56272186649279175195952493 21102069993479690698482185)
          ·
            refine ⟨15826552495109768023861639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21102069993479690698482185 15826552495109768023861639)
            ·
              refine ⟨23739828742664652035792459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15826552495109768023861639 23739828742664652035792459)
              ·
                refine ⟨35609743113996978053688689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23739828742664652035792459 35609743113996978053688689)
                ·
                  refine ⟨26707307335497733540266517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35609743113996978053688689 26707307335497733540266517)
                  ·
                    refine ⟨1251905031351456259699993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26707307335497733540266517 1251905031351456259699993)
                    ·
                      rfl

theorem cell23_7314229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7314229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314229 prefixEnd_7314229 := by exact prefixLift 7314229
  have htrace : WordTrace (prefixWord ++ tailWord_7314229) baseStart_7314229 baseEnd_7314229 := by
    simpa [prefixWord, tailWord_7314229, baseEnd_7314229] using wordTrace_append hprefix tailTrace_7314229
  have hstable : (prefixWord ++ tailWord_7314229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314229).length < 2 ^ (prefixWord ++ tailWord_7314229).sum := by decide
  have hdescent : baseEnd_7314229 < baseStart_7314229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314236 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_7314236 : Nat := 118140960795 + 7314236 * 2 ^ 59
def prefixEnd_7314236 : Nat := 4983230072969 + 3 ^ 40 * 7314236 * 2
def baseEnd_7314236 : Nat := 3755718688418950251712447

theorem tailTrace_7314236 : CollatzResearch.WordTrace tailWord_7314236 prefixEnd_7314236 3755718688418950251712447 := by
  unfold tailWord_7314236
  simp only [CollatzResearch.WordTrace]
  refine ⟨133386051564889809451121281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177848068753186412601495041 133386051564889809451121281)
  ·
    refine ⟨100039538673667357088340961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133386051564889809451121281 100039538673667357088340961)
    ·
      refine ⟨75029654005250517816255721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100039538673667357088340961 75029654005250517816255721)
      ·
        refine ⟨56272240503937888362191791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75029654005250517816255721 56272240503937888362191791)
        ·
          refine ⟨84408360755906832543287687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56272240503937888362191791 84408360755906832543287687)
          ·
            refine ⟨126612541133860248814931531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84408360755906832543287687 126612541133860248814931531)
            ·
              refine ⟨189918811700790373222397297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126612541133860248814931531 189918811700790373222397297)
              ·
                refine ⟨142439108775592779916797973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189918811700790373222397297 142439108775592779916797973)
                ·
                  refine ⟨6676833223855911558599905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142439108775592779916797973 6676833223855911558599905)
                  ·
                    refine ⟨5007624917891933668949929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6676833223855911558599905 5007624917891933668949929)
                    ·
                      refine ⟨3755718688418950251712447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007624917891933668949929 3755718688418950251712447)
                      ·
                        rfl

theorem cell23_7314236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_7314236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314236 prefixEnd_7314236 := by exact prefixLift 7314236
  have htrace : WordTrace (prefixWord ++ tailWord_7314236) baseStart_7314236 baseEnd_7314236 := by
    simpa [prefixWord, tailWord_7314236, baseEnd_7314236] using wordTrace_append hprefix tailTrace_7314236
  have hstable : (prefixWord ++ tailWord_7314236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314236).length < 2 ^ (prefixWord ++ tailWord_7314236).sum := by decide
  have hdescent : baseEnd_7314236 < baseStart_7314236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314257 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 1, 3, 2]
def baseStart_7314257 : Nat := 118140960795 + 7314257 * 2 ^ 59
def prefixEnd_7314257 : Nat := 4983230072969 + 3 ^ 40 * 7314257 * 2
def baseEnd_7314257 : Nat := 3755729471512694669549851

theorem tailTrace_7314257 : CollatzResearch.WordTrace tailWord_7314257 prefixEnd_7314257 3755729471512694669549851 := by
  unfold tailWord_7314257
  simp only [CollatzResearch.WordTrace]
  refine ⟨266772869062703539488757025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177848579375135692992504683 266772869062703539488757025)
  ·
    refine ⟨200079651797027654616567769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266772869062703539488757025 200079651797027654616567769)
    ·
      refine ⟨150059738847770740962425827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200079651797027654616567769 150059738847770740962425827)
      ·
        refine ⟨225089608271656111443638741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150059738847770740962425827 225089608271656111443638741)
        ·
          refine ⟨5275537693866940111960283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 225089608271656111443638741 5275537693866940111960283)
          ·
            refine ⟨7913306540800410167940425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275537693866940111960283 7913306540800410167940425)
            ·
              refine ⟨5934979905600307625955319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7913306540800410167940425 5934979905600307625955319)
              ·
                refine ⟨8902469858400461438932979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934979905600307625955319 8902469858400461438932979)
                ·
                  refine ⟨13353704787600692158399469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8902469858400461438932979 13353704787600692158399469)
                  ·
                    refine ⟨5007639295350259559399801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13353704787600692158399469 5007639295350259559399801)
                    ·
                      refine ⟨3755729471512694669549851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007639295350259559399801 3755729471512694669549851)
                      ·
                        rfl

theorem cell23_7314257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_7314257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314257 prefixEnd_7314257 := by exact prefixLift 7314257
  have htrace : WordTrace (prefixWord ++ tailWord_7314257) baseStart_7314257 baseEnd_7314257 := by
    simpa [prefixWord, tailWord_7314257, baseEnd_7314257] using wordTrace_append hprefix tailTrace_7314257
  have hstable : (prefixWord ++ tailWord_7314257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314257).length < 2 ^ (prefixWord ++ tailWord_7314257).sum := by decide
  have hdescent : baseEnd_7314257 < baseStart_7314257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314276 : List Nat := [2, 3, 1, 1, 4, 1, 2, 4, 5]
def baseStart_7314276 : Nat := 118140960795 + 7314276 * 2 ^ 59
def prefixEnd_7314276 : Nat := 4983230072969 + 3 ^ 40 * 7314276 * 2
def baseEnd_7314276 : Nat := 417304358627236677245807

theorem tailTrace_7314276 : CollatzResearch.WordTrace tailWord_7314276 prefixEnd_7314276 417304358627236677245807 := by
  unfold tailWord_7314276
  simp only [CollatzResearch.WordTrace]
  refine ⟨133386781024817352866849341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177849041366423137155799121 133386781024817352866849341)
  ·
    refine ⟨50020042884306507325068503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133386781024817352866849341 50020042884306507325068503)
    ·
      refine ⟨75030064326459760987602755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50020042884306507325068503 75030064326459760987602755)
      ·
        refine ⟨112545096489689641481404133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75030064326459760987602755 112545096489689641481404133)
        ·
          refine ⟨21102205591816807777763275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112545096489689641481404133 21102205591816807777763275)
          ·
            refine ⟨31653308387725211666644913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21102205591816807777763275 31653308387725211666644913)
            ·
              refine ⟨23739981290793908749983685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31653308387725211666644913 23739981290793908749983685)
              ·
                refine ⟨4451246492023857890621941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23739981290793908749983685 4451246492023857890621941)
                ·
                  refine ⟨417304358627236677245807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451246492023857890621941 417304358627236677245807)
                  ·
                    rfl

theorem cell23_7314276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_7314276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314276 prefixEnd_7314276 := by exact prefixLift 7314276
  have htrace : WordTrace (prefixWord ++ tailWord_7314276) baseStart_7314276 baseEnd_7314276 := by
    simpa [prefixWord, tailWord_7314276, baseEnd_7314276] using wordTrace_append hprefix tailTrace_7314276
  have hstable : (prefixWord ++ tailWord_7314276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314276).length < 2 ^ (prefixWord ++ tailWord_7314276).sum := by decide
  have hdescent : baseEnd_7314276 < baseStart_7314276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314309 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_7314309 : Nat := 118140960795 + 7314309 * 2 ^ 59
def prefixEnd_7314309 : Nat := 4983230072969 + 3 ^ 40 * 7314309 * 2
def baseEnd_7314309 : Nat := 3755756172506728466099611

theorem tailTrace_7314309 : CollatzResearch.WordTrace tailWord_7314309 prefixEnd_7314309 3755756172506728466099611 := by
  unfold tailWord_7314309
  simp only [CollatzResearch.WordTrace]
  refine ⟨266774765658515152369649981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177849843772343434913099987 266774765658515152369649981)
  ·
    refine ⟨100040537121943182138618743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266774765658515152369649981 100040537121943182138618743)
    ·
      refine ⟨150060805682914773207928115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100040537121943182138618743 150060805682914773207928115)
      ·
        refine ⟨225091208524372159811892173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150060805682914773207928115 225091208524372159811892173)
        ·
          refine ⟨84409203196639559929459565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225091208524372159811892173 84409203196639559929459565)
          ·
            refine ⟨31653451198739834973547337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84409203196639559929459565 31653451198739834973547337)
            ·
              refine ⟨23740088399054876230160503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31653451198739834973547337 23740088399054876230160503)
              ·
                refine ⟨35610132598582314345240755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23740088399054876230160503 35610132598582314345240755)
                ·
                  refine ⟨53415198897873471517861133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35610132598582314345240755 53415198897873471517861133)
                  ·
                    refine ⟨20030699586702551819197925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53415198897873471517861133 20030699586702551819197925)
                    ·
                      refine ⟨3755756172506728466099611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20030699586702551819197925 3755756172506728466099611)
                      ·
                        rfl

theorem cell23_7314309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_7314309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314309 prefixEnd_7314309 := by exact prefixLift 7314309
  have htrace : WordTrace (prefixWord ++ tailWord_7314309) baseStart_7314309 baseEnd_7314309 := by
    simpa [prefixWord, tailWord_7314309, baseEnd_7314309] using wordTrace_append hprefix tailTrace_7314309
  have hstable : (prefixWord ++ tailWord_7314309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314309).length < 2 ^ (prefixWord ++ tailWord_7314309).sum := by decide
  have hdescent : baseEnd_7314309 < baseStart_7314309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314336 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 3, 4]
def baseStart_7314336 : Nat := 118140960795 + 7314336 * 2 ^ 59
def prefixEnd_7314336 : Nat := 4983230072969 + 3 ^ 40 * 7314336 * 2
def baseEnd_7314336 : Nat := 1251923345494799953487329

theorem tailTrace_7314336 : CollatzResearch.WordTrace tailWord_7314336 prefixEnd_7314336 1251923345494799953487329 := by
  unfold tailWord_7314336
  simp only [CollatzResearch.WordTrace]
  refine ⟨133387875214708667990441431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177850500286278223987255241 133387875214708667990441431)
  ·
    refine ⟨200081812822063001985662147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133387875214708667990441431 200081812822063001985662147)
    ·
      refine ⟨300122719233094502978493221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200081812822063001985662147 300122719233094502978493221)
      ·
        refine ⟨56273009856205219308467479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300122719233094502978493221 56273009856205219308467479)
        ·
          refine ⟨84409514784307828962701219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56273009856205219308467479 84409514784307828962701219)
          ·
            refine ⟨126614272176461743444051829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84409514784307828962701219 126614272176461743444051829)
            ·
              refine ⟨11870088016543288447879859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126614272176461743444051829 11870088016543288447879859)
              ·
                refine ⟨17805132024814932671819789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11870088016543288447879859 17805132024814932671819789)
                ·
                  refine ⟨6676924509305599751932421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17805132024814932671819789 6676924509305599751932421)
                  ·
                    refine ⟨1251923345494799953487329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676924509305599751932421 1251923345494799953487329)
                    ·
                      rfl

theorem cell23_7314336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_7314336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314336 prefixEnd_7314336 := by exact prefixLift 7314336
  have htrace : WordTrace (prefixWord ++ tailWord_7314336) baseStart_7314336 baseEnd_7314336 := by
    simpa [prefixWord, tailWord_7314336, baseEnd_7314336] using wordTrace_append hprefix tailTrace_7314336
  have hstable : (prefixWord ++ tailWord_7314336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314336).length < 2 ^ (prefixWord ++ tailWord_7314336).sum := by decide
  have hdescent : baseEnd_7314336 < baseStart_7314336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314359 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_7314359 : Nat := 118140960795 + 7314359 * 2 ^ 59
def prefixEnd_7314359 : Nat := 4983230072969 + 3 ^ 40 * 7314359 * 2
def baseEnd_7314359 : Nat := 3755781846539453270474381

theorem tailTrace_7314359 : CollatzResearch.WordTrace tailWord_7314359 prefixEnd_7314359 3755781846539453270474381 := by
  unfold tailWord_7314359
  simp only [CollatzResearch.WordTrace]
  refine ⟨266776589308334010908970131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177851059538889340605980087 266776589308334010908970131)
  ·
    refine ⟨400164883962501016363455197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266776589308334010908970131 400164883962501016363455197)
    ·
      refine ⟨150061831485937881136295699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400164883962501016363455197 150061831485937881136295699)
      ·
        refine ⟨225092747228906821704443549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150061831485937881136295699 225092747228906821704443549)
        ·
          refine ⟨84409780210840058139166331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225092747228906821704443549 84409780210840058139166331)
          ·
            refine ⟨126614670316260087208749497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84409780210840058139166331 126614670316260087208749497)
            ·
              refine ⟨94961002737195065406562123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126614670316260087208749497 94961002737195065406562123)
              ·
                refine ⟨142441504105792598109843185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94961002737195065406562123 142441504105792598109843185)
                ·
                  refine ⟨106831128079344448582382389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142441504105792598109843185 106831128079344448582382389)
                  ·
                    refine ⟨10015418257438542054598349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106831128079344448582382389 10015418257438542054598349)
                    ·
                      refine ⟨3755781846539453270474381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10015418257438542054598349 3755781846539453270474381)
                      ·
                        rfl

theorem cell23_7314359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_7314359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314359 prefixEnd_7314359 := by exact prefixLift 7314359
  have htrace : WordTrace (prefixWord ++ tailWord_7314359) baseStart_7314359 baseEnd_7314359 := by
    simpa [prefixWord, tailWord_7314359, baseEnd_7314359] using wordTrace_append hprefix tailTrace_7314359
  have hstable : (prefixWord ++ tailWord_7314359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314359).length < 2 ^ (prefixWord ++ tailWord_7314359).sum := by decide
  have hdescent : baseEnd_7314359 < baseStart_7314359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314416 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4]
def baseStart_7314416 : Nat := 118140960795 + 7314416 * 2 ^ 59
def prefixEnd_7314416 : Nat := 4983230072969 + 3 ^ 40 * 7314416 * 2
def baseEnd_7314416 : Nat := 3755811114936759547461619

theorem tailTrace_7314416 : CollatzResearch.WordTrace tailWord_7314416 prefixEnd_7314416 3755811114936759547461619 := by
  unfold tailWord_7314416
  simp only [CollatzResearch.WordTrace]
  refine ⟨133389334134563754821897551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177852445512751673095863401 133389334134563754821897551)
  ·
    refine ⟨200084001201845632232846327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133389334134563754821897551 200084001201845632232846327)
    ·
      refine ⟨300126001802768448349269491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200084001201845632232846327 300126001802768448349269491)
      ·
        refine ⟨450189002704152672523904237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300126001802768448349269491 450189002704152672523904237)
        ·
          refine ⟨168820876014057252196464089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450189002704152672523904237 168820876014057252196464089)
          ·
            refine ⟨126615657010542939147348067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168820876014057252196464089 126615657010542939147348067)
            ·
              refine ⟨189923485515814408721022101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126615657010542939147348067 189923485515814408721022101)
              ·
                refine ⟨8902663383553800408797911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189923485515814408721022101 8902663383553800408797911)
                ·
                  refine ⟨13353995075330700613196867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8902663383553800408797911 13353995075330700613196867)
                  ·
                    refine ⟨20030992612996050919795301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13353995075330700613196867 20030992612996050919795301)
                    ·
                      refine ⟨3755811114936759547461619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20030992612996050919795301 3755811114936759547461619)
                      ·
                        rfl

theorem cell23_7314416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_7314416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314416 prefixEnd_7314416 := by exact prefixLift 7314416
  have htrace : WordTrace (prefixWord ++ tailWord_7314416) baseStart_7314416 baseEnd_7314416 := by
    simpa [prefixWord, tailWord_7314416, baseEnd_7314416] using wordTrace_append hprefix tailTrace_7314416
  have hstable : (prefixWord ++ tailWord_7314416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314416).length < 2 ^ (prefixWord ++ tailWord_7314416).sum := by decide
  have hdescent : baseEnd_7314416 < baseStart_7314416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314429 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_7314429 : Nat := 118140960795 + 7314429 * 2 ^ 59
def prefixEnd_7314429 : Nat := 4983230072969 + 3 ^ 40 * 7314429 * 2
def baseEnd_7314429 : Nat := 3755817790185267996599059

theorem tailTrace_7314429 : CollatzResearch.WordTrace tailWord_7314429 prefixEnd_7314429 3755817790185267996599059 := by
  unfold tailWord_7314429
  simp only [CollatzResearch.WordTrace]
  refine ⟨266779142418080412864018341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177852761612053608576012227 266779142418080412864018341)
  ·
    refine ⟨50021089203390077412003439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266779142418080412864018341 50021089203390077412003439)
    ·
      refine ⟨75031633805085116118005159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50021089203390077412003439 75031633805085116118005159)
      ·
        refine ⟨112547450707627674177007739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75031633805085116118005159 112547450707627674177007739)
        ·
          refine ⟨168821176061441511265511609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112547450707627674177007739 168821176061441511265511609)
          ·
            refine ⟨126615882046081133449133707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168821176061441511265511609 126615882046081133449133707)
            ·
              refine ⟨189923823069121700173700561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126615882046081133449133707 189923823069121700173700561)
              ·
                refine ⟨142442867301841275130275421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189923823069121700173700561 142442867301841275130275421)
                ·
                  refine ⟨53416075238190478173853283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142442867301841275130275421 53416075238190478173853283)
                  ·
                    refine ⟨80124112857285717260779925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53416075238190478173853283 80124112857285717260779925)
                    ·
                      refine ⟨3755817790185267996599059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80124112857285717260779925 3755817790185267996599059)
                      ·
                        rfl

theorem cell23_7314429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_7314429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314429 prefixEnd_7314429 := by exact prefixLift 7314429
  have htrace : WordTrace (prefixWord ++ tailWord_7314429) baseStart_7314429 baseEnd_7314429 := by
    simpa [prefixWord, tailWord_7314429, baseEnd_7314429] using wordTrace_append hprefix tailTrace_7314429
  have hstable : (prefixWord ++ tailWord_7314429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314429).length < 2 ^ (prefixWord ++ tailWord_7314429).sum := by decide
  have hdescent : baseEnd_7314429 < baseStart_7314429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314430 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_7314430 : Nat := 118140960795 + 7314430 * 2 ^ 59
def prefixEnd_7314430 : Nat := 4983230072969 + 3 ^ 40 * 7314430 * 2
def baseEnd_7314430 : Nat := 1251939434555307497562185

theorem tailTrace_7314430 : CollatzResearch.WordTrace tailWord_7314430 prefixEnd_7314430 1251939434555307497562185 := by
  unfold tailWord_7314430
  simp only [CollatzResearch.WordTrace]
  refine ⟨33347397361384598754350593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177852785927384526689869829 33347397361384598754350593)
  ·
    refine ⟨25010548021038449065762945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33347397361384598754350593 25010548021038449065762945)
    ·
      refine ⟨18757911015778836799322209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25010548021038449065762945 18757911015778836799322209)
      ·
        refine ⟨14068433261834127599491657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18757911015778836799322209 14068433261834127599491657)
        ·
          refine ⟨10551324946375595699618743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14068433261834127599491657 10551324946375595699618743)
          ·
            refine ⟨15826987419563393549428115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10551324946375595699618743 15826987419563393549428115)
            ·
              refine ⟨23740481129345090324142173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15826987419563393549428115 23740481129345090324142173)
              ·
                refine ⟨8902680423504408871553315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23740481129345090324142173 8902680423504408871553315)
                ·
                  refine ⟨13354020635256613307329973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8902680423504408871553315 13354020635256613307329973)
                  ·
                    refine ⟨1251939434555307497562185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13354020635256613307329973 1251939434555307497562185)
                    ·
                      rfl

theorem cell23_7314430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_7314430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314430 prefixEnd_7314430 := by exact prefixLift 7314430
  have htrace : WordTrace (prefixWord ++ tailWord_7314430) baseStart_7314430 baseEnd_7314430 := by
    simpa [prefixWord, tailWord_7314430, baseEnd_7314430] using wordTrace_append hprefix tailTrace_7314430
  have hstable : (prefixWord ++ tailWord_7314430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314430).length < 2 ^ (prefixWord ++ tailWord_7314430).sum := by decide
  have hdescent : baseEnd_7314430 < baseStart_7314430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314433 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_7314433 : Nat := 118140960795 + 7314433 * 2 ^ 59
def prefixEnd_7314433 : Nat := 4983230072969 + 3 ^ 40 * 7314433 * 2
def baseEnd_7314433 : Nat := 3755819844107885980949041

theorem tailTrace_7314433 : CollatzResearch.WordTrace tailWord_7314433 prefixEnd_7314433 3755819844107885980949041 := by
  unfold tailWord_7314433
  simp only [CollatzResearch.WordTrace]
  refine ⟨266779288310065921547163953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177852858873377281031442635 266779288310065921547163953)
  ·
    refine ⟨200084466232549441160372965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266779288310065921547163953 200084466232549441160372965)
    ·
      refine ⟨37515837418603020217569931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200084466232549441160372965 37515837418603020217569931)
      ·
        refine ⟨56273756127904530326354897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37515837418603020217569931 56273756127904530326354897)
        ·
          refine ⟨42205317095928397744766173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56273756127904530326354897 42205317095928397744766173)
          ·
            refine ⟨15826993910973149154287315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42205317095928397744766173 15826993910973149154287315)
            ·
              refine ⟨23740490866459723731430973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15826993910973149154287315 23740490866459723731430973)
              ·
                refine ⟨8902684074922396399286615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23740490866459723731430973 8902684074922396399286615)
                ·
                  refine ⟨13354026112383594598929923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8902684074922396399286615 13354026112383594598929923)
                  ·
                    refine ⟨20031039168575391898394885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13354026112383594598929923 20031039168575391898394885)
                    ·
                      refine ⟨3755819844107885980949041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20031039168575391898394885 3755819844107885980949041)
                      ·
                        rfl

theorem cell23_7314433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_7314433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314433 prefixEnd_7314433 := by exact prefixLift 7314433
  have htrace : WordTrace (prefixWord ++ tailWord_7314433) baseStart_7314433 baseEnd_7314433 := by
    simpa [prefixWord, tailWord_7314433, baseEnd_7314433] using wordTrace_append hprefix tailTrace_7314433
  have hstable : (prefixWord ++ tailWord_7314433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314433).length < 2 ^ (prefixWord ++ tailWord_7314433).sum := by decide
  have hdescent : baseEnd_7314433 < baseStart_7314433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314439 : List Nat := [1, 1, 4, 3, 1, 1, 12]
def baseStart_7314439 : Nat := 118140960795 + 7314439 * 2 ^ 59
def prefixEnd_7314439 : Nat := 4983230072969 + 3 ^ 40 * 7314439 * 2
def baseEnd_7314439 : Nat := 46368184259158184660173

theorem tailTrace_7314439 : CollatzResearch.WordTrace tailWord_7314439 prefixEnd_7314439 46368184259158184660173 := by
  unfold tailWord_7314439
  simp only [CollatzResearch.WordTrace]
  refine ⟨266779507148044184571882371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177853004765362789714588247 266779507148044184571882371)
  ·
    refine ⟨400169260722066276857823557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266779507148044184571882371 400169260722066276857823557)
    ·
      refine ⟨75031736385387426910841917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400169260722066276857823557 75031736385387426910841917)
      ·
        refine ⟨28136901144520285091565719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75031736385387426910841917 28136901144520285091565719)
        ·
          refine ⟨42205351716780427637348579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28136901144520285091565719 42205351716780427637348579)
          ·
            refine ⟨63308027575170641456022869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42205351716780427637348579 63308027575170641456022869)
            ·
              refine ⟨46368184259158184660173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63308027575170641456022869 46368184259158184660173)
              ·
                rfl

theorem cell23_7314439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 12].length) (baseStart_7314439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314439 prefixEnd_7314439 := by exact prefixLift 7314439
  have htrace : WordTrace (prefixWord ++ tailWord_7314439) baseStart_7314439 baseEnd_7314439 := by
    simpa [prefixWord, tailWord_7314439, baseEnd_7314439] using wordTrace_append hprefix tailTrace_7314439
  have hstable : (prefixWord ++ tailWord_7314439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314439).length < 2 ^ (prefixWord ++ tailWord_7314439).sum := by decide
  have hdescent : baseEnd_7314439 < baseStart_7314439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314443 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 2, 4]
def baseStart_7314443 : Nat := 118140960795 + 7314443 * 2 ^ 59
def prefixEnd_7314443 : Nat := 4983230072969 + 3 ^ 40 * 7314443 * 2
def baseEnd_7314443 : Nat := 1251941659638143647274665

theorem tailTrace_7314443 : CollatzResearch.WordTrace tailWord_7314443 prefixEnd_7314443 1251941659638143647274665 := by
  unfold tailWord_7314443
  simp only [CollatzResearch.WordTrace]
  refine ⟨266779653040029693255027983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177853102026686462170018655 266779653040029693255027983)
  ·
    refine ⟨400169479560044539882541975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266779653040029693255027983 400169479560044539882541975)
    ·
      refine ⟨600254219340066809823812963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400169479560044539882541975 600254219340066809823812963)
      ·
        refine ⟨900381329010100214735719445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600254219340066809823812963 900381329010100214735719445)
        ·
          refine ⟨42205374797348447565736849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 900381329010100214735719445 42205374797348447565736849)
          ·
            refine ⟨31654031098011335674302637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42205374797348447565736849 31654031098011335674302637)
            ·
              refine ⟨11870261661754250877863489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31654031098011335674302637 11870261661754250877863489)
              ·
                refine ⟨8902696246315688158397617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11870261661754250877863489 8902696246315688158397617)
                ·
                  refine ⟨6677022184736766118798213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8902696246315688158397617 6677022184736766118798213)
                  ·
                    refine ⟨1251941659638143647274665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677022184736766118798213 1251941659638143647274665)
                    ·
                      rfl

theorem cell23_7314443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 4].length) (baseStart_7314443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314443 prefixEnd_7314443 := by exact prefixLift 7314443
  have htrace : WordTrace (prefixWord ++ tailWord_7314443) baseStart_7314443 baseEnd_7314443 := by
    simpa [prefixWord, tailWord_7314443, baseEnd_7314443] using wordTrace_append hprefix tailTrace_7314443
  have hstable : (prefixWord ++ tailWord_7314443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314443).length < 2 ^ (prefixWord ++ tailWord_7314443).sum := by decide
  have hdescent : baseEnd_7314443 < baseStart_7314443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314460 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_7314460 : Nat := 118140960795 + 7314460 * 2 ^ 59
def prefixEnd_7314460 : Nat := 4983230072969 + 3 ^ 40 * 7314460 * 2
def baseEnd_7314460 : Nat := 1251944569361852458437139

theorem tailTrace_7314460 : CollatzResearch.WordTrace tailWord_7314460 prefixEnd_7314460 1251944569361852458437139 := by
  unfold tailWord_7314460
  simp only [CollatzResearch.WordTrace]
  refine ⟨133390136540484052579198417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177853515387312070105597889 133390136540484052579198417)
  ·
    refine ⟨100042602405363039434398813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133390136540484052579198417 100042602405363039434398813)
    ·
      refine ⟨37515975902011139787899555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100042602405363039434398813 37515975902011139787899555)
      ·
        refine ⟨56273963853016709681849333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37515975902011139787899555 56273963853016709681849333)
        ·
          refine ⟨5275684111220316532673375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56273963853016709681849333 5275684111220316532673375)
          ·
            refine ⟨7913526166830474799010063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275684111220316532673375 7913526166830474799010063)
            ·
              refine ⟨11870289250245712198515095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913526166830474799010063 11870289250245712198515095)
              ·
                refine ⟨17805433875368568297772643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11870289250245712198515095 17805433875368568297772643)
                ·
                  refine ⟨26708150813052852446658965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17805433875368568297772643 26708150813052852446658965)
                  ·
                    refine ⟨1251944569361852458437139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26708150813052852446658965 1251944569361852458437139)
                    ·
                      rfl

theorem cell23_7314460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_7314460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314460 prefixEnd_7314460 := by exact prefixLift 7314460
  have htrace : WordTrace (prefixWord ++ tailWord_7314460) baseStart_7314460 baseEnd_7314460 := by
    simpa [prefixWord, tailWord_7314460, baseEnd_7314460] using wordTrace_append hprefix tailTrace_7314460
  have hstable : (prefixWord ++ tailWord_7314460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314460).length < 2 ^ (prefixWord ++ tailWord_7314460).sum := by decide
  have hdescent : baseEnd_7314460 < baseStart_7314460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314463 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 4]
def baseStart_7314463 : Nat := 118140960795 + 7314463 * 2 ^ 59
def prefixEnd_7314463 : Nat := 4983230072969 + 3 ^ 40 * 7314463 * 2
def baseEnd_7314463 : Nat := 3755835248527520863573903

theorem tailTrace_7314463 : CollatzResearch.WordTrace tailWord_7314463 prefixEnd_7314463 3755835248527520863573903 := by
  unfold tailWord_7314463
  simp only [CollatzResearch.WordTrace]
  refine ⟨266780382499957236670756043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177853588333304824447170695 266780382499957236670756043)
  ·
    refine ⟨400170573749935855006134065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266780382499957236670756043 400170573749935855006134065)
    ·
      refine ⟨300127930312451891254600549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400170573749935855006134065 300127930312451891254600549)
      ·
        refine ⟨56273986933584729610237603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300127930312451891254600549 56273986933584729610237603)
        ·
          refine ⟨84410980400377094415356405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56273986933584729610237603 84410980400377094415356405)
          ·
            refine ⟨7913529412535352601439663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84410980400377094415356405 7913529412535352601439663)
            ·
              refine ⟨11870294118803028902159495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913529412535352601439663 11870294118803028902159495)
              ·
                refine ⟨17805441178204543353239243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11870294118803028902159495 17805441178204543353239243)
                ·
                  refine ⟨26708161767306815029858865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17805441178204543353239243 26708161767306815029858865)
                  ·
                    refine ⟨20031121325480111272394149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26708161767306815029858865 20031121325480111272394149)
                    ·
                      refine ⟨3755835248527520863573903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20031121325480111272394149 3755835248527520863573903)
                      ·
                        rfl

theorem cell23_7314463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_7314463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314463 prefixEnd_7314463 := by exact prefixLift 7314463
  have htrace : WordTrace (prefixWord ++ tailWord_7314463) baseStart_7314463 baseEnd_7314463 := by
    simpa [prefixWord, tailWord_7314463, baseEnd_7314463] using wordTrace_append hprefix tailTrace_7314463
  have hstable : (prefixWord ++ tailWord_7314463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314463).length < 2 ^ (prefixWord ++ tailWord_7314463).sum := by decide
  have hdescent : baseEnd_7314463 < baseStart_7314463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314516 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_7314516 : Nat := 118140960795 + 7314516 * 2 ^ 59
def prefixEnd_7314516 : Nat := 4983230072969 + 3 ^ 40 * 7314516 * 2
def baseEnd_7314516 : Nat := 1251954154334069718737053

theorem tailTrace_7314516 : CollatzResearch.WordTrace tailWord_7314516 prefixEnd_7314516 1251954154334069718737053 := by
  unfold tailWord_7314516
  simp only [CollatzResearch.WordTrace]
  refine ⟨133391157784382613361217701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177854877045843484481623601 133391157784382613361217701)
  ·
    refine ⟨25010842084571740005228319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133391157784382613361217701 25010842084571740005228319)
    ·
      refine ⟨37516263126857610007842479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25010842084571740005228319 37516263126857610007842479)
      ·
        refine ⟨56274394690286415011763719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37516263126857610007842479 56274394690286415011763719)
        ·
          refine ⟨84411592035429622517645579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56274394690286415011763719 84411592035429622517645579)
          ·
            refine ⟨126617388053144433776468369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84411592035429622517645579 126617388053144433776468369)
            ·
              refine ⟨94963041039858325332351277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126617388053144433776468369 94963041039858325332351277)
              ·
                refine ⟨35611140389946871999631729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94963041039858325332351277 35611140389946871999631729)
                ·
                  refine ⟨26708355292460153999723797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35611140389946871999631729 26708355292460153999723797)
                  ·
                    refine ⟨1251954154334069718737053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26708355292460153999723797 1251954154334069718737053)
                    ·
                      rfl

theorem cell23_7314516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_7314516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314516 prefixEnd_7314516 := by exact prefixLift 7314516
  have htrace : WordTrace (prefixWord ++ tailWord_7314516) baseStart_7314516 baseEnd_7314516 := by
    simpa [prefixWord, tailWord_7314516, baseEnd_7314516] using wordTrace_append hprefix tailTrace_7314516
  have hstable : (prefixWord ++ tailWord_7314516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314516).length < 2 ^ (prefixWord ++ tailWord_7314516).sum := by decide
  have hdescent : baseEnd_7314516 < baseStart_7314516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314557 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_7314557 : Nat := 118140960795 + 7314557 * 2 ^ 59
def prefixEnd_7314557 : Nat := 4983230072969 + 3 ^ 40 * 7314557 * 2
def baseEnd_7314557 : Nat := 3755883515709043495798471

theorem tailTrace_7314557 : CollatzResearch.WordTrace tailWord_7314557 prefixEnd_7314557 3755883515709043495798471 := by
  unfold tailWord_7314557
  simp only [CollatzResearch.WordTrace]
  refine ⟨266783810961616690724677925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177855873974411127149785283 266783810961616690724677925)
  ·
    refine ⟨50021964555303129510877111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266783810961616690724677925 50021964555303129510877111)
    ·
      refine ⟨75032946832954694266315667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50021964555303129510877111 75032946832954694266315667)
      ·
        refine ⟨112549420249432041399473501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75032946832954694266315667 112549420249432041399473501)
        ·
          refine ⟨42206032593537015524802563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112549420249432041399473501 42206032593537015524802563)
          ·
            refine ⟨63309048890305523287203845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42206032593537015524802563 63309048890305523287203845)
            ·
              refine ⟨11870446666932285616350721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63309048890305523287203845 11870446666932285616350721)
              ·
                refine ⟨8902835000199214212263041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11870446666932285616350721 8902835000199214212263041)
                ·
                  refine ⟨6677126250149410659197281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8902835000199214212263041 6677126250149410659197281)
                  ·
                    refine ⟨5007844687612057994397961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6677126250149410659197281 5007844687612057994397961)
                    ·
                      refine ⟨3755883515709043495798471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5007844687612057994397961 3755883515709043495798471)
                      ·
                        rfl

theorem cell23_7314557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_7314557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314557 prefixEnd_7314557 := by exact prefixLift 7314557
  have htrace : WordTrace (prefixWord ++ tailWord_7314557) baseStart_7314557 baseEnd_7314557 := by
    simpa [prefixWord, tailWord_7314557, baseEnd_7314557] using wordTrace_append hprefix tailTrace_7314557
  have hstable : (prefixWord ++ tailWord_7314557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314557).length < 2 ^ (prefixWord ++ tailWord_7314557).sum := by decide
  have hdescent : baseEnd_7314557 < baseStart_7314557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314563 : List Nat := [1, 1, 1, 3, 3, 2, 3, 4, 5]
def baseStart_7314563 : Nat := 118140960795 + 7314563 * 2 ^ 59
def prefixEnd_7314563 : Nat := 4983230072969 + 3 ^ 40 * 7314563 * 2
def baseEnd_7314563 : Nat := 417320732954774496924827

theorem tailTrace_7314563 : CollatzResearch.WordTrace tailWord_7314563 prefixEnd_7314563 417320732954774496924827 := by
  unfold tailWord_7314563
  simp only [CollatzResearch.WordTrace]
  refine ⟨266784029799594953749396343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177856019866396635832930895 266784029799594953749396343)
  ·
    refine ⟨400176044699392430624094515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266784029799594953749396343 400176044699392430624094515)
    ·
      refine ⟨600264067049088645936141773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400176044699392430624094515 600264067049088645936141773)
      ·
        refine ⟨225099025143408242226053165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600264067049088645936141773 225099025143408242226053165)
        ·
          refine ⟨84412134428778090834769937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225099025143408242226053165 84412134428778090834769937)
          ·
            refine ⟨63309100821583568126077453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84412134428778090834769937 63309100821583568126077453)
            ·
              refine ⟨23740912808093838047279045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63309100821583568126077453 23740912808093838047279045)
              ·
                refine ⟨4451421151517594633864821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23740912808093838047279045 4451421151517594633864821)
                ·
                  refine ⟨417320732954774496924827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451421151517594633864821 417320732954774496924827)
                  ·
                    rfl

theorem cell23_7314563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 5].length) (baseStart_7314563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314563 prefixEnd_7314563 := by exact prefixLift 7314563
  have htrace : WordTrace (prefixWord ++ tailWord_7314563) baseStart_7314563 baseEnd_7314563 := by
    simpa [prefixWord, tailWord_7314563, baseEnd_7314563] using wordTrace_append hprefix tailTrace_7314563
  have hstable : (prefixWord ++ tailWord_7314563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314563).length < 2 ^ (prefixWord ++ tailWord_7314563).sum := by decide
  have hdescent : baseEnd_7314563 < baseStart_7314563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314623 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 3, 4]
def baseStart_7314623 : Nat := 118140960795 + 7314623 * 2 ^ 59
def prefixEnd_7314623 : Nat := 4983230072969 + 3 ^ 40 * 7314623 * 2
def baseEnd_7314623 : Nat := 1251972468477413412524389

theorem tailTrace_7314623 : CollatzResearch.WordTrace tailWord_7314623 prefixEnd_7314623 1251972468477413412524389 := by
  unfold tailWord_7314623
  simp only [CollatzResearch.WordTrace]
  refine ⟨266786218179377583996580523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177857478786251722664387015 266786218179377583996580523)
  ·
    refine ⟨400179327269066375994870785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266786218179377583996580523 400179327269066375994870785)
    ·
      refine ⟨300134495451799781996153089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400179327269066375994870785 300134495451799781996153089)
      ·
        refine ⟨225100871588849836497114817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300134495451799781996153089 225100871588849836497114817)
        ·
          refine ⟨168825653691637377372836113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225100871588849836497114817 168825653691637377372836113)
          ·
            refine ⟨126619240268728033029627085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168825653691637377372836113 126619240268728033029627085)
            ·
              refine ⟨47482215100773012386110157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126619240268728033029627085 47482215100773012386110157)
              ·
                refine ⟨17805830662789879644791309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47482215100773012386110157 17805830662789879644791309)
                ·
                  refine ⟨6677186498546204866796741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17805830662789879644791309 6677186498546204866796741)
                  ·
                    refine ⟨1251972468477413412524389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677186498546204866796741 1251972468477413412524389)
                    ·
                      rfl

theorem cell23_7314623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_7314623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314623 prefixEnd_7314623 := by exact prefixLift 7314623
  have htrace : WordTrace (prefixWord ++ tailWord_7314623) baseStart_7314623 baseEnd_7314623 := by
    simpa [prefixWord, tailWord_7314623, baseEnd_7314623] using wordTrace_append hprefix tailTrace_7314623
  have hstable : (prefixWord ++ tailWord_7314623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314623).length < 2 ^ (prefixWord ++ tailWord_7314623).sum := by decide
  have hdescent : baseEnd_7314623 < baseStart_7314623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314657 : List Nat := [1, 2, 3, 1, 3, 2, 3, 3, 1, 4]
def baseStart_7314657 : Nat := 118140960795 + 7314657 * 2 ^ 59
def prefixEnd_7314657 : Nat := 4983230072969 + 3 ^ 40 * 7314657 * 2
def baseEnd_7314657 : Nat := 1251978287924831034849337

theorem tailTrace_7314657 : CollatzResearch.WordTrace tailWord_7314657 prefixEnd_7314657 1251978287924831034849337 := by
  unfold tailWord_7314657
  simp only [CollatzResearch.WordTrace]
  refine ⟨266787458261254407803318225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177858305507502938535545483 266787458261254407803318225)
  ·
    refine ⟨200090593695940805852488669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266787458261254407803318225 200090593695940805852488669)
    ·
      refine ⟨75033972635977802194683251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200090593695940805852488669 75033972635977802194683251)
      ·
        refine ⟨112550958953966703292024877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75033972635977802194683251 112550958953966703292024877)
        ·
          refine ⟨42206609607737513734509329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112550958953966703292024877 42206609607737513734509329)
          ·
            refine ⟨31654957205803135300881997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42206609607737513734509329 31654957205803135300881997)
            ·
              refine ⟨11870608952176175737830749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31654957205803135300881997 11870608952176175737830749)
              ·
                refine ⟨4451478357066065901686531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11870608952176175737830749 4451478357066065901686531)
                ·
                  refine ⟨6677217535599098852529797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451478357066065901686531 6677217535599098852529797)
                  ·
                    refine ⟨1251978287924831034849337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677217535599098852529797 1251978287924831034849337)
                    ·
                      rfl

theorem cell23_7314657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_7314657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314657 prefixEnd_7314657 := by exact prefixLift 7314657
  have htrace : WordTrace (prefixWord ++ tailWord_7314657) baseStart_7314657 baseEnd_7314657 := by
    simpa [prefixWord, tailWord_7314657, baseEnd_7314657] using wordTrace_append hprefix tailTrace_7314657
  have hstable : (prefixWord ++ tailWord_7314657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314657).length < 2 ^ (prefixWord ++ tailWord_7314657).sum := by decide
  have hdescent : baseEnd_7314657 < baseStart_7314657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314674 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_7314674 : Nat := 118140960795 + 7314674 * 2 ^ 59
def prefixEnd_7314674 : Nat := 4983230072969 + 3 ^ 40 * 7314674 * 2
def baseEnd_7314674 : Nat := 1251981197648539846011811

theorem tailTrace_7314674 : CollatzResearch.WordTrace tailWord_7314674 prefixEnd_7314674 1251981197648539846011811 := by
  unfold tailWord_7314674
  simp only [CollatzResearch.WordTrace]
  refine ⟨66697019575548204926671769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177858718868128546471124717 66697019575548204926671769)
  ·
    refine ⟨50022764681661153695003827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66697019575548204926671769 50022764681661153695003827)
    ·
      refine ⟨75034147022491730542505741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50022764681661153695003827 75034147022491730542505741)
      ·
        refine ⟨28137805133434398953439653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75034147022491730542505741 28137805133434398953439653)
        ·
          refine ⟨5275838462518949803769935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28137805133434398953439653 5275838462518949803769935)
          ·
            refine ⟨7913757693778424705654903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275838462518949803769935 7913757693778424705654903)
            ·
              refine ⟨11870636540667637058482355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913757693778424705654903 11870636540667637058482355)
              ·
                refine ⟨17805954811001455587723533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11870636540667637058482355 17805954811001455587723533)
                ·
                  refine ⟨6677233054125545845396325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17805954811001455587723533 6677233054125545845396325)
                  ·
                    refine ⟨1251981197648539846011811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677233054125545845396325 1251981197648539846011811)
                    ·
                      rfl

theorem cell23_7314674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_7314674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314674 prefixEnd_7314674 := by exact prefixLift 7314674
  have htrace : WordTrace (prefixWord ++ tailWord_7314674) baseStart_7314674 baseEnd_7314674 := by
    simpa [prefixWord, tailWord_7314674, baseEnd_7314674] using wordTrace_append hprefix tailTrace_7314674
  have hstable : (prefixWord ++ tailWord_7314674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314674).length < 2 ^ (prefixWord ++ tailWord_7314674).sum := by decide
  have hdescent : baseEnd_7314674 < baseStart_7314674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314700 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_7314700 : Nat := 118140960795 + 7314700 * 2 ^ 59
def prefixEnd_7314700 : Nat := 4983230072969 + 3 ^ 40 * 7314700 * 2
def baseEnd_7314700 : Nat := 1251985647814212145436771

theorem tailTrace_7314700 : CollatzResearch.WordTrace tailWord_7314700 prefixEnd_7314700 1251985647814212145436771 := by
  unfold tailWord_7314700
  simp only [CollatzResearch.WordTrace]
  refine ⟨133394513300049313073566777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177859351066732417431422369 133394513300049313073566777)
  ·
    refine ⟨100045884975036984805175083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133394513300049313073566777 100045884975036984805175083)
    ·
      refine ⟨150068827462555477207762625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100045884975036984805175083 150068827462555477207762625)
      ·
        refine ⟨112551620596916607905821969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150068827462555477207762625 112551620596916607905821969)
        ·
          refine ⟨84413715447687455929366477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112551620596916607905821969 84413715447687455929366477)
          ·
            refine ⟨31655143292882795973512429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84413715447687455929366477 31655143292882795973512429)
            ·
              refine ⟨11870678734831048490067161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31655143292882795973512429 11870678734831048490067161)
              ·
                refine ⟨8903009051123286367550371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11870678734831048490067161 8903009051123286367550371)
                ·
                  refine ⟨13354513576684929551325557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8903009051123286367550371 13354513576684929551325557)
                  ·
                    refine ⟨1251985647814212145436771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13354513576684929551325557 1251985647814212145436771)
                    ·
                      rfl

theorem cell23_7314700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_7314700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314700 prefixEnd_7314700 := by exact prefixLift 7314700
  have htrace : WordTrace (prefixWord ++ tailWord_7314700) baseStart_7314700 baseEnd_7314700 := by
    simpa [prefixWord, tailWord_7314700, baseEnd_7314700] using wordTrace_append hprefix tailTrace_7314700
  have hstable : (prefixWord ++ tailWord_7314700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314700).length < 2 ^ (prefixWord ++ tailWord_7314700).sum := by decide
  have hdescent : baseEnd_7314700 < baseStart_7314700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314740 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_7314740 : Nat := 118140960795 + 7314740 * 2 ^ 59
def prefixEnd_7314740 : Nat := 4983230072969 + 3 ^ 40 * 7314740 * 2
def baseEnd_7314740 : Nat := 3755977482668816279810129

theorem tailTrace_7314740 : CollatzResearch.WordTrace tailWord_7314740 prefixEnd_7314740 3755977482668816279810129 := by
  unfold tailWord_7314740
  simp only [CollatzResearch.WordTrace]
  refine ⟨133395242759976856489294837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177860323679969141985726449 133395242759976856489294837)
  ·
    refine ⟨12505804008747830295871391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133395242759976856489294837 12505804008747830295871391)
    ·
      refine ⟨18758706013121745443807087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12505804008747830295871391 18758706013121745443807087)
      ·
        refine ⟨28138059019682618165710631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18758706013121745443807087 28138059019682618165710631)
        ·
          refine ⟨42207088529523927248565947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28138059019682618165710631 42207088529523927248565947)
          ·
            refine ⟨63310632794285890872848921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42207088529523927248565947 63310632794285890872848921)
            ·
              refine ⟨47482974595714418154636691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63310632794285890872848921 47482974595714418154636691)
              ·
                refine ⟨71224461893571627231955037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47482974595714418154636691 71224461893571627231955037)
                ·
                  refine ⟨26709173210089360211983139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71224461893571627231955037 26709173210089360211983139)
                  ·
                    refine ⟨40063759815134040317974709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26709173210089360211983139 40063759815134040317974709)
                    ·
                      refine ⟨3755977482668816279810129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40063759815134040317974709 3755977482668816279810129)
                      ·
                        rfl

theorem cell23_7314740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_7314740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314740 prefixEnd_7314740 := by exact prefixLift 7314740
  have htrace : WordTrace (prefixWord ++ tailWord_7314740) baseStart_7314740 baseEnd_7314740 := by
    simpa [prefixWord, tailWord_7314740, baseEnd_7314740] using wordTrace_append hprefix tailTrace_7314740
  have hstable : (prefixWord ++ tailWord_7314740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314740).length < 2 ^ (prefixWord ++ tailWord_7314740).sum := by decide
  have hdescent : baseEnd_7314740 < baseStart_7314740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314781 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7314781 : Nat := 118140960795 + 7314781 * 2 ^ 59
def prefixEnd_7314781 : Nat := 4983230072969 + 3 ^ 40 * 7314781 * 2
def baseEnd_7314781 : Nat := 1251999511791883539799147

theorem tailTrace_7314781 : CollatzResearch.WordTrace tailWord_7314781 prefixEnd_7314781 1251999511791883539799147 := by
  unfold tailWord_7314781
  simp only [CollatzResearch.WordTrace]
  refine ⟨266791980912805176980832197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177861320608536784653888131 266791980912805176980832197)
  ·
    refine ⟨50023496421150970683906037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266791980912805176980832197 50023496421150970683906037)
    ·
      refine ⟨4689702789482903501616191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50023496421150970683906037 4689702789482903501616191)
      ·
        refine ⟨7034554184224355252424287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689702789482903501616191 7034554184224355252424287)
        ·
          refine ⟨10551831276336532878636431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7034554184224355252424287 10551831276336532878636431)
          ·
            refine ⟨15827746914504799317954647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10551831276336532878636431 15827746914504799317954647)
            ·
              refine ⟨23741620371757198976931971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15827746914504799317954647 23741620371757198976931971)
              ·
                refine ⟨35612430557635798465397957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23741620371757198976931971 35612430557635798465397957)
                ·
                  refine ⟨6677330729556712212262117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35612430557635798465397957 6677330729556712212262117)
                  ·
                    refine ⟨1251999511791883539799147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677330729556712212262117 1251999511791883539799147)
                    ·
                      rfl

theorem cell23_7314781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7314781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314781 prefixEnd_7314781 := by exact prefixLift 7314781
  have htrace : WordTrace (prefixWord ++ tailWord_7314781) baseStart_7314781 baseEnd_7314781 := by
    simpa [prefixWord, tailWord_7314781, baseEnd_7314781] using wordTrace_append hprefix tailTrace_7314781
  have hstable : (prefixWord ++ tailWord_7314781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314781).length < 2 ^ (prefixWord ++ tailWord_7314781).sum := by decide
  have hdescent : baseEnd_7314781 < baseStart_7314781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314787 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 3]
def baseStart_7314787 : Nat := 118140960795 + 7314787 * 2 ^ 59
def prefixEnd_7314787 : Nat := 4983230072969 + 3 ^ 40 * 7314787 * 2
def baseEnd_7314787 : Nat := 3756001616259577595922413

theorem tailTrace_7314787 : CollatzResearch.WordTrace tailWord_7314787 prefixEnd_7314787 3756001616259577595922413 := by
  unfold tailWord_7314787
  simp only [CollatzResearch.WordTrace]
  refine ⟨266792199750783440005550615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177861466500522293337033743 266792199750783440005550615)
  ·
    refine ⟨400188299626175160008325923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266792199750783440005550615 400188299626175160008325923)
    ·
      refine ⟨600282449439262740012488885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400188299626175160008325923 600282449439262740012488885)
      ·
        refine ⟨56276479634930881876170833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 600282449439262740012488885 56276479634930881876170833)
        ·
          refine ⟨42207359726198161407128125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56276479634930881876170833 42207359726198161407128125)
          ·
            refine ⟨15827759897324310527673047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42207359726198161407128125 15827759897324310527673047)
            ·
              refine ⟨23741639845986465791509571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15827759897324310527673047 23741639845986465791509571)
              ·
                refine ⟨35612459768979698687264357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23741639845986465791509571 35612459768979698687264357)
                ·
                  refine ⟨6677336206683693503862067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35612459768979698687264357 6677336206683693503862067)
                  ·
                    refine ⟨10016004310025540255793101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6677336206683693503862067 10016004310025540255793101)
                    ·
                      refine ⟨3756001616259577595922413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10016004310025540255793101 3756001616259577595922413)
                      ·
                        rfl

theorem cell23_7314787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_7314787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314787 prefixEnd_7314787 := by exact prefixLift 7314787
  have htrace : WordTrace (prefixWord ++ tailWord_7314787) baseStart_7314787 baseEnd_7314787 := by
    simpa [prefixWord, tailWord_7314787, baseEnd_7314787] using wordTrace_append hprefix tailTrace_7314787
  have hstable : (prefixWord ++ tailWord_7314787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314787).length < 2 ^ (prefixWord ++ tailWord_7314787).sum := by decide
  have hdescent : baseEnd_7314787 < baseStart_7314787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314793 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_7314793 : Nat := 118140960795 + 7314793 * 2 ^ 59
def prefixEnd_7314793 : Nat := 4983230072969 + 3 ^ 40 * 7314793 * 2
def baseEnd_7314793 : Nat := 3756004697143504572447385

theorem tailTrace_7314793 : CollatzResearch.WordTrace tailWord_7314793 prefixEnd_7314793 3756004697143504572447385 := by
  unfold tailWord_7314793
  simp only [CollatzResearch.WordTrace]
  refine ⟨266792418588761703030269033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177861612392507802020179355 266792418588761703030269033)
  ·
    refine ⟨200094313941571277272701775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266792418588761703030269033 200094313941571277272701775)
    ·
      refine ⟨300141470912356915909052663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200094313941571277272701775 300141470912356915909052663)
      ·
        refine ⟨450212206368535373863578995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300141470912356915909052663 450212206368535373863578995)
        ·
          refine ⟨675318309552803060795368493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450212206368535373863578995 675318309552803060795368493)
          ·
            refine ⟨253244366082301147798263185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675318309552803060795368493 253244366082301147798263185)
            ·
              refine ⟨189933274561725860848697389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253244366082301147798263185 189933274561725860848697389)
              ·
                refine ⟨71224977960647197818261521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189933274561725860848697389 71224977960647197818261521)
                ·
                  refine ⟨53418733470485398363696141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71224977960647197818261521 53418733470485398363696141)
                  ·
                    refine ⟨20032025051432024386386053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53418733470485398363696141 20032025051432024386386053)
                    ·
                      refine ⟨3756004697143504572447385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20032025051432024386386053 3756004697143504572447385)
                      ·
                        rfl

theorem cell23_7314793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_7314793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314793 prefixEnd_7314793 := by exact prefixLift 7314793
  have htrace : WordTrace (prefixWord ++ tailWord_7314793) baseStart_7314793 baseEnd_7314793 := by
    simpa [prefixWord, tailWord_7314793, baseEnd_7314793] using wordTrace_append hprefix tailTrace_7314793
  have hstable : (prefixWord ++ tailWord_7314793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314793).length < 2 ^ (prefixWord ++ tailWord_7314793).sum := by decide
  have hdescent : baseEnd_7314793 < baseStart_7314793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314827 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 6, 2, 2]
def baseStart_7314827 : Nat := 118140960795 + 7314827 * 2 ^ 59
def prefixEnd_7314827 : Nat := 4983230072969 + 3 ^ 40 * 7314827 * 2
def baseEnd_7314827 : Nat := 3756022155485757439422229

theorem tailTrace_7314827 : CollatzResearch.WordTrace tailWord_7314827 prefixEnd_7314827 3756022155485757439422229 := by
  unfold tailWord_7314827
  simp only [CollatzResearch.WordTrace]
  refine ⟨266793658670638526837006735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177862439113759017891337823 266793658670638526837006735)
  ·
    refine ⟨400190488005957790255510103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266793658670638526837006735 400190488005957790255510103)
    ·
      refine ⟨600285732008936685383265155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400190488005957790255510103 600285732008936685383265155)
      ·
        refine ⟨900428598013405028074897733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600285732008936685383265155 900428598013405028074897733)
        ·
          refine ⟨168830362127513442764043325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 900428598013405028074897733 168830362127513442764043325)
          ·
            refine ⟨63311385797817541036516247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168830362127513442764043325 63311385797817541036516247)
            ·
              refine ⟨94967078696726311554774371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63311385797817541036516247 94967078696726311554774371)
              ·
                refine ⟨142450618045089467332161557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94967078696726311554774371 142450618045089467332161557)
                ·
                  refine ⟨6677372720863568781195073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142450618045089467332161557 6677372720863568781195073)
                  ·
                    refine ⟨5008029540647676585896305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6677372720863568781195073 5008029540647676585896305)
                    ·
                      refine ⟨3756022155485757439422229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008029540647676585896305 3756022155485757439422229)
                      ·
                        rfl

theorem cell23_7314827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 2, 2].length) (baseStart_7314827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314827 prefixEnd_7314827 := by exact prefixLift 7314827
  have htrace : WordTrace (prefixWord ++ tailWord_7314827) baseStart_7314827 baseEnd_7314827 := by
    simpa [prefixWord, tailWord_7314827, baseEnd_7314827] using wordTrace_append hprefix tailTrace_7314827
  have hstable : (prefixWord ++ tailWord_7314827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314827).length < 2 ^ (prefixWord ++ tailWord_7314827).sum := by decide
  have hdescent : baseEnd_7314827 < baseStart_7314827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314853 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_7314853 : Nat := 118140960795 + 7314853 * 2 ^ 59
def prefixEnd_7314853 : Nat := 4983230072969 + 3 ^ 40 * 7314853 * 2
def baseEnd_7314853 : Nat := 3756035505982774337697109

theorem tailTrace_7314853 : CollatzResearch.WordTrace tailWord_7314853 prefixEnd_7314853 3756035505982774337697109 := by
  unfold tailWord_7314853
  simp only [CollatzResearch.WordTrace]
  refine ⟨266794606968544333277453213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177863071312362888851635475 266794606968544333277453213)
  ·
    refine ⟨100047977613204124979044955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266794606968544333277453213 100047977613204124979044955)
    ·
      refine ⟨150071966419806187468567433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100047977613204124979044955 150071966419806187468567433)
      ·
        refine ⟨112553974814854640601425575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150071966419806187468567433 112553974814854640601425575)
        ·
          refine ⟨168830962222281960902138363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112553974814854640601425575 168830962222281960902138363)
          ·
            refine ⟨253246443333422941353207545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168830962222281960902138363 253246443333422941353207545)
            ·
              refine ⟨189934832500067206014905659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253246443333422941353207545 189934832500067206014905659)
              ·
                refine ⟨284902248750100809022358489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189934832500067206014905659 284902248750100809022358489)
                ·
                  refine ⟨213676686562575606766768867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284902248750100809022358489 213676686562575606766768867)
                  ·
                    refine ⟨320515029843863410150153301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213676686562575606766768867 320515029843863410150153301)
                    ·
                      refine ⟨3756035505982774337697109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 320515029843863410150153301 3756035505982774337697109)
                      ·
                        rfl

theorem cell23_7314853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_7314853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314853 prefixEnd_7314853 := by exact prefixLift 7314853
  have htrace : WordTrace (prefixWord ++ tailWord_7314853) baseStart_7314853 baseEnd_7314853 := by
    simpa [prefixWord, tailWord_7314853, baseEnd_7314853] using wordTrace_append hprefix tailTrace_7314853
  have hstable : (prefixWord ++ tailWord_7314853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314853).length < 2 ^ (prefixWord ++ tailWord_7314853).sum := by decide
  have hdescent : baseEnd_7314853 < baseStart_7314853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314860 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_7314860 : Nat := 118140960795 + 7314860 * 2 ^ 59
def prefixEnd_7314860 : Nat := 4983230072969 + 3 ^ 40 * 7314860 * 2
def baseEnd_7314860 : Nat := 3756039100347355810309577

theorem tailTrace_7314860 : CollatzResearch.WordTrace tailWord_7314860 prefixEnd_7314860 3756039100347355810309577 := by
  unfold tailWord_7314860
  simp only [CollatzResearch.WordTrace]
  refine ⟨133397431139759486736479017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177863241519679315648638689 133397431139759486736479017)
  ·
    refine ⟨100048073354819615052359263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133397431139759486736479017 100048073354819615052359263)
    ·
      refine ⟨150072110032229422578538895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100048073354819615052359263 150072110032229422578538895)
      ·
        refine ⟨225108165048344133867808343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150072110032229422578538895 225108165048344133867808343)
        ·
          refine ⟨337662247572516200801712515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225108165048344133867808343 337662247572516200801712515)
          ·
            refine ⟨506493371358774301202568773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337662247572516200801712515 506493371358774301202568773)
            ·
              refine ⟨94967507129770181475481645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 506493371358774301202568773 94967507129770181475481645)
              ·
                refine ⟨35612815173663818053305617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94967507129770181475481645 35612815173663818053305617)
                ·
                  refine ⟨26709611380247863539979213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35612815173663818053305617 26709611380247863539979213)
                  ·
                    refine ⟨10016104267592948827492205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26709611380247863539979213 10016104267592948827492205)
                    ·
                      refine ⟨3756039100347355810309577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10016104267592948827492205 3756039100347355810309577)
                      ·
                        rfl

theorem cell23_7314860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_7314860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314860 prefixEnd_7314860 := by exact prefixLift 7314860
  have htrace : WordTrace (prefixWord ++ tailWord_7314860) baseStart_7314860 baseEnd_7314860 := by
    simpa [prefixWord, tailWord_7314860, baseEnd_7314860] using wordTrace_append hprefix tailTrace_7314860
  have hstable : (prefixWord ++ tailWord_7314860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314860).length < 2 ^ (prefixWord ++ tailWord_7314860).sum := by decide
  have hdescent : baseEnd_7314860 < baseStart_7314860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314863 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 3, 7]
def baseStart_7314863 : Nat := 118140960795 + 7314863 * 2 ^ 59
def prefixEnd_7314863 : Nat := 4983230072969 + 3 ^ 40 * 7314863 * 2
def baseEnd_7314863 : Nat := 1252013546929773099524021

theorem tailTrace_7314863 : CollatzResearch.WordTrace tailWord_7314863 prefixEnd_7314863 1252013546929773099524021 := by
  unfold tailWord_7314863
  simp only [CollatzResearch.WordTrace]
  refine ⟨266794971698508104985317243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177863314465672069990211495 266794971698508104985317243)
  ·
    refine ⟨400192457547762157477975865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266794971698508104985317243 400192457547762157477975865)
    ·
      refine ⟨300144343160821618108481899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400192457547762157477975865 300144343160821618108481899)
      ·
        refine ⟨450216514741232427162722849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300144343160821618108481899 450216514741232427162722849)
        ·
          refine ⟨337662386055924320372042137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450216514741232427162722849 337662386055924320372042137)
          ·
            refine ⟨253246789541943240279031603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337662386055924320372042137 253246789541943240279031603)
            ·
              refine ⟨379870184312914860418547405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253246789541943240279031603 379870184312914860418547405)
              ·
                refine ⟨142451319117343072656955277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379870184312914860418547405 142451319117343072656955277)
                ·
                  refine ⟨53419244669003652246358229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142451319117343072656955277 53419244669003652246358229)
                  ·
                    refine ⟨1252013546929773099524021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53419244669003652246358229 1252013546929773099524021)
                    ·
                      rfl

theorem cell23_7314863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_7314863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314863 prefixEnd_7314863 := by exact prefixLift 7314863
  have htrace : WordTrace (prefixWord ++ tailWord_7314863) baseStart_7314863 baseEnd_7314863 := by
    simpa [prefixWord, tailWord_7314863, baseEnd_7314863] using wordTrace_append hprefix tailTrace_7314863
  have hstable : (prefixWord ++ tailWord_7314863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314863).length < 2 ^ (prefixWord ++ tailWord_7314863).sum := by decide
  have hdescent : baseEnd_7314863 < baseStart_7314863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314880 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 2, 5]
def baseStart_7314880 : Nat := 118140960795 + 7314880 * 2 ^ 59
def prefixEnd_7314880 : Nat := 4983230072969 + 3 ^ 40 * 7314880 * 2
def baseEnd_7314880 : Nat := 1252016456653481910686495

theorem tailTrace_7314880 : CollatzResearch.WordTrace tailWord_7314880 prefixEnd_7314880 1252016456653481910686495 := by
  unfold tailWord_7314880
  simp only [CollatzResearch.WordTrace]
  refine ⟨133397795869723258444343047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177863727826297677925790729 133397795869723258444343047)
  ·
    refine ⟨200096693804584887666514571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133397795869723258444343047 200096693804584887666514571)
    ·
      refine ⟨300145040706877331499771857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200096693804584887666514571 300145040706877331499771857)
      ·
        refine ⟨225108780530157998624828893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300145040706877331499771857 225108780530157998624828893)
        ·
          refine ⟨84415792698809249484310835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225108780530157998624828893 84415792698809249484310835)
          ·
            refine ⟨126623689048213874226466253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84415792698809249484310835 126623689048213874226466253)
            ·
              refine ⟨47483883393080202834924845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126623689048213874226466253 47483883393080202834924845)
              ·
                refine ⟨17806456272405076063096817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47483883393080202834924845 17806456272405076063096817)
                ·
                  refine ⟨13354842204303807047322613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17806456272405076063096817 13354842204303807047322613)
                  ·
                    refine ⟨1252016456653481910686495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13354842204303807047322613 1252016456653481910686495)
                    ·
                      rfl

theorem cell23_7314880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_7314880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314880 prefixEnd_7314880 := by exact prefixLift 7314880
  have htrace : WordTrace (prefixWord ++ tailWord_7314880) baseStart_7314880 baseEnd_7314880 := by
    simpa [prefixWord, tailWord_7314880, baseEnd_7314880] using wordTrace_append hprefix tailTrace_7314880
  have hstable : (prefixWord ++ tailWord_7314880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314880).length < 2 ^ (prefixWord ++ tailWord_7314880).sum := by decide
  have hdescent : baseEnd_7314880 < baseStart_7314880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314890 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_7314890 : Nat := 118140960795 + 7314890 * 2 ^ 59
def prefixEnd_7314890 : Nat := 4983230072969 + 3 ^ 40 * 7314890 * 2
def baseEnd_7314890 : Nat := 3756054504766990692934439

theorem tailTrace_7314890 : CollatzResearch.WordTrace tailWord_7314890 prefixEnd_7314890 3756054504766990692934439 := by
  unfold tailWord_7314890
  simp only [CollatzResearch.WordTrace]
  refine ⟨66698989117352572149137531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177863970979606859064366749 66698989117352572149137531)
  ·
    refine ⟨100048483676028858223706297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66698989117352572149137531 100048483676028858223706297)
    ·
      refine ⟨75036362757021643667779723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100048483676028858223706297 75036362757021643667779723)
      ·
        refine ⟨112554544135532465501669585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75036362757021643667779723 112554544135532465501669585)
        ·
          refine ⟨84415908101649349126252189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112554544135532465501669585 84415908101649349126252189)
          ·
            refine ⟨31655965538118505922344571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84415908101649349126252189 31655965538118505922344571)
            ·
              refine ⟨47483948307177758883516857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31655965538118505922344571 47483948307177758883516857)
              ·
                refine ⟨35612961230383319162637643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47483948307177758883516857 35612961230383319162637643)
                ·
                  refine ⟨53419441845574978743956465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35612961230383319162637643 53419441845574978743956465)
                  ·
                    refine ⟨40064581384181234057967349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53419441845574978743956465 40064581384181234057967349)
                    ·
                      refine ⟨3756054504766990692934439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40064581384181234057967349 3756054504766990692934439)
                      ·
                        rfl

theorem cell23_7314890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_7314890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314890 prefixEnd_7314890 := by exact prefixLift 7314890
  have htrace : WordTrace (prefixWord ++ tailWord_7314890) baseStart_7314890 baseEnd_7314890 := by
    simpa [prefixWord, tailWord_7314890, baseEnd_7314890] using wordTrace_append hprefix tailTrace_7314890
  have hstable : (prefixWord ++ tailWord_7314890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314890).length < 2 ^ (prefixWord ++ tailWord_7314890).sum := by decide
  have hdescent : baseEnd_7314890 < baseStart_7314890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314934 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_7314934 : Nat := 118140960795 + 7314934 * 2 ^ 59
def prefixEnd_7314934 : Nat := 4983230072969 + 3 ^ 40 * 7314934 * 2
def baseEnd_7314934 : Nat := 3756077097915788520784237

theorem tailTrace_7314934 : CollatzResearch.WordTrace tailWord_7314934 prefixEnd_7314934 3756077097915788520784237 := by
  unfold tailWord_7314934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674847580078180256946991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177865040854167256074101237 16674847580078180256946991)
  ·
    refine ⟨25012271370117270385420487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16674847580078180256946991 25012271370117270385420487)
    ·
      refine ⟨37518407055175905578130731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25012271370117270385420487 37518407055175905578130731)
      ·
        refine ⟨56277610582763858367196097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37518407055175905578130731 56277610582763858367196097)
        ·
          refine ⟨42208207937072893775397073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56277610582763858367196097 42208207937072893775397073)
          ·
            refine ⟨31656155952804670331547805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42208207937072893775397073 31656155952804670331547805)
            ·
              refine ⟨11871058482301751374330427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31656155952804670331547805 11871058482301751374330427)
              ·
                refine ⟨17806587723452627061495641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11871058482301751374330427 17806587723452627061495641)
                ·
                  refine ⟨13354940792589470296121731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17806587723452627061495641 13354940792589470296121731)
                  ·
                    refine ⟨20032411188884205444182597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13354940792589470296121731 20032411188884205444182597)
                    ·
                      refine ⟨3756077097915788520784237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20032411188884205444182597 3756077097915788520784237)
                      ·
                        rfl

theorem cell23_7314934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_7314934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314934 prefixEnd_7314934 := by exact prefixLift 7314934
  have htrace : WordTrace (prefixWord ++ tailWord_7314934) baseStart_7314934 baseEnd_7314934 := by
    simpa [prefixWord, tailWord_7314934, baseEnd_7314934] using wordTrace_append hprefix tailTrace_7314934
  have hstable : (prefixWord ++ tailWord_7314934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314934).length < 2 ^ (prefixWord ++ tailWord_7314934).sum := by decide
  have hdescent : baseEnd_7314934 < baseStart_7314934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314994 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_7314994 : Nat := 118140960795 + 7314994 * 2 ^ 59
def prefixEnd_7314994 : Nat := 4983230072969 + 3 ^ 40 * 7314994 * 2
def baseEnd_7314994 : Nat := 3756107906755058286033961

theorem tailTrace_7314994 : CollatzResearch.WordTrace tailWord_7314994 prefixEnd_7314994 3756107906755058286033961 := by
  unfold tailWord_7314994
  simp only [CollatzResearch.WordTrace]
  refine ⟨66699937415258378589584009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177866499774022342905557357 66699937415258378589584009)
  ·
    refine ⟨50024953061443783942188007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66699937415258378589584009 50024953061443783942188007)
    ·
      refine ⟨75037429592165675913282011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50024953061443783942188007 75037429592165675913282011)
      ·
        refine ⟨112556144388248513869923017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75037429592165675913282011 112556144388248513869923017)
        ·
          refine ⟨84417108291186385402442263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112556144388248513869923017 84417108291186385402442263)
          ·
            refine ⟨126625662436779578103663395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84417108291186385402442263 126625662436779578103663395)
            ·
              refine ⟨189938493655169367155495093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126625662436779578103663395 189938493655169367155495093)
              ·
                refine ⟨17806733780172128170827665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189938493655169367155495093 17806733780172128170827665)
                ·
                  refine ⟨13355050335129096128120749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17806733780172128170827665 13355050335129096128120749)
                  ·
                    refine ⟨5008143875673411048045281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13355050335129096128120749 5008143875673411048045281)
                    ·
                      refine ⟨3756107906755058286033961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008143875673411048045281 3756107906755058286033961)
                      ·
                        rfl

theorem cell23_7314994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_7314994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7314994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7314994 prefixEnd_7314994 := by exact prefixLift 7314994
  have htrace : WordTrace (prefixWord ++ tailWord_7314994) baseStart_7314994 baseEnd_7314994 := by
    simpa [prefixWord, tailWord_7314994, baseEnd_7314994] using wordTrace_append hprefix tailTrace_7314994
  have hstable : (prefixWord ++ tailWord_7314994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314994).length < 2 ^ (prefixWord ++ tailWord_7314994).sum := by decide
  have hdescent : baseEnd_7314994 < baseStart_7314994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315018 : List Nat := [3, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_7315018 : Nat := 118140960795 + 7315018 * 2 ^ 59
def prefixEnd_7315018 : Nat := 4983230072969 + 3 ^ 40 * 7315018 * 2
def baseEnd_7315018 : Nat := 3756120230290766192133851

theorem tailTrace_7315018 : CollatzResearch.WordTrace tailWord_7315018 prefixEnd_7315018 3756120230290766192133851 := by
  unfold tailWord_7315018
  simp only [CollatzResearch.WordTrace]
  refine ⟨66700156253236641614302427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177867083341964377638139805 66700156253236641614302427)
  ·
    refine ⟨100050234379854962421453641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66700156253236641614302427 100050234379854962421453641)
    ·
      refine ⟨75037675784891221816090231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100050234379854962421453641 75037675784891221816090231)
      ·
        refine ⟨112556513677336832724135347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75037675784891221816090231 112556513677336832724135347)
        ·
          refine ⟨168834770516005249086203021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112556513677336832724135347 168834770516005249086203021)
          ·
            refine ⟨63313038943501968407326133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168834770516005249086203021 63313038943501968407326133)
            ·
              refine ⟨5935597400953309538186825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63313038943501968407326133 5935597400953309538186825)
              ·
                refine ⟨4451698050714982153640119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935597400953309538186825 4451698050714982153640119)
                ·
                  refine ⟨6677547076072473230460179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451698050714982153640119 6677547076072473230460179)
                  ·
                    refine ⟨10016320614108709845690269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6677547076072473230460179 10016320614108709845690269)
                    ·
                      refine ⟨3756120230290766192133851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10016320614108709845690269 3756120230290766192133851)
                      ·
                        rfl

theorem cell23_7315018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_7315018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315018 prefixEnd_7315018 := by exact prefixLift 7315018
  have htrace : WordTrace (prefixWord ++ tailWord_7315018) baseStart_7315018 baseEnd_7315018 := by
    simpa [prefixWord, tailWord_7315018, baseEnd_7315018] using wordTrace_append hprefix tailTrace_7315018
  have hstable : (prefixWord ++ tailWord_7315018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315018).length < 2 ^ (prefixWord ++ tailWord_7315018).sum := by decide
  have hdescent : baseEnd_7315018 < baseStart_7315018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315044 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_7315044 : Nat := 118140960795 + 7315044 * 2 ^ 59
def prefixEnd_7315044 : Nat := 4983230072969 + 3 ^ 40 * 7315044 * 2
def baseEnd_7315044 : Nat := 3756133580787783090408731

theorem tailTrace_7315044 : CollatzResearch.WordTrace tailWord_7315044 prefixEnd_7315044 3756133580787783090408731 := by
  unfold tailWord_7315044
  simp only [CollatzResearch.WordTrace]
  refine ⟨133400786655426186448828093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177867715540568248598437457 133400786655426186448828093)
  ·
    refine ⟨50025294995784819918310535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133400786655426186448828093 50025294995784819918310535)
    ·
      refine ⟨75037942493677229877465803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50025294995784819918310535 75037942493677229877465803)
      ·
        refine ⟨112556913740515844816198705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75037942493677229877465803 112556913740515844816198705)
        ·
          refine ⟨84417685305386883612149029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112556913740515844816198705 84417685305386883612149029)
          ·
            refine ⟨15828315994760040677277943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84417685305386883612149029 15828315994760040677277943)
            ·
              refine ⟨23742473992140061015916915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15828315994760040677277943 23742473992140061015916915)
              ·
                refine ⟨35613710988210091523875373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23742473992140061015916915 35613710988210091523875373)
                ·
                  refine ⟨13355141620578784321453265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35613710988210091523875373 13355141620578784321453265)
                  ·
                    refine ⟨10016356215434088241089949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13355141620578784321453265 10016356215434088241089949)
                    ·
                      refine ⟨3756133580787783090408731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10016356215434088241089949 3756133580787783090408731)
                      ·
                        rfl

theorem cell23_7315044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_7315044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315044 prefixEnd_7315044 := by exact prefixLift 7315044
  have htrace : WordTrace (prefixWord ++ tailWord_7315044) baseStart_7315044 baseEnd_7315044 := by
    simpa [prefixWord, tailWord_7315044, baseEnd_7315044] using wordTrace_append hprefix tailTrace_7315044
  have hstable : (prefixWord ++ tailWord_7315044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315044).length < 2 ^ (prefixWord ++ tailWord_7315044).sum := by decide
  have hdescent : baseEnd_7315044 < baseStart_7315044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315061 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7315061 : Nat := 118140960795 + 7315061 * 2 ^ 59
def prefixEnd_7315061 : Nat := 4983230072969 + 3 ^ 40 * 7315061 * 2
def baseEnd_7315061 : Nat := 3756142309958909523896153

theorem tailTrace_7315061 : CollatzResearch.WordTrace tailWord_7315061 prefixEnd_7315061 3756142309958909523896153 := by
  unfold tailWord_7315061
  simp only [CollatzResearch.WordTrace]
  refine ⟨266802193351790784801025037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177868128901193856534016691 266802193351790784801025037)
  ·
    refine ⟨100050822506921544300384389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266802193351790784801025037 100050822506921544300384389)
    ·
      refine ⟨18759529220047789556322073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100050822506921544300384389 18759529220047789556322073)
      ·
        refine ⟨14069646915035842167241555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18759529220047789556322073 14069646915035842167241555)
        ·
          refine ⟨21104470372553763250862333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14069646915035842167241555 21104470372553763250862333)
          ·
            refine ⟨7914176389707661219073375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21104470372553763250862333 7914176389707661219073375)
            ·
              refine ⟨11871264584561491828610063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7914176389707661219073375 11871264584561491828610063)
              ·
                refine ⟨17806896876842237742915095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11871264584561491828610063 17806896876842237742915095)
                ·
                  refine ⟨26710345315263356614372643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17806896876842237742915095 26710345315263356614372643)
                  ·
                    refine ⟨40065517972895034921558965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26710345315263356614372643 40065517972895034921558965)
                    ·
                      refine ⟨3756142309958909523896153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40065517972895034921558965 3756142309958909523896153)
                      ·
                        rfl

theorem cell23_7315061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7315061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315061 prefixEnd_7315061 := by exact prefixLift 7315061
  have htrace : WordTrace (prefixWord ++ tailWord_7315061) baseStart_7315061 baseEnd_7315061 := by
    simpa [prefixWord, tailWord_7315061, baseEnd_7315061] using wordTrace_append hprefix tailTrace_7315061
  have hstable : (prefixWord ++ tailWord_7315061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315061).length < 2 ^ (prefixWord ++ tailWord_7315061).sum := by decide
  have hdescent : baseEnd_7315061 < baseStart_7315061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315084 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 5, 3, 2]
def baseStart_7315084 : Nat := 118140960795 + 7315084 * 2 ^ 59
def prefixEnd_7315084 : Nat := 4983230072969 + 3 ^ 40 * 7315084 * 2
def baseEnd_7315084 : Nat := 3756154120013962933908547

theorem tailTrace_7315084 : CollatzResearch.WordTrace tailWord_7315084 prefixEnd_7315084 3756154120013962933908547 := by
  unfold tailWord_7315084
  simp only [CollatzResearch.WordTrace]
  refine ⟨133401516115353729864556153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177868688153804973152741537 133401516115353729864556153)
  ·
    refine ⟨100051137086515297398417115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133401516115353729864556153 100051137086515297398417115)
    ·
      refine ⟨150076705629772946097625673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100051137086515297398417115 150076705629772946097625673)
      ·
        refine ⟨112557529222329709573219255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150076705629772946097625673 112557529222329709573219255)
        ·
          refine ⟨168836293833494564359828883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112557529222329709573219255 168836293833494564359828883)
          ·
            refine ⟨253254440750241846539743325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168836293833494564359828883 253254440750241846539743325)
            ·
              refine ⟨94970415281340692452403747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253254440750241846539743325 94970415281340692452403747)
              ·
                refine ⟨142455622922011038678605621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94970415281340692452403747 142455622922011038678605621)
                ·
                  refine ⟨13355214648938534876119277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142455622922011038678605621 13355214648938534876119277)
                  ·
                    refine ⟨5008205493351950578544729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13355214648938534876119277 5008205493351950578544729)
                    ·
                      refine ⟨3756154120013962933908547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008205493351950578544729 3756154120013962933908547)
                      ·
                        rfl

theorem cell23_7315084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_7315084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315084 prefixEnd_7315084 := by exact prefixLift 7315084
  have htrace : WordTrace (prefixWord ++ tailWord_7315084) baseStart_7315084 baseEnd_7315084 := by
    simpa [prefixWord, tailWord_7315084, baseEnd_7315084] using wordTrace_append hprefix tailTrace_7315084
  have hstable : (prefixWord ++ tailWord_7315084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315084).length < 2 ^ (prefixWord ++ tailWord_7315084).sum := by decide
  have hdescent : baseEnd_7315084 < baseStart_7315084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315101 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_7315101 : Nat := 118140960795 + 7315101 * 2 ^ 59
def prefixEnd_7315101 : Nat := 4983230072969 + 3 ^ 40 * 7315101 * 2
def baseEnd_7315101 : Nat := 3756162849185089367395969

theorem tailTrace_7315101 : CollatzResearch.WordTrace tailWord_7315101 prefixEnd_7315101 3756162849185089367395969 := by
  unfold tailWord_7315101
  simp only [CollatzResearch.WordTrace]
  refine ⟨266803652271645871632481157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177869101514430581088320771 266803652271645871632481157)
  ·
    refine ⟨50025684800933600931090217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266803652271645871632481157 50025684800933600931090217)
    ·
      refine ⟨37519263600700200698317663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50025684800933600931090217 37519263600700200698317663)
      ·
        refine ⟨56278895401050301047476495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37519263600700200698317663 56278895401050301047476495)
        ·
          refine ⟨84418343101575451571214743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56278895401050301047476495 84418343101575451571214743)
          ·
            refine ⟨126627514652363177356822115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84418343101575451571214743 126627514652363177356822115)
            ·
              refine ⟨189941271978544766035233173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126627514652363177356822115 189941271978544766035233173)
              ·
                refine ⟨8903497123994285907901555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189941271978544766035233173 8903497123994285907901555)
                ·
                  refine ⟨13355245685991428861852333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8903497123994285907901555 13355245685991428861852333)
                  ·
                    refine ⟨5008217132246785823194625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13355245685991428861852333 5008217132246785823194625)
                    ·
                      refine ⟨3756162849185089367395969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008217132246785823194625 3756162849185089367395969)
                      ·
                        rfl

theorem cell23_7315101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_7315101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315101 prefixEnd_7315101 := by exact prefixLift 7315101
  have htrace : WordTrace (prefixWord ++ tailWord_7315101) baseStart_7315101 baseEnd_7315101 := by
    simpa [prefixWord, tailWord_7315101, baseEnd_7315101] using wordTrace_append hprefix tailTrace_7315101
  have hstable : (prefixWord ++ tailWord_7315101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315101).length < 2 ^ (prefixWord ++ tailWord_7315101).sum := by decide
  have hdescent : baseEnd_7315101 < baseStart_7315101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315125 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7315125 : Nat := 118140960795 + 7315125 * 2 ^ 59
def prefixEnd_7315125 : Nat := 4983230072969 + 3 ^ 40 * 7315125 * 2
def baseEnd_7315125 : Nat := 3756175172720797273495859

theorem tailTrace_7315125 : CollatzResearch.WordTrace tailWord_7315125 prefixEnd_7315125 3756175172720797273495859 := by
  unfold tailWord_7315125
  simp only [CollatzResearch.WordTrace]
  refine ⟨266804527623558923731354829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177869685082372615820903219 266804527623558923731354829)
  ·
    refine ⟨100051697858834596399258061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266804527623558923731354829 100051697858834596399258061)
    ·
      refine ⟨37519386697062973649721773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100051697858834596399258061 37519386697062973649721773)
      ·
        refine ⟨14069770011398615118645665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37519386697062973649721773 14069770011398615118645665)
        ·
          refine ⟨10552327508548961338984249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14069770011398615118645665 10552327508548961338984249)
          ·
            refine ⟨7914245631411721004238187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10552327508548961338984249 7914245631411721004238187)
            ·
              refine ⟨11871368447117581506357281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7914245631411721004238187 11871368447117581506357281)
              ·
                refine ⟨8903526335338186129767961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11871368447117581506357281 8903526335338186129767961)
                ·
                  refine ⟨6677644751503639597325971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8903526335338186129767961 6677644751503639597325971)
                  ·
                    refine ⟨10016467127255459395988957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6677644751503639597325971 10016467127255459395988957)
                    ·
                      refine ⟨3756175172720797273495859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10016467127255459395988957 3756175172720797273495859)
                      ·
                        rfl

theorem cell23_7315125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7315125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315125 prefixEnd_7315125 := by exact prefixLift 7315125
  have htrace : WordTrace (prefixWord ++ tailWord_7315125) baseStart_7315125 baseEnd_7315125 := by
    simpa [prefixWord, tailWord_7315125, baseEnd_7315125] using wordTrace_append hprefix tailTrace_7315125
  have hstable : (prefixWord ++ tailWord_7315125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315125).length < 2 ^ (prefixWord ++ tailWord_7315125).sum := by decide
  have hdescent : baseEnd_7315125 < baseStart_7315125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315154 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 7]
def baseStart_7315154 : Nat := 118140960795 + 7315154 * 2 ^ 59
def prefixEnd_7315154 : Nat := 4983230072969 + 3 ^ 40 * 7315154 * 2
def baseEnd_7315154 : Nat := 417354451517753073337025

theorem tailTrace_7315154 : CollatzResearch.WordTrace tailWord_7315154 prefixEnd_7315154 417354451517753073337025 := by
  unfold tailWord_7315154
  simp only [CollatzResearch.WordTrace]
  refine ⟨66701396335113465421040129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177870390226969241122773677 66701396335113465421040129)
  ·
    refine ⟨50026047251335099065780097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66701396335113465421040129 50026047251335099065780097)
    ·
      refine ⟨37519535438501324299335073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50026047251335099065780097 37519535438501324299335073)
      ·
        refine ⟨28139651578875993224501305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37519535438501324299335073 28139651578875993224501305)
        ·
          refine ⟨21104738684156994918375979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28139651578875993224501305 21104738684156994918375979)
          ·
            refine ⟨31657108026235492377563969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21104738684156994918375979 31657108026235492377563969)
            ·
              refine ⟨23742831019676619283172977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31657108026235492377563969 23742831019676619283172977)
              ·
                refine ⟨17807123264757464462379733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23742831019676619283172977 17807123264757464462379733)
                ·
                  refine ⟨417354451517753073337025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17807123264757464462379733 417354451517753073337025)
                  ·
                    rfl

theorem cell23_7315154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_7315154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315154 prefixEnd_7315154 := by exact prefixLift 7315154
  have htrace : WordTrace (prefixWord ++ tailWord_7315154) baseStart_7315154 baseEnd_7315154 := by
    simpa [prefixWord, tailWord_7315154, baseEnd_7315154] using wordTrace_append hprefix tailTrace_7315154
  have hstable : (prefixWord ++ tailWord_7315154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315154).length < 2 ^ (prefixWord ++ tailWord_7315154).sum := by decide
  have hdescent : baseEnd_7315154 < baseStart_7315154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315167 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 1, 7]
def baseStart_7315167 : Nat := 118140960795 + 7315167 * 2 ^ 59
def prefixEnd_7315167 : Nat := 4983230072969 + 3 ^ 40 * 7315167 * 2
def baseEnd_7315167 : Nat := 1252065579636095369723555

theorem tailTrace_7315167 : CollatzResearch.WordTrace tailWord_7315167 prefixEnd_7315167 1252065579636095369723555 := by
  unfold tailWord_7315167
  simp only [CollatzResearch.WordTrace]
  refine ⟨266806059489406764904383755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177870706326271176602922503 266806059489406764904383755)
  ·
    refine ⟨400209089234110147356575633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266806059489406764904383755 400209089234110147356575633)
    ·
      refine ⟨300156816925582610517431725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400209089234110147356575633 300156816925582610517431725)
      ·
        refine ⟨112558806347093478944036897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300156816925582610517431725 112558806347093478944036897)
        ·
          refine ⟨84419104760320109208027673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112558806347093478944036897 84419104760320109208027673)
          ·
            refine ⟨63314328570240081906020755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84419104760320109208027673 63314328570240081906020755)
            ·
              refine ⟨94971492855360122859031133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63314328570240081906020755 94971492855360122859031133)
              ·
                refine ⟨35614309820760046072136675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94971492855360122859031133 35614309820760046072136675)
                ·
                  refine ⟨53421464731140069108205013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35614309820760046072136675 53421464731140069108205013)
                  ·
                    refine ⟨1252065579636095369723555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53421464731140069108205013 1252065579636095369723555)
                    ·
                      rfl

theorem cell23_7315167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_7315167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315167 prefixEnd_7315167 := by exact prefixLift 7315167
  have htrace : WordTrace (prefixWord ++ tailWord_7315167) baseStart_7315167 baseEnd_7315167 := by
    simpa [prefixWord, tailWord_7315167, baseEnd_7315167] using wordTrace_append hprefix tailTrace_7315167
  have hstable : (prefixWord ++ tailWord_7315167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315167).length < 2 ^ (prefixWord ++ tailWord_7315167).sum := by decide
  have hdescent : baseEnd_7315167 < baseStart_7315167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315177 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_7315177 : Nat := 118140960795 + 7315177 * 2 ^ 59
def prefixEnd_7315177 : Nat := 4983230072969 + 3 ^ 40 * 7315177 * 2
def baseEnd_7315177 : Nat := 3756201873714831070045619

theorem tailTrace_7315177 : CollatzResearch.WordTrace tailWord_7315177 prefixEnd_7315177 3756201873714831070045619 := by
  unfold tailWord_7315177
  simp only [CollatzResearch.WordTrace]
  refine ⟨266806424219370536612247785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177870949479580357741498523 266806424219370536612247785)
  ·
    refine ⟨200104818164527902459185839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266806424219370536612247785 200104818164527902459185839)
    ·
      refine ⟨300157227246791853688778759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200104818164527902459185839 300157227246791853688778759)
      ·
        refine ⟨450235840870187780533168139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300157227246791853688778759 450235840870187780533168139)
        ·
          refine ⟨675353761305281670799752209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450235840870187780533168139 675353761305281670799752209)
          ·
            refine ⟨506515320978961253099814157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675353761305281670799752209 506515320978961253099814157)
            ·
              refine ⟨189943245367110469912430309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506515320978961253099814157 189943245367110469912430309)
              ·
                refine ⟨35614358506333213108580683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189943245367110469912430309 35614358506333213108580683)
                ·
                  refine ⟨53421537759499819662871025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35614358506333213108580683 53421537759499819662871025)
                  ·
                    refine ⟨40066153319624864747153269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53421537759499819662871025 40066153319624864747153269)
                    ·
                      refine ⟨3756201873714831070045619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40066153319624864747153269 3756201873714831070045619)
                      ·
                        rfl

theorem cell23_7315177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_7315177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315177 prefixEnd_7315177 := by exact prefixLift 7315177
  have htrace : WordTrace (prefixWord ++ tailWord_7315177) baseStart_7315177 baseEnd_7315177 := by
    simpa [prefixWord, tailWord_7315177, baseEnd_7315177] using wordTrace_append hprefix tailTrace_7315177
  have hstable : (prefixWord ++ tailWord_7315177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315177).length < 2 ^ (prefixWord ++ tailWord_7315177).sum := by decide
  have hdescent : baseEnd_7315177 < baseStart_7315177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315188 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7315188 : Nat := 118140960795 + 7315188 * 2 ^ 59
def prefixEnd_7315188 : Nat := 4983230072969 + 3 ^ 40 * 7315188 * 2
def baseEnd_7315188 : Nat := 417356391333558947445341

theorem tailTrace_7315188 : CollatzResearch.WordTrace tailWord_7315188 prefixEnd_7315188 417356391333558947445341 := by
  unfold tailWord_7315188
  simp only [CollatzResearch.WordTrace]
  refine ⟨133403412711165342745449109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177871216948220456993932145 133403412711165342745449109)
  ·
    refine ⟨6253284970835875441192927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133403412711165342745449109 6253284970835875441192927)
    ·
      refine ⟨9379927456253813161789391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6253284970835875441192927 9379927456253813161789391)
      ·
        refine ⟨14069891184380719742684087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9379927456253813161789391 14069891184380719742684087)
        ·
          refine ⟨21104836776571079614026131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14069891184380719742684087 21104836776571079614026131)
          ·
            refine ⟨31657255164856619421039197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21104836776571079614026131 31657255164856619421039197)
            ·
              refine ⟨11871470686821232282889699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31657255164856619421039197 11871470686821232282889699)
              ·
                refine ⟨17807206030231848424334549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11871470686821232282889699 17807206030231848424334549)
                ·
                  refine ⟨417356391333558947445341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17807206030231848424334549 417356391333558947445341)
                  ·
                    rfl

theorem cell23_7315188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7315188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315188 prefixEnd_7315188 := by exact prefixLift 7315188
  have htrace : WordTrace (prefixWord ++ tailWord_7315188) baseStart_7315188 baseEnd_7315188 := by
    simpa [prefixWord, tailWord_7315188, baseEnd_7315188] using wordTrace_append hprefix tailTrace_7315188
  have hstable : (prefixWord ++ tailWord_7315188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315188).length < 2 ^ (prefixWord ++ tailWord_7315188).sum := by decide
  have hdescent : baseEnd_7315188 < baseStart_7315188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315197 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_7315197 : Nat := 118140960795 + 7315197 * 2 ^ 59
def prefixEnd_7315197 : Nat := 4983230072969 + 3 ^ 40 * 7315197 * 2
def baseEnd_7315197 : Nat := 1252070714442640330598509

theorem tailTrace_7315197 : CollatzResearch.WordTrace tailWord_7315197 prefixEnd_7315197 1252070714442640330598509 := by
  unfold tailWord_7315197
  simp only [CollatzResearch.WordTrace]
  refine ⟨266807153679298080027975845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177871435786198720018650563 266807153679298080027975845)
  ·
    refine ⟨50026341314868390005245471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266807153679298080027975845 50026341314868390005245471)
    ·
      refine ⟨75039511972302585007868207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50026341314868390005245471 75039511972302585007868207)
      ·
        refine ⟨112559267958453877511802311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75039511972302585007868207 112559267958453877511802311)
        ·
          refine ⟨168838901937680816267703467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112559267958453877511802311 168838901937680816267703467)
          ·
            refine ⟨253258352906521224401555201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168838901937680816267703467 253258352906521224401555201)
            ·
              refine ⟨189943764679890918301166401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253258352906521224401555201 189943764679890918301166401)
              ·
                refine ⟨142457823509918188725874801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189943764679890918301166401 142457823509918188725874801)
                ·
                  refine ⟨106843367632438641544406101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142457823509918188725874801 106843367632438641544406101)
                  ·
                    refine ⟨1252070714442640330598509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106843367632438641544406101 1252070714442640330598509)
                    ·
                      rfl

theorem cell23_7315197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_7315197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315197 prefixEnd_7315197 := by exact prefixLift 7315197
  have htrace : WordTrace (prefixWord ++ tailWord_7315197) baseStart_7315197 baseEnd_7315197 := by
    simpa [prefixWord, tailWord_7315197, baseEnd_7315197] using wordTrace_append hprefix tailTrace_7315197
  have hstable : (prefixWord ++ tailWord_7315197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315197).length < 2 ^ (prefixWord ++ tailWord_7315197).sum := by decide
  have hdescent : baseEnd_7315197 < baseStart_7315197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315217 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_7315217 : Nat := 118140960795 + 7315217 * 2 ^ 59
def prefixEnd_7315217 : Nat := 4983230072969 + 3 ^ 40 * 7315217 * 2
def baseEnd_7315217 : Nat := 3756222412941010913545435

theorem tailTrace_7315217 : CollatzResearch.WordTrace tailWord_7315217 prefixEnd_7315217 3756222412941010913545435 := by
  unfold tailWord_7315217
  simp only [CollatzResearch.WordTrace]
  refine ⟨266807883139225623443703905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177871922092817082295802603 266807883139225623443703905)
  ·
    refine ⟨200105912354419217582777929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266807883139225623443703905 200105912354419217582777929)
    ·
      refine ⟨150079434265814413187083447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200105912354419217582777929 150079434265814413187083447)
      ·
        refine ⟨225119151398721619780625171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150079434265814413187083447 225119151398721619780625171)
        ·
          refine ⟨337678727098082429670937757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225119151398721619780625171 337678727098082429670937757)
          ·
            refine ⟨126629522661780911126601659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337678727098082429670937757 126629522661780911126601659)
            ·
              refine ⟨189944283992671366689902489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126629522661780911126601659 189944283992671366689902489)
              ·
                refine ⟨142458212994503525017426867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189944283992671366689902489 142458212994503525017426867)
                ·
                  refine ⟨213687319491755287526140301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142458212994503525017426867 213687319491755287526140301)
                  ·
                    refine ⟨80132744809408232822302613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213687319491755287526140301 80132744809408232822302613)
                    ·
                      refine ⟨3756222412941010913545435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80132744809408232822302613 3756222412941010913545435)
                      ·
                        rfl

theorem cell23_7315217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_7315217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315217 prefixEnd_7315217 := by exact prefixLift 7315217
  have htrace : WordTrace (prefixWord ++ tailWord_7315217) baseStart_7315217 baseEnd_7315217 := by
    simpa [prefixWord, tailWord_7315217, baseEnd_7315217] using wordTrace_append hprefix tailTrace_7315217
  have hstable : (prefixWord ++ tailWord_7315217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315217).length < 2 ^ (prefixWord ++ tailWord_7315217).sum := by decide
  have hdescent : baseEnd_7315217 < baseStart_7315217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315218 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7315218 : Nat := 118140960795 + 7315218 * 2 ^ 59
def prefixEnd_7315218 : Nat := 4983230072969 + 3 ^ 40 * 7315218 * 2
def baseEnd_7315218 : Nat := 1252074308807221803210977

theorem tailTrace_7315218 : CollatzResearch.WordTrace tailWord_7315218 prefixEnd_7315218 1252074308807221803210977 := by
  unfold tailWord_7315218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66701979903055500153622577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177871946408148000409660205 66701979903055500153622577)
  ·
    refine ⟨50026484927291625115216933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66701979903055500153622577 50026484927291625115216933)
    ·
      refine ⟨9379965923867179709103175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50026484927291625115216933 9379965923867179709103175)
      ·
        refine ⟨14069948885800769563654763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9379965923867179709103175 14069948885800769563654763)
        ·
          refine ⟨21104923328701154345482145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14069948885800769563654763 21104923328701154345482145)
          ·
            refine ⟨15828692496525865759111609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21104923328701154345482145 15828692496525865759111609)
            ·
              refine ⟨11871519372394399319333707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15828692496525865759111609 11871519372394399319333707)
              ·
                refine ⟨17807279058591598979000561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11871519372394399319333707 17807279058591598979000561)
                ·
                  refine ⟨13355459293943699234250421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17807279058591598979000561 13355459293943699234250421)
                  ·
                    refine ⟨1252074308807221803210977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13355459293943699234250421 1252074308807221803210977)
                    ·
                      rfl

theorem cell23_7315218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7315218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315218 prefixEnd_7315218 := by exact prefixLift 7315218
  have htrace : WordTrace (prefixWord ++ tailWord_7315218) baseStart_7315218 baseEnd_7315218 := by
    simpa [prefixWord, tailWord_7315218, baseEnd_7315218] using wordTrace_append hprefix tailTrace_7315218
  have hstable : (prefixWord ++ tailWord_7315218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315218).length < 2 ^ (prefixWord ++ tailWord_7315218).sum := by decide
  have hdescent : baseEnd_7315218 < baseStart_7315218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315221 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_7315221 : Nat := 118140960795 + 7315221 * 2 ^ 59
def prefixEnd_7315221 : Nat := 4983230072969 + 3 ^ 40 * 7315221 * 2
def baseEnd_7315221 : Nat := 3756224466863628897895417

theorem tailTrace_7315221 : CollatzResearch.WordTrace tailWord_7315221 prefixEnd_7315221 3756224466863628897895417 := by
  unfold tailWord_7315221
  simp only [CollatzResearch.WordTrace]
  refine ⟨266808029031211132126849517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177872019354140754751233011 266808029031211132126849517)
  ·
    refine ⟨100053010886704174547568569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266808029031211132126849517 100053010886704174547568569)
    ·
      refine ⟨75039758165028130910676427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100053010886704174547568569 75039758165028130910676427)
      ·
        refine ⟨112559637247542196366014641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75039758165028130910676427 112559637247542196366014641)
        ·
          refine ⟨84419727935656647274510981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112559637247542196366014641 84419727935656647274510981)
          ·
            refine ⟨15828698987935621363970809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84419727935656647274510981 15828698987935621363970809)
            ·
              refine ⟨11871524240951716022978107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15828698987935621363970809 11871524240951716022978107)
              ·
                refine ⟨17807286361427574034467161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11871524240951716022978107 17807286361427574034467161)
                ·
                  refine ⟨13355464771070680525850371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17807286361427574034467161 13355464771070680525850371)
                  ·
                    refine ⟨20033197156606020788775557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13355464771070680525850371 20033197156606020788775557)
                    ·
                      refine ⟨3756224466863628897895417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20033197156606020788775557 3756224466863628897895417)
                      ·
                        rfl

theorem cell23_7315221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_7315221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315221 prefixEnd_7315221 := by exact prefixLift 7315221
  have htrace : WordTrace (prefixWord ++ tailWord_7315221) baseStart_7315221 baseEnd_7315221 := by
    simpa [prefixWord, tailWord_7315221, baseEnd_7315221] using wordTrace_append hprefix tailTrace_7315221
  have hstable : (prefixWord ++ tailWord_7315221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315221).length < 2 ^ (prefixWord ++ tailWord_7315221).sum := by decide
  have hdescent : baseEnd_7315221 < baseStart_7315221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315224 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_7315224 : Nat := 118140960795 + 7315224 * 2 ^ 59
def prefixEnd_7315224 : Nat := 4983230072969 + 3 ^ 40 * 7315224 * 2
def baseEnd_7315224 : Nat := 3756226007305592386157903

theorem tailTrace_7315224 : CollatzResearch.WordTrace tailWord_7315224 prefixEnd_7315224 3756226007305592386157903 := by
  unfold tailWord_7315224
  simp only [CollatzResearch.WordTrace]
  refine ⟨133404069225100131819604363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177872092300133509092805817 133404069225100131819604363)
  ·
    refine ⟨200106103837650197729406545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133404069225100131819604363 200106103837650197729406545)
    ·
      refine ⟨150079577878237648297054909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200106103837650197729406545 150079577878237648297054909)
      ·
        refine ⟨56279841704339118111395591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150079577878237648297054909 56279841704339118111395591)
        ·
          refine ⟨84419762556508677167093387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56279841704339118111395591 84419762556508677167093387)
          ·
            refine ⟨126629643834763015750640081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84419762556508677167093387 126629643834763015750640081)
            ·
              refine ⟨94972232876072261812980061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126629643834763015750640081 94972232876072261812980061)
              ·
                refine ⟨35614587328527098179867523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94972232876072261812980061 35614587328527098179867523)
                ·
                  refine ⟨53421880992790647269801285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35614587328527098179867523 53421880992790647269801285)
                  ·
                    refine ⟨10016602686148246363087741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53421880992790647269801285 10016602686148246363087741)
                    ·
                      refine ⟨3756226007305592386157903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10016602686148246363087741 3756226007305592386157903)
                      ·
                        rfl

theorem cell23_7315224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_7315224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315224 prefixEnd_7315224 := by exact prefixLift 7315224
  have htrace : WordTrace (prefixWord ++ tailWord_7315224) baseStart_7315224 baseEnd_7315224 := by
    simpa [prefixWord, tailWord_7315224, baseEnd_7315224] using wordTrace_append hprefix tailTrace_7315224
  have hstable : (prefixWord ++ tailWord_7315224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315224).length < 2 ^ (prefixWord ++ tailWord_7315224).sum := by decide
  have hdescent : baseEnd_7315224 < baseStart_7315224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315234 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7315234 : Nat := 118140960795 + 7315234 * 2 ^ 59
def prefixEnd_7315234 : Nat := 4983230072969 + 3 ^ 40 * 7315234 * 2
def baseEnd_7315234 : Nat := 3756231142112137347032857

theorem tailTrace_7315234 : CollatzResearch.WordTrace tailWord_7315234 prefixEnd_7315234 3756231142112137347032857 := by
  unfold tailWord_7315234
  simp only [CollatzResearch.WordTrace]
  refine ⟨66702125795041008836768189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177872335453442690231381837 66702125795041008836768189)
  ·
    refine ⟨25013297173140378313788071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66702125795041008836768189 25013297173140378313788071)
    ·
      refine ⟨37519945759710567470682107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25013297173140378313788071 37519945759710567470682107)
      ·
        refine ⟨56279918639565851206023161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37519945759710567470682107 56279918639565851206023161)
        ·
          refine ⟨42209938979674388404517371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56279918639565851206023161 42209938979674388404517371)
          ·
            refine ⟨63314908469511582606776057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42209938979674388404517371 63314908469511582606776057)
            ·
              refine ⟨47486181352133686955082043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63314908469511582606776057 47486181352133686955082043)
              ·
                refine ⟨71229272028200530432623065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47486181352133686955082043 71229272028200530432623065)
                ·
                  refine ⟨53421954021150397824467299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71229272028200530432623065 53421954021150397824467299)
                  ·
                    refine ⟨80132931031725596736700949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53421954021150397824467299 80132931031725596736700949)
                    ·
                      refine ⟨3756231142112137347032857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80132931031725596736700949 3756231142112137347032857)
                      ·
                        rfl

theorem cell23_7315234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7315234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315234 prefixEnd_7315234 := by exact prefixLift 7315234
  have htrace : WordTrace (prefixWord ++ tailWord_7315234) baseStart_7315234 baseEnd_7315234 := by
    simpa [prefixWord, tailWord_7315234, baseEnd_7315234] using wordTrace_append hprefix tailTrace_7315234
  have hstable : (prefixWord ++ tailWord_7315234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315234).length < 2 ^ (prefixWord ++ tailWord_7315234).sum := by decide
  have hdescent : baseEnd_7315234 < baseStart_7315234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315244 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 6]
def baseStart_7315244 : Nat := 118140960795 + 7315244 * 2 ^ 59
def prefixEnd_7315244 : Nat := 4983230072969 + 3 ^ 40 * 7315244 * 2
def baseEnd_7315244 : Nat := 417359586324298034211979

theorem tailTrace_7315244 : CollatzResearch.WordTrace tailWord_7315244 prefixEnd_7315244 417359586324298034211979 := by
  unfold tailWord_7315244
  simp only [CollatzResearch.WordTrace]
  refine ⟨133404433955063903527468393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177872578606751871369957857 133404433955063903527468393)
  ·
    refine ⟨100053325466297927645601295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133404433955063903527468393 100053325466297927645601295)
    ·
      refine ⟨150079988199446891468401943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100053325466297927645601295 150079988199446891468401943)
      ·
        refine ⟨225119982299170337202602915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150079988199446891468401943 225119982299170337202602915)
        ·
          refine ⟨337679973448755505803904373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225119982299170337202602915 337679973448755505803904373)
          ·
            refine ⟨31657497510820828669116035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 337679973448755505803904373 31657497510820828669116035)
            ·
              refine ⟨47486246266231243003674053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31657497510820828669116035 47486246266231243003674053)
              ·
                refine ⟨8903671174918358063188885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47486246266231243003674053 8903671174918358063188885)
                ·
                  refine ⟨417359586324298034211979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8903671174918358063188885 417359586324298034211979)
                  ·
                    rfl

theorem cell23_7315244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_7315244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315244 prefixEnd_7315244 := by exact prefixLift 7315244
  have htrace : WordTrace (prefixWord ++ tailWord_7315244) baseStart_7315244 baseEnd_7315244 := by
    simpa [prefixWord, tailWord_7315244, baseEnd_7315244] using wordTrace_append hprefix tailTrace_7315244
  have hstable : (prefixWord ++ tailWord_7315244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315244).length < 2 ^ (prefixWord ++ tailWord_7315244).sum := by decide
  have hdescent : baseEnd_7315244 < baseStart_7315244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315247 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_7315247 : Nat := 118140960795 + 7315247 * 2 ^ 59
def prefixEnd_7315247 : Nat := 4983230072969 + 3 ^ 40 * 7315247 * 2
def baseEnd_7315247 : Nat := 3756237817360645796170297

theorem tailTrace_7315247 : CollatzResearch.WordTrace tailWord_7315247 prefixEnd_7315247 3756237817360645796170297 := by
  unfold tailWord_7315247
  simp only [CollatzResearch.WordTrace]
  refine ⟨266808977329116938567295995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177872651552744625711530663 266808977329116938567295995)
  ·
    refine ⟨400213465993675407850943993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266808977329116938567295995 400213465993675407850943993)
    ·
      refine ⟨300160099495256555888207995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400213465993675407850943993 300160099495256555888207995)
      ·
        refine ⟨450240149242884833832311993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300160099495256555888207995 450240149242884833832311993)
        ·
          refine ⟨337680111932163625374233995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450240149242884833832311993 337680111932163625374233995)
          ·
            refine ⟨506520167898245438061350993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337680111932163625374233995 506520167898245438061350993)
            ·
              refine ⟨379890125923684078546013245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506520167898245438061350993 379890125923684078546013245)
              ·
                refine ⟨142458797221381529454754967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379890125923684078546013245 142458797221381529454754967)
                ·
                  refine ⟨213688195832072294182132451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142458797221381529454754967 213688195832072294182132451)
                  ·
                    refine ⟨320532293748108441273198677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213688195832072294182132451 320532293748108441273198677)
                    ·
                      refine ⟨3756237817360645796170297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 320532293748108441273198677 3756237817360645796170297)
                      ·
                        rfl

theorem cell23_7315247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_7315247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315247 prefixEnd_7315247 := by exact prefixLift 7315247
  have htrace : WordTrace (prefixWord ++ tailWord_7315247) baseStart_7315247 baseEnd_7315247 := by
    simpa [prefixWord, tailWord_7315247, baseEnd_7315247] using wordTrace_append hprefix tailTrace_7315247
  have hstable : (prefixWord ++ tailWord_7315247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315247).length < 2 ^ (prefixWord ++ tailWord_7315247).sum := by decide
  have hdescent : baseEnd_7315247 < baseStart_7315247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315261 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 6]
def baseStart_7315261 : Nat := 118140960795 + 7315261 * 2 ^ 59
def prefixEnd_7315261 : Nat := 4983230072969 + 3 ^ 40 * 7315261 * 2
def baseEnd_7315261 : Nat := 417360556232200971266137

theorem tailTrace_7315261 : CollatzResearch.WordTrace tailWord_7315261 prefixEnd_7315261 417360556232200971266137 := by
  unfold tailWord_7315261
  simp only [CollatzResearch.WordTrace]
  refine ⟨266809487951066218958305637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177872991967377479305537091 266809487951066218958305637)
  ·
    refine ⟨50026778990824916054682307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266809487951066218958305637 50026778990824916054682307)
    ·
      refine ⟨75040168486237374082023461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50026778990824916054682307 75040168486237374082023461)
      ·
        refine ⟨14070031591169507640379399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75040168486237374082023461 14070031591169507640379399)
        ·
          refine ⟨21105047386754261460569099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14070031591169507640379399 21105047386754261460569099)
          ·
            refine ⟨31657571080131392190853649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21105047386754261460569099 31657571080131392190853649)
            ·
              refine ⟨23743178310098544143140237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31657571080131392190853649 23743178310098544143140237)
              ·
                refine ⟨8903691866286954053677589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23743178310098544143140237 8903691866286954053677589)
                ·
                  refine ⟨417360556232200971266137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8903691866286954053677589 417360556232200971266137)
                  ·
                    rfl

theorem cell23_7315261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_7315261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315261 prefixEnd_7315261 := by exact prefixLift 7315261
  have htrace : WordTrace (prefixWord ++ tailWord_7315261) baseStart_7315261 baseEnd_7315261 := by
    simpa [prefixWord, tailWord_7315261, baseEnd_7315261] using wordTrace_append hprefix tailTrace_7315261
  have hstable : (prefixWord ++ tailWord_7315261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315261).length < 2 ^ (prefixWord ++ tailWord_7315261).sum := by decide
  have hdescent : baseEnd_7315261 < baseStart_7315261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315271 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_7315271 : Nat := 118140960795 + 7315271 * 2 ^ 59
def prefixEnd_7315271 : Nat := 4983230072969 + 3 ^ 40 * 7315271 * 2
def baseEnd_7315271 : Nat := 3756250140896353702270187

theorem tailTrace_7315271 : CollatzResearch.WordTrace tailWord_7315271 prefixEnd_7315271 3756250140896353702270187 := by
  unfold tailWord_7315271
  simp only [CollatzResearch.WordTrace]
  refine ⟨266809852681029990666169667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177873235120686660444113111 266809852681029990666169667)
  ·
    refine ⟨400214779021544985999254501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266809852681029990666169667 400214779021544985999254501)
    ·
      refine ⟨75040271066539684874860219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400214779021544985999254501 75040271066539684874860219)
      ·
        refine ⟨112560406599809527312290329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75040271066539684874860219 112560406599809527312290329)
        ·
          refine ⟨84420304949857145484217747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112560406599809527312290329 84420304949857145484217747)
          ·
            refine ⟨126630457424785718226326621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84420304949857145484217747 126630457424785718226326621)
            ·
              refine ⟨47486421534294644334872483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126630457424785718226326621 47486421534294644334872483)
              ·
                refine ⟨71229632301441966502308725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47486421534294644334872483 71229632301441966502308725)
                ·
                  refine ⟨6677778028260184359591443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71229632301441966502308725 6677778028260184359591443)
                  ·
                    refine ⟨10016667042390276539387165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6677778028260184359591443 10016667042390276539387165)
                    ·
                      refine ⟨3756250140896353702270187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10016667042390276539387165 3756250140896353702270187)
                      ·
                        rfl

theorem cell23_7315271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_7315271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315271 prefixEnd_7315271 := by exact prefixLift 7315271
  have htrace : WordTrace (prefixWord ++ tailWord_7315271) baseStart_7315271 baseEnd_7315271 := by
    simpa [prefixWord, tailWord_7315271, baseEnd_7315271] using wordTrace_append hprefix tailTrace_7315271
  have hstable : (prefixWord ++ tailWord_7315271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315271).length < 2 ^ (prefixWord ++ tailWord_7315271).sum := by decide
  have hdescent : baseEnd_7315271 < baseStart_7315271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315274 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_7315274 : Nat := 118140960795 + 7315274 * 2 ^ 59
def prefixEnd_7315274 : Nat := 4983230072969 + 3 ^ 40 * 7315274 * 2
def baseEnd_7315274 : Nat := 1252083893779439063510891

theorem tailTrace_7315274 : CollatzResearch.WordTrace tailWord_7315274 prefixEnd_7315274 1252083893779439063510891 := by
  unfold tailWord_7315274
  simp only [CollatzResearch.WordTrace]
  refine ⟨66702490525004780544632219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177873308066679414785685917 66702490525004780544632219)
  ·
    refine ⟨100053735787507170816948329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66702490525004780544632219 100053735787507170816948329)
    ·
      refine ⟨75040301840630378112711247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100053735787507170816948329 75040301840630378112711247)
      ·
        refine ⟨112560452760945567169066871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75040301840630378112711247 112560452760945567169066871)
        ·
          refine ⟨168840679141418350753600307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112560452760945567169066871 168840679141418350753600307)
          ·
            refine ⟨253261018712127526130400461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168840679141418350753600307 253261018712127526130400461)
            ·
              refine ⟨94972882017047822298900173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253261018712127526130400461 94972882017047822298900173)
              ·
                refine ⟨35614830756392933362087565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94972882017047822298900173 35614830756392933362087565)
                ·
                  refine ⟨13355561533647350010782837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35614830756392933362087565 13355561533647350010782837)
                  ·
                    refine ⟨1252083893779439063510891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13355561533647350010782837 1252083893779439063510891)
                    ·
                      rfl

theorem cell23_7315274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_7315274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315274 prefixEnd_7315274 := by exact prefixLift 7315274
  have htrace : WordTrace (prefixWord ++ tailWord_7315274) baseStart_7315274 baseEnd_7315274 := by
    simpa [prefixWord, tailWord_7315274, baseEnd_7315274] using wordTrace_append hprefix tailTrace_7315274
  have hstable : (prefixWord ++ tailWord_7315274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315274).length < 2 ^ (prefixWord ++ tailWord_7315274).sum := by decide
  have hdescent : baseEnd_7315274 < baseStart_7315274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315328 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 3, 2, 2]
def baseStart_7315328 : Nat := 118140960795 + 7315328 * 2 ^ 59
def prefixEnd_7315328 : Nat := 4983230072969 + 3 ^ 40 * 7315328 * 2
def baseEnd_7315328 : Nat := 3756279409293659979257425

theorem tailTrace_7315328 : CollatzResearch.WordTrace tailWord_7315328 prefixEnd_7315328 3756279409293659979257425 := by
  unfold tailWord_7315328
  simp only [CollatzResearch.WordTrace]
  refine ⟨133405965820911744700497319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177874621094548992933996425 133405965820911744700497319)
  ·
    refine ⟨200108948731367617050745979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133405965820911744700497319 200108948731367617050745979)
    ·
      refine ⟨300163423097051425576118969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200108948731367617050745979 300163423097051425576118969)
      ·
        refine ⟨225122567322788569182089227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300163423097051425576118969 225122567322788569182089227)
        ·
          refine ⟨337683850984182853773133841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225122567322788569182089227 337683850984182853773133841)
          ·
            refine ⟨253262888238137140329850381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337683850984182853773133841 253262888238137140329850381)
            ·
              refine ⟨94973583089301427623693893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253262888238137140329850381 94973583089301427623693893)
              ·
                refine ⟨17807546829244017679442605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94973583089301427623693893 17807546829244017679442605)
                ·
                  refine ⟨6677830060966506629790977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17807546829244017679442605 6677830060966506629790977)
                  ·
                    refine ⟨5008372545724879972343233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6677830060966506629790977 5008372545724879972343233)
                    ·
                      refine ⟨3756279409293659979257425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008372545724879972343233 3756279409293659979257425)
                      ·
                        rfl

theorem cell23_7315328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_7315328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315328 prefixEnd_7315328 := by exact prefixLift 7315328
  have htrace : WordTrace (prefixWord ++ tailWord_7315328) baseStart_7315328 baseEnd_7315328 := by
    simpa [prefixWord, tailWord_7315328, baseEnd_7315328] using wordTrace_append hprefix tailTrace_7315328
  have hstable : (prefixWord ++ tailWord_7315328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315328).length < 2 ^ (prefixWord ++ tailWord_7315328).sum := by decide
  have hdescent : baseEnd_7315328 < baseStart_7315328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315348 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7315348 : Nat := 118140960795 + 7315348 * 2 ^ 59
def prefixEnd_7315348 : Nat := 4983230072969 + 3 ^ 40 * 7315348 * 2
def baseEnd_7315348 : Nat := 3756289678906749901007333

theorem tailTrace_7315348 : CollatzResearch.WordTrace tailWord_7315348 prefixEnd_7315348 3756289678906749901007333 := by
  unfold tailWord_7315348
  simp only [CollatzResearch.WordTrace]
  refine ⟨133406330550875516408361349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177875107401167355211148465 133406330550875516408361349)
  ·
    refine ⟨25013686978289159326567753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133406330550875516408361349 25013686978289159326567753)
    ·
      refine ⟨18760265233716869494925815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25013686978289159326567753 18760265233716869494925815)
      ·
        refine ⟨28140397850575304242388723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18760265233716869494925815 28140397850575304242388723)
        ·
          refine ⟨42210596775862956363583085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28140397850575304242388723 42210596775862956363583085)
          ·
            refine ⟨15828973790948608636343657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42210596775862956363583085 15828973790948608636343657)
            ·
              refine ⟨11871730343211456477257743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15828973790948608636343657 11871730343211456477257743)
              ·
                refine ⟨17807595514817184715886615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11871730343211456477257743 17807595514817184715886615)
                ·
                  refine ⟨26711393272225777073829923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17807595514817184715886615 26711393272225777073829923)
                  ·
                    refine ⟨40067089908338665610744885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26711393272225777073829923 40067089908338665610744885)
                    ·
                      refine ⟨3756289678906749901007333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40067089908338665610744885 3756289678906749901007333)
                      ·
                        rfl

theorem cell23_7315348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7315348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315348 prefixEnd_7315348 := by exact prefixLift 7315348
  have htrace : WordTrace (prefixWord ++ tailWord_7315348) baseStart_7315348 baseEnd_7315348 := by
    simpa [prefixWord, tailWord_7315348, baseEnd_7315348] using wordTrace_append hprefix tailTrace_7315348
  have hstable : (prefixWord ++ tailWord_7315348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315348).length < 2 ^ (prefixWord ++ tailWord_7315348).sum := by decide
  have hdescent : baseEnd_7315348 < baseStart_7315348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315424 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 11]
def baseStart_7315424 : Nat := 118140960795 + 7315424 * 2 ^ 59
def prefixEnd_7315424 : Nat := 4983230072969 + 3 ^ 40 * 7315424 * 2
def baseEnd_7315424 : Nat := 417369855937387955961887

theorem tailTrace_7315424 : CollatzResearch.WordTrace tailWord_7315424 prefixEnd_7315424 417369855937387955961887 := by
  unfold tailWord_7315424
  simp only [CollatzResearch.WordTrace]
  refine ⟨133407716524737848898244663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177876955366317131864326217 133407716524737848898244663)
  ·
    refine ⟨200111574787106773347366995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133407716524737848898244663 200111574787106773347366995)
    ·
      refine ⟨300167362180660160021050493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200111574787106773347366995 300167362180660160021050493)
      ·
        refine ⟨112562760817747560007893935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300167362180660160021050493 112562760817747560007893935)
        ·
          refine ⟨168844141226621340011840903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112562760817747560007893935 168844141226621340011840903)
          ·
            refine ⟨253266211839932010017761355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168844141226621340011840903 253266211839932010017761355)
            ·
              refine ⟨379899317759898015026642033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253266211839932010017761355 379899317759898015026642033)
              ·
                refine ⟨284924488319923511269981525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379899317759898015026642033 284924488319923511269981525)
                ·
                  refine ⟨417369855937387955961887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 284924488319923511269981525 417369855937387955961887)
                  ·
                    rfl

theorem cell23_7315424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_7315424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315424 prefixEnd_7315424 := by exact prefixLift 7315424
  have htrace : WordTrace (prefixWord ++ tailWord_7315424) baseStart_7315424 baseEnd_7315424 := by
    simpa [prefixWord, tailWord_7315424, baseEnd_7315424] using wordTrace_append hprefix tailTrace_7315424
  have hstable : (prefixWord ++ tailWord_7315424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315424).length < 2 ^ (prefixWord ++ tailWord_7315424).sum := by decide
  have hdescent : baseEnd_7315424 < baseStart_7315424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315491 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4]
def baseStart_7315491 : Nat := 118140960795 + 7315491 * 2 ^ 59
def prefixEnd_7315491 : Nat := 4983230072969 + 3 ^ 40 * 7315491 * 2
def baseEnd_7315491 : Nat := 3756363106640342841519175

theorem tailTrace_7315491 : CollatzResearch.WordTrace tailWord_7315491 prefixEnd_7315491 3756363106640342841519175 := by
  unfold tailWord_7315491
  simp only [CollatzResearch.WordTrace]
  refine ⟨266817876740232968239178327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177878584493488645492785551 266817876740232968239178327)
  ·
    refine ⟨400226815110349452358767491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266817876740232968239178327 400226815110349452358767491)
    ·
      refine ⟨600340222665524178538151237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400226815110349452358767491 600340222665524178538151237)
      ·
        refine ⟨112563791749785783475903357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 600340222665524178538151237 112563791749785783475903357)
        ·
          refine ⟨42211421906169668803463759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112563791749785783475903357 42211421906169668803463759)
          ·
            refine ⟨63317132859254503205195639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42211421906169668803463759 63317132859254503205195639)
            ·
              refine ⟨94975699288881754807793459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63317132859254503205195639 94975699288881754807793459)
              ·
                refine ⟨142463548933322632211690189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94975699288881754807793459 142463548933322632211690189)
                ·
                  refine ⟨53423830849995987079383821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142463548933322632211690189 53423830849995987079383821)
                  ·
                    refine ⟨20033936568748495154768933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53423830849995987079383821 20033936568748495154768933)
                    ·
                      refine ⟨3756363106640342841519175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20033936568748495154768933 3756363106640342841519175)
                      ·
                        rfl

theorem cell23_7315491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_7315491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315491 prefixEnd_7315491 := by exact prefixLift 7315491
  have htrace : WordTrace (prefixWord ++ tailWord_7315491) baseStart_7315491 baseEnd_7315491 := by
    simpa [prefixWord, tailWord_7315491, baseEnd_7315491] using wordTrace_append hprefix tailTrace_7315491
  have hstable : (prefixWord ++ tailWord_7315491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315491).length < 2 ^ (prefixWord ++ tailWord_7315491).sum := by decide
  have hdescent : baseEnd_7315491 < baseStart_7315491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315562 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_7315562 : Nat := 118140960795 + 7315562 * 2 ^ 59
def prefixEnd_7315562 : Nat := 4983230072969 + 3 ^ 40 * 7315562 * 2
def baseEnd_7315562 : Nat := 3756399563766812063731349

theorem tailTrace_7315562 : CollatzResearch.WordTrace tailWord_7315562 prefixEnd_7315562 3756399563766812063731349 := by
  unfold tailWord_7315562
  simp only [CollatzResearch.WordTrace]
  refine ⟨66705116580743936841253235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177880310881983831576675293 66705116580743936841253235)
  ·
    refine ⟨100057674871115905261879853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66705116580743936841253235 100057674871115905261879853)
    ·
      refine ⟨37521628076668464473204945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100057674871115905261879853 37521628076668464473204945)
      ·
        refine ⟨28141221057501348354903709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37521628076668464473204945 28141221057501348354903709)
        ·
          refine ⟨10552957896563005633088891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28141221057501348354903709 10552957896563005633088891)
          ·
            refine ⟨15829436844844508449633337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10552957896563005633088891 15829436844844508449633337)
            ·
              refine ⟨11872077633633381337225003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15829436844844508449633337 11872077633633381337225003)
              ·
                refine ⟨17808116450450072005837505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872077633633381337225003 17808116450450072005837505)
                ·
                  refine ⟨13356087337837554004378129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17808116450450072005837505 13356087337837554004378129)
                  ·
                    refine ⟨10017065503378165503283597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13356087337837554004378129 10017065503378165503283597)
                    ·
                      refine ⟨3756399563766812063731349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10017065503378165503283597 3756399563766812063731349)
                      ·
                        rfl

theorem cell23_7315562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_7315562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315562 prefixEnd_7315562 := by exact prefixLift 7315562
  have htrace : WordTrace (prefixWord ++ tailWord_7315562) baseStart_7315562 baseEnd_7315562 := by
    simpa [prefixWord, tailWord_7315562, baseEnd_7315562] using wordTrace_append hprefix tailTrace_7315562
  have hstable : (prefixWord ++ tailWord_7315562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315562).length < 2 ^ (prefixWord ++ tailWord_7315562).sum := by decide
  have hdescent : baseEnd_7315562 < baseStart_7315562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315615 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7315615 : Nat := 118140960795 + 7315615 * 2 ^ 59
def prefixEnd_7315615 : Nat := 4983230072969 + 3 ^ 40 * 7315615 * 2
def baseEnd_7315615 : Nat := 3756426778241500356368605

theorem tailTrace_7315615 : CollatzResearch.WordTrace tailWord_7315615 prefixEnd_7315615 3756426778241500356368605 := by
  unfold tailWord_7315615
  simp only [CollatzResearch.WordTrace]
  refine ⟨266822399391783737416692299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177881599594522491611128199 266822399391783737416692299)
  ·
    refine ⟨400233599087675606125038449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266822399391783737416692299 400233599087675606125038449)
    ·
      refine ⟨300175199315756704593778837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400233599087675606125038449 300175199315756704593778837)
      ·
        refine ⟨14070712467926095527833383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 300175199315756704593778837 14070712467926095527833383)
        ·
          refine ⟨21106068701889143291750075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14070712467926095527833383 21106068701889143291750075)
          ·
            refine ⟨31659103052833714937625113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21106068701889143291750075 31659103052833714937625113)
            ·
              refine ⟨23744327289625286203218835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31659103052833714937625113 23744327289625286203218835)
              ·
                refine ⟨35616490934437929304828253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23744327289625286203218835 35616490934437929304828253)
                ·
                  refine ⟨13356184100414223489310595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35616490934437929304828253 13356184100414223489310595)
                  ·
                    refine ⟨20034276150621335233965893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13356184100414223489310595 20034276150621335233965893)
                    ·
                      refine ⟨3756426778241500356368605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20034276150621335233965893 3756426778241500356368605)
                      ·
                        rfl

theorem cell23_7315615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7315615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315615 prefixEnd_7315615 := by exact prefixLift 7315615
  have htrace : WordTrace (prefixWord ++ tailWord_7315615) baseStart_7315615 baseEnd_7315615 := by
    simpa [prefixWord, tailWord_7315615, baseEnd_7315615] using wordTrace_append hprefix tailTrace_7315615
  have hstable : (prefixWord ++ tailWord_7315615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315615).length < 2 ^ (prefixWord ++ tailWord_7315615).sum := by decide
  have hdescent : baseEnd_7315615 < baseStart_7315615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315629 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_7315629 : Nat := 118140960795 + 7315629 * 2 ^ 59
def prefixEnd_7315629 : Nat := 4983230072969 + 3 ^ 40 * 7315629 * 2
def baseEnd_7315629 : Nat := 1252144655656887767197847

theorem tailTrace_7315629 : CollatzResearch.WordTrace tailWord_7315629 prefixEnd_7315629 1252144655656887767197847 := by
  unfold tailWord_7315629
  simp only [CollatzResearch.WordTrace]
  refine ⟨266822910013733017807701941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177881940009155345205134627 266822910013733017807701941)
  ·
    refine ⟨25014647813787470419472057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266822910013733017807701941 25014647813787470419472057)
    ·
      refine ⟨18760985860340602814604043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25014647813787470419472057 18760985860340602814604043)
      ·
        refine ⟨28141478790510904221906065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18760985860340602814604043 28141478790510904221906065)
        ·
          refine ⟨21106109092883178166429549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28141478790510904221906065 21106109092883178166429549)
          ·
            refine ⟨7914790909831191812411081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21106109092883178166429549 7914790909831191812411081)
            ·
              refine ⟨5936093182373393859308311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7914790909831191812411081 5936093182373393859308311)
              ·
                refine ⟨8904139773560090788962467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936093182373393859308311 8904139773560090788962467)
                ·
                  refine ⟨13356209660340136183443701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904139773560090788962467 13356209660340136183443701)
                  ·
                    refine ⟨1252144655656887767197847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13356209660340136183443701 1252144655656887767197847)
                    ·
                      rfl

theorem cell23_7315629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_7315629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315629 prefixEnd_7315629 := by exact prefixLift 7315629
  have htrace : WordTrace (prefixWord ++ tailWord_7315629) baseStart_7315629 baseEnd_7315629 := by
    simpa [prefixWord, tailWord_7315629, baseEnd_7315629] using wordTrace_append hprefix tailTrace_7315629
  have hstable : (prefixWord ++ tailWord_7315629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315629).length < 2 ^ (prefixWord ++ tailWord_7315629).sum := by decide
  have hdescent : baseEnd_7315629 < baseStart_7315629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315662 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_7315662 : Nat := 118140960795 + 7315662 * 2 ^ 59
def prefixEnd_7315662 : Nat := 4983230072969 + 3 ^ 40 * 7315662 * 2
def baseEnd_7315662 : Nat := 3756450911832261672480889

theorem tailTrace_7315662 : CollatzResearch.WordTrace tailWord_7315662 prefixEnd_7315662 3756450911832261672480889 := by
  unfold tailWord_7315662
  simp only [CollatzResearch.WordTrace]
  refine ⟨33353014202826683055456655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177882742415075642962435493 33353014202826683055456655)
  ·
    refine ⟨50029521304240024583184983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33353014202826683055456655 50029521304240024583184983)
    ·
      refine ⟨75044281956360036874777475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50029521304240024583184983 75044281956360036874777475)
      ·
        refine ⟨112566422934540055312166213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75044281956360036874777475 112566422934540055312166213)
        ·
          refine ⟨21106204300226260371031165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112566422934540055312166213 21106204300226260371031165)
          ·
            refine ⟨7914826612584847639136687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21106204300226260371031165 7914826612584847639136687)
            ·
              refine ⟨11872239918877271458705031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7914826612584847639136687 11872239918877271458705031)
              ·
                refine ⟨17808359878315907188057547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872239918877271458705031 17808359878315907188057547)
                ·
                  refine ⟨26712539817473860782086321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17808359878315907188057547 26712539817473860782086321)
                  ·
                    refine ⟨20034404863105395586564741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26712539817473860782086321 20034404863105395586564741)
                    ·
                      refine ⟨3756450911832261672480889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20034404863105395586564741 3756450911832261672480889)
                      ·
                        rfl

theorem cell23_7315662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_7315662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315662 prefixEnd_7315662 := by exact prefixLift 7315662
  have htrace : WordTrace (prefixWord ++ tailWord_7315662) baseStart_7315662 baseEnd_7315662 := by
    simpa [prefixWord, tailWord_7315662, baseEnd_7315662] using wordTrace_append hprefix tailTrace_7315662
  have hstable : (prefixWord ++ tailWord_7315662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315662).length < 2 ^ (prefixWord ++ tailWord_7315662).sum := by decide
  have hdescent : baseEnd_7315662 < baseStart_7315662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315665 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_7315665 : Nat := 118140960795 + 7315665 * 2 ^ 59
def prefixEnd_7315665 : Nat := 4983230072969 + 3 ^ 40 * 7315665 * 2
def baseEnd_7315665 : Nat := 3756452452274225160743375

theorem tailTrace_7315665 : CollatzResearch.WordTrace tailWord_7315665 prefixEnd_7315665 3756452452274225160743375 := by
  unfold tailWord_7315665
  simp only [CollatzResearch.WordTrace]
  refine ⟨266824223041602595956012449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177882815361068397304008299 266824223041602595956012449)
  ·
    refine ⟨200118167281201946967009337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266824223041602595956012449 200118167281201946967009337)
    ·
      refine ⟨150088625460901460225257003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200118167281201946967009337 150088625460901460225257003)
      ·
        refine ⟨225132938191352190337885505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150088625460901460225257003 225132938191352190337885505)
        ·
          refine ⟨168849703643514142753414129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225132938191352190337885505 168849703643514142753414129)
          ·
            refine ⟨126637277732635607065060597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168849703643514142753414129 126637277732635607065060597)
            ·
              refine ⟨11872244787434588162349431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126637277732635607065060597 11872244787434588162349431)
              ·
                refine ⟨17808367181151882243524147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872244787434588162349431 17808367181151882243524147)
                ·
                  refine ⟨26712550771727823365286221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17808367181151882243524147 26712550771727823365286221)
                  ·
                    refine ⟨10017206539397933761982333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26712550771727823365286221 10017206539397933761982333)
                    ·
                      refine ⟨3756452452274225160743375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10017206539397933761982333 3756452452274225160743375)
                      ·
                        rfl

theorem cell23_7315665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_7315665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315665 prefixEnd_7315665 := by exact prefixLift 7315665
  have htrace : WordTrace (prefixWord ++ tailWord_7315665) baseStart_7315665 baseEnd_7315665 := by
    simpa [prefixWord, tailWord_7315665, baseEnd_7315665] using wordTrace_append hprefix tailTrace_7315665
  have hstable : (prefixWord ++ tailWord_7315665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315665).length < 2 ^ (prefixWord ++ tailWord_7315665).sum := by decide
  have hdescent : baseEnd_7315665 < baseStart_7315665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315669 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7315669 : Nat := 118140960795 + 7315669 * 2 ^ 59
def prefixEnd_7315669 : Nat := 4983230072969 + 3 ^ 40 * 7315669 * 2
def baseEnd_7315669 : Nat := 3756454506196843145093357

theorem tailTrace_7315669 : CollatzResearch.WordTrace tailWord_7315669 prefixEnd_7315669 3756454506196843145093357 := by
  unfold tailWord_7315669
  simp only [CollatzResearch.WordTrace]
  refine ⟨266824368933588104639158061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177882912622392069759438707 266824368933588104639158061)
  ·
    refine ⟨100059138350095539239684273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266824368933588104639158061 100059138350095539239684273)
    ·
      refine ⟨75044353762571654429763205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100059138350095539239684273 75044353762571654429763205)
      ·
        refine ⟨14070816330482185205580601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75044353762571654429763205 14070816330482185205580601)
        ·
          refine ⟨10553112247861638904185451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14070816330482185205580601 10553112247861638904185451)
          ·
            refine ⟨15829668371792458356278177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10553112247861638904185451 15829668371792458356278177)
            ·
              refine ⟨11872251278844343767208633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15829668371792458356278177 11872251278844343767208633)
              ·
                refine ⟨8904188459133257825406475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11872251278844343767208633 8904188459133257825406475)
                ·
                  refine ⟨13356282688699886738109713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904188459133257825406475 13356282688699886738109713)
                  ·
                    refine ⟨10017212016524915053582285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13356282688699886738109713 10017212016524915053582285)
                    ·
                      refine ⟨3756454506196843145093357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10017212016524915053582285 3756454506196843145093357)
                      ·
                        rfl

theorem cell23_7315669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7315669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315669 prefixEnd_7315669 := by exact prefixLift 7315669
  have htrace : WordTrace (prefixWord ++ tailWord_7315669) baseStart_7315669 baseEnd_7315669 := by
    simpa [prefixWord, tailWord_7315669, baseEnd_7315669] using wordTrace_append hprefix tailTrace_7315669
  have hstable : (prefixWord ++ tailWord_7315669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315669).length < 2 ^ (prefixWord ++ tailWord_7315669).sum := by decide
  have hdescent : baseEnd_7315669 < baseStart_7315669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315692 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 1, 3, 2]
def baseStart_7315692 : Nat := 118140960795 + 7315692 * 2 ^ 59
def prefixEnd_7315692 : Nat := 4983230072969 + 3 ^ 40 * 7315692 * 2
def baseEnd_7315692 : Nat := 3756466316251896555105751

theorem tailTrace_7315692 : CollatzResearch.WordTrace tailWord_7315692 prefixEnd_7315692 3756466316251896555105751 := by
  unfold tailWord_7315692
  simp only [CollatzResearch.WordTrace]
  refine ⟨133412603906252389783622665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177883471875003186378163553 133412603906252389783622665)
  ·
    refine ⟨100059452929689292337716999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133412603906252389783622665 100059452929689292337716999)
    ·
      refine ⟨150089179394533938506575499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100059452929689292337716999 150089179394533938506575499)
      ·
        refine ⟨225133769091800907759863249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150089179394533938506575499 225133769091800907759863249)
        ·
          refine ⟨168850326818850680819897437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225133769091800907759863249 168850326818850680819897437)
          ·
            refine ⟨63318872557069005307461539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168850326818850680819897437 63318872557069005307461539)
            ·
              refine ⟨94978308835603507961192309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63318872557069005307461539 94978308835603507961192309)
              ·
                refine ⟨8904216453337828871361779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94978308835603507961192309 8904216453337828871361779)
                ·
                  refine ⟨13356324680006743307042669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904216453337828871361779 13356324680006743307042669)
                  ·
                    refine ⟨5008621755002528740141001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13356324680006743307042669 5008621755002528740141001)
                    ·
                      refine ⟨3756466316251896555105751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008621755002528740141001 3756466316251896555105751)
                      ·
                        rfl

theorem cell23_7315692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_7315692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315692 prefixEnd_7315692 := by exact prefixLift 7315692
  have htrace : WordTrace (prefixWord ++ tailWord_7315692) baseStart_7315692 baseEnd_7315692 := by
    simpa [prefixWord, tailWord_7315692, baseEnd_7315692] using wordTrace_append hprefix tailTrace_7315692
  have hstable : (prefixWord ++ tailWord_7315692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315692).length < 2 ^ (prefixWord ++ tailWord_7315692).sum := by decide
  have hdescent : baseEnd_7315692 < baseStart_7315692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315705 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 5, 4, 2]
def baseStart_7315705 : Nat := 118140960795 + 7315705 * 2 ^ 59
def prefixEnd_7315705 : Nat := 4983230072969 + 3 ^ 40 * 7315705 * 2
def baseEnd_7315705 : Nat := 3756472991500405004243191

theorem tailTrace_7315705 : CollatzResearch.WordTrace tailWord_7315705 prefixEnd_7315705 3756472991500405004243191 := by
  unfold tailWord_7315705
  simp only [CollatzResearch.WordTrace]
  refine ⟨266825681961457682787468569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177883787974305121858312379 266825681961457682787468569)
  ·
    refine ⟨200119261471093262090601427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266825681961457682787468569 200119261471093262090601427)
    ·
      refine ⟨300178892206639893135902141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200119261471093262090601427 300178892206639893135902141)
      ·
        refine ⟨112567084577489959925963303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300178892206639893135902141 112567084577489959925963303)
        ·
          refine ⟨168850626866234939888944955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112567084577489959925963303 168850626866234939888944955)
          ·
            refine ⟨253275940299352409833417433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168850626866234939888944955 253275940299352409833417433)
            ·
              refine ⟨189956955224514307375063075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253275940299352409833417433 189956955224514307375063075)
              ·
                refine ⟨284935432836771461062594613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189956955224514307375063075 284935432836771461062594613)
                ·
                  refine ⟨26712696828447324474618245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284935432836771461062594613 26712696828447324474618245)
                  ·
                    refine ⟨5008630655333873338990921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26712696828447324474618245 5008630655333873338990921)
                    ·
                      refine ⟨3756472991500405004243191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008630655333873338990921 3756472991500405004243191)
                      ·
                        rfl

theorem cell23_7315705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_7315705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315705 prefixEnd_7315705 := by exact prefixLift 7315705
  have htrace : WordTrace (prefixWord ++ tailWord_7315705) baseStart_7315705 baseEnd_7315705 := by
    simpa [prefixWord, tailWord_7315705, baseEnd_7315705] using wordTrace_append hprefix tailTrace_7315705
  have hstable : (prefixWord ++ tailWord_7315705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315705).length < 2 ^ (prefixWord ++ tailWord_7315705).sum := by decide
  have hdescent : baseEnd_7315705 < baseStart_7315705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315792 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 2, 5]
def baseStart_7315792 : Nat := 118140960795 + 7315792 * 2 ^ 59
def prefixEnd_7315792 : Nat := 4983230072969 + 3 ^ 40 * 7315792 * 2
def baseEnd_7315792 : Nat := 1252172554772448721285097

theorem tailTrace_7315792 : CollatzResearch.WordTrace tailWord_7315792 prefixEnd_7315792 1252172554772448721285097 := by
  unfold tailWord_7315792
  simp only [CollatzResearch.WordTrace]
  refine ⟨133414427556071248322942815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177885903408094997763923753 133414427556071248322942815)
  ·
    refine ⟨200121641334106872484414223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133414427556071248322942815 200121641334106872484414223)
    ·
      refine ⟨300182462001160308726621335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200121641334106872484414223 300182462001160308726621335)
      ·
        refine ⟨450273693001740463089932003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300182462001160308726621335 450273693001740463089932003)
        ·
          refine ⟨675410539502610694634898005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450273693001740463089932003 675410539502610694634898005)
          ·
            refine ⟨7914967259796219077752711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 675410539502610694634898005 7914967259796219077752711)
            ·
              refine ⟨11872450889694328616629067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7914967259796219077752711 11872450889694328616629067)
              ·
                refine ⟨17808676334541492924943601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872450889694328616629067 17808676334541492924943601)
                ·
                  refine ⟨13356507250906119693707701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17808676334541492924943601 13356507250906119693707701)
                  ·
                    refine ⟨1252172554772448721285097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13356507250906119693707701 1252172554772448721285097)
                    ·
                      rfl

theorem cell23_7315792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_7315792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315792 prefixEnd_7315792 := by exact prefixLift 7315792
  have htrace : WordTrace (prefixWord ++ tailWord_7315792) baseStart_7315792 baseEnd_7315792 := by
    simpa [prefixWord, tailWord_7315792, baseEnd_7315792] using wordTrace_append hprefix tailTrace_7315792
  have hstable : (prefixWord ++ tailWord_7315792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315792).length < 2 ^ (prefixWord ++ tailWord_7315792).sum := by decide
  have hdescent : baseEnd_7315792 < baseStart_7315792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315795 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 4]
def baseStart_7315795 : Nat := 118140960795 + 7315795 * 2 ^ 59
def prefixEnd_7315795 : Nat := 4983230072969 + 3 ^ 40 * 7315795 * 2
def baseEnd_7315795 : Nat := 3756519204759309652117777

theorem tailTrace_7315795 : CollatzResearch.WordTrace tailWord_7315795 prefixEnd_7315795 3756519204759309652117777 := by
  unfold tailWord_7315795
  simp only [CollatzResearch.WordTrace]
  refine ⟨266828964531131628158244839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177885976354087752105496559 266828964531131628158244839)
  ·
    refine ⟨400243446796697442237367259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266828964531131628158244839 400243446796697442237367259)
    ·
      refine ⟨600365170195046163356050889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400243446796697442237367259 600365170195046163356050889)
      ·
        refine ⟨450273877646284622517038167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600365170195046163356050889 450273877646284622517038167)
        ·
          refine ⟨675410816469426933775557251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450273877646284622517038167 675410816469426933775557251)
          ·
            refine ⟨1013116224704140400663335877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675410816469426933775557251 1013116224704140400663335877)
            ·
              refine ⟨189959292132026325124375477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1013116224704140400663335877 189959292132026325124375477)
              ·
                refine ⟨17808683637377467980410201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189959292132026325124375477 17808683637377467980410201)
                ·
                  refine ⟨13356512728033100985307651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17808683637377467980410201 13356512728033100985307651)
                  ·
                    refine ⟨20034769092049651477961477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13356512728033100985307651 20034769092049651477961477)
                    ·
                      refine ⟨3756519204759309652117777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20034769092049651477961477 3756519204759309652117777)
                      ·
                        rfl

theorem cell23_7315795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_7315795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315795 prefixEnd_7315795 := by exact prefixLift 7315795
  have htrace : WordTrace (prefixWord ++ tailWord_7315795) baseStart_7315795 baseEnd_7315795 := by
    simpa [prefixWord, tailWord_7315795, baseEnd_7315795] using wordTrace_append hprefix tailTrace_7315795
  have hstable : (prefixWord ++ tailWord_7315795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315795).length < 2 ^ (prefixWord ++ tailWord_7315795).sum := by decide
  have hdescent : baseEnd_7315795 < baseStart_7315795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315812 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_7315812 : Nat := 118140960795 + 7315812 * 2 ^ 59
def prefixEnd_7315812 : Nat := 4983230072969 + 3 ^ 40 * 7315812 * 2
def baseEnd_7315812 : Nat := 3756527933930436085605199

theorem tailTrace_7315812 : CollatzResearch.WordTrace tailWord_7315812 prefixEnd_7315812 3756527933930436085605199 := by
  unfold tailWord_7315812
  simp only [CollatzResearch.WordTrace]
  refine ⟨133414792286035020030806845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177886389714713360041075793 133414792286035020030806845)
  ·
    refine ⟨50030547107263132511552567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133414792286035020030806845 50030547107263132511552567)
    ·
      refine ⟨75045820660894698767328851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50030547107263132511552567 75045820660894698767328851)
      ·
        refine ⟨112568730991342048150993277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75045820660894698767328851 112568730991342048150993277)
        ·
          refine ⟨42213274121753268056622479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112568730991342048150993277 42213274121753268056622479)
          ·
            refine ⟨63319911182629902084933719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42213274121753268056622479 63319911182629902084933719)
            ·
              refine ⟨94979866773944853127400579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63319911182629902084933719 94979866773944853127400579)
              ·
                refine ⟨142469800160917279691100869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94979866773944853127400579 142469800160917279691100869)
                ·
                  refine ⟨26713087530171989942081413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142469800160917279691100869 26713087530171989942081413)
                  ·
                    refine ⟨5008703911907248114140265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26713087530171989942081413 5008703911907248114140265)
                    ·
                      refine ⟨3756527933930436085605199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008703911907248114140265 3756527933930436085605199)
                      ·
                        rfl

theorem cell23_7315812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_7315812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315812 prefixEnd_7315812 := by exact prefixLift 7315812
  have htrace : WordTrace (prefixWord ++ tailWord_7315812) baseStart_7315812 baseEnd_7315812 := by
    simpa [prefixWord, tailWord_7315812, baseEnd_7315812] using wordTrace_append hprefix tailTrace_7315812
  have hstable : (prefixWord ++ tailWord_7315812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315812).length < 2 ^ (prefixWord ++ tailWord_7315812).sum := by decide
  have hdescent : baseEnd_7315812 < baseStart_7315812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315829 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7315829 : Nat := 118140960795 + 7315829 * 2 ^ 59
def prefixEnd_7315829 : Nat := 4983230072969 + 3 ^ 40 * 7315829 * 2
def baseEnd_7315829 : Nat := 3756536663101562519092621

theorem tailTrace_7315829 : CollatzResearch.WordTrace tailWord_7315829 prefixEnd_7315829 3756536663101562519092621 := by
  unfold tailWord_7315829
  simp only [CollatzResearch.WordTrace]
  refine ⟨266830204613008451964982541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177886803075338967976655027 266830204613008451964982541)
  ·
    refine ⟨100061326729878169486868453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266830204613008451964982541 100061326729878169486868453)
    ·
      refine ⟨18761498761852156778787835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100061326729878169486868453 18761498761852156778787835)
      ·
        refine ⟨28142248142778235168181753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18761498761852156778787835 28142248142778235168181753)
        ·
          refine ⟨21106686107083676376136315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28142248142778235168181753 21106686107083676376136315)
          ·
            refine ⟨31660029160625514564204473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21106686107083676376136315 31660029160625514564204473)
            ·
              refine ⟨23745021870469135923153355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31660029160625514564204473 23745021870469135923153355)
              ·
                refine ⟨35617532805703703884730033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23745021870469135923153355 35617532805703703884730033)
                ·
                  refine ⟨26713149604277777913547525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35617532805703703884730033 26713149604277777913547525)
                  ·
                    refine ⟨5008715550802083358790161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26713149604277777913547525 5008715550802083358790161)
                    ·
                      refine ⟨3756536663101562519092621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008715550802083358790161 3756536663101562519092621)
                      ·
                        rfl

theorem cell23_7315829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7315829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315829 prefixEnd_7315829 := by exact prefixLift 7315829
  have htrace : WordTrace (prefixWord ++ tailWord_7315829) baseStart_7315829 baseEnd_7315829 := by
    simpa [prefixWord, tailWord_7315829, baseEnd_7315829] using wordTrace_append hprefix tailTrace_7315829
  have hstable : (prefixWord ++ tailWord_7315829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315829).length < 2 ^ (prefixWord ++ tailWord_7315829).sum := by decide
  have hdescent : baseEnd_7315829 < baseStart_7315829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315845 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_7315845 : Nat := 118140960795 + 7315845 * 2 ^ 59
def prefixEnd_7315845 : Nat := 4983230072969 + 3 ^ 40 * 7315845 * 2
def baseEnd_7315845 : Nat := 3756544878792034456492547

theorem tailTrace_7315845 : CollatzResearch.WordTrace tailWord_7315845 prefixEnd_7315845 3756544878792034456492547 := by
  unfold tailWord_7315845
  simp only [CollatzResearch.WordTrace]
  refine ⟨266830788180950486697564989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177887192120633657798376659 266830788180950486697564989)
  ·
    refine ⟨100061545567856432511586871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266830788180950486697564989 100061545567856432511586871)
    ·
      refine ⟨150092318351784648767380307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100061545567856432511586871 150092318351784648767380307)
      ·
        refine ⟨225138477527676973151070461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150092318351784648767380307 225138477527676973151070461)
        ·
          refine ⟨84426929072878864931651423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225138477527676973151070461 84426929072878864931651423)
          ·
            refine ⟨126640393609318297397477135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84426929072878864931651423 126640393609318297397477135)
            ·
              refine ⟨189960590413977446096215703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126640393609318297397477135 189960590413977446096215703)
              ·
                refine ⟨284940885620966169144323555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189960590413977446096215703 284940885620966169144323555)
                ·
                  refine ⟨427411328431449253716485333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284940885620966169144323555 427411328431449253716485333)
                  ·
                    refine ⟨10017453010112091883980125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 427411328431449253716485333 10017453010112091883980125)
                    ·
                      refine ⟨3756544878792034456492547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10017453010112091883980125 3756544878792034456492547)
                      ·
                        rfl

theorem cell23_7315845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_7315845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315845 prefixEnd_7315845 := by exact prefixLift 7315845
  have htrace : WordTrace (prefixWord ++ tailWord_7315845) baseStart_7315845 baseEnd_7315845 := by
    simpa [prefixWord, tailWord_7315845, baseEnd_7315845] using wordTrace_append hprefix tailTrace_7315845
  have hstable : (prefixWord ++ tailWord_7315845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315845).length < 2 ^ (prefixWord ++ tailWord_7315845).sum := by decide
  have hdescent : baseEnd_7315845 < baseStart_7315845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315873 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 3, 4]
def baseStart_7315873 : Nat := 118140960795 + 7315873 * 2 ^ 59
def prefixEnd_7315873 : Nat := 4983230072969 + 3 ^ 40 * 7315873 * 2
def baseEnd_7315873 : Nat := 1252186418750120115647473

theorem tailTrace_7315873 : CollatzResearch.WordTrace tailWord_7315873 prefixEnd_7315873 1252186418750120115647473 := by
  unfold tailWord_7315873
  simp only [CollatzResearch.WordTrace]
  refine ⟨266831809424849047479584273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177887872949899364986389515 266831809424849047479584273)
  ·
    refine ⟨200123857068636785609688205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266831809424849047479584273 200123857068636785609688205)
    ·
      refine ⟨75046446400738794603633077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200123857068636785609688205 75046446400738794603633077)
      ·
        refine ⟨7035604350069261994090601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75046446400738794603633077 7035604350069261994090601)
        ·
          refine ⟨5276703262551946495567951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7035604350069261994090601 5276703262551946495567951)
          ·
            refine ⟨7915054893827919743351927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276703262551946495567951 7915054893827919743351927)
            ·
              refine ⟨11872582340741879615027891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915054893827919743351927 11872582340741879615027891)
              ·
                refine ⟨17808873511112819422541837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872582340741879615027891 17808873511112819422541837)
                ·
                  refine ⟨6678327566667307283453189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17808873511112819422541837 6678327566667307283453189)
                  ·
                    refine ⟨1252186418750120115647473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678327566667307283453189 1252186418750120115647473)
                    ·
                      rfl

theorem cell23_7315873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_7315873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315873 prefixEnd_7315873 := by exact prefixLift 7315873
  have htrace : WordTrace (prefixWord ++ tailWord_7315873) baseStart_7315873 baseEnd_7315873 := by
    simpa [prefixWord, tailWord_7315873, baseEnd_7315873] using wordTrace_append hprefix tailTrace_7315873
  have hstable : (prefixWord ++ tailWord_7315873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315873).length < 2 ^ (prefixWord ++ tailWord_7315873).sum := by decide
  have hdescent : baseEnd_7315873 < baseStart_7315873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315912 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 1, 6]
def baseStart_7315912 : Nat := 118140960795 + 7315912 * 2 ^ 59
def prefixEnd_7315912 : Nat := 4983230072969 + 3 ^ 40 * 7315912 * 2
def baseEnd_7315912 : Nat := 1252193093998628564784913

theorem tailTrace_7315912 : CollatzResearch.WordTrace tailWord_7315912 prefixEnd_7315912 1252193093998628564784913 := by
  unfold tailWord_7315912
  simp only [CollatzResearch.WordTrace]
  refine ⟨133416615935853878570126995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177888821247805171426835993 133416615935853878570126995)
  ·
    refine ⟨200124923903780817855190493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133416615935853878570126995 200124923903780817855190493)
    ·
      refine ⟨75046846463917806695696435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200124923903780817855190493 75046846463917806695696435)
      ·
        refine ⟨112570269695876710043544653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75046846463917806695696435 112570269695876710043544653)
        ·
          refine ⟨42213851135953766266329245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112570269695876710043544653 42213851135953766266329245)
          ·
            refine ⟨15830194175982662349873467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42213851135953766266329245 15830194175982662349873467)
            ·
              refine ⟨23745291263973993524810201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15830194175982662349873467 23745291263973993524810201)
              ·
                refine ⟨17808968447980495143607651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23745291263973993524810201 17808968447980495143607651)
                ·
                  refine ⟨26713452671970742715411477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17808968447980495143607651 26713452671970742715411477)
                  ·
                    refine ⟨1252193093998628564784913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26713452671970742715411477 1252193093998628564784913)
                    ·
                      rfl

theorem cell23_7315912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_7315912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315912 prefixEnd_7315912 := by exact prefixLift 7315912
  have htrace : WordTrace (prefixWord ++ tailWord_7315912) baseStart_7315912 baseEnd_7315912 := by
    simpa [prefixWord, tailWord_7315912, baseEnd_7315912] using wordTrace_append hprefix tailTrace_7315912
  have hstable : (prefixWord ++ tailWord_7315912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315912).length < 2 ^ (prefixWord ++ tailWord_7315912).sum := by decide
  have hdescent : baseEnd_7315912 < baseStart_7315912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315916 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_7315916 : Nat := 118140960795 + 7315916 * 2 ^ 59
def prefixEnd_7315916 : Nat := 4983230072969 + 3 ^ 40 * 7315916 * 2
def baseEnd_7315916 : Nat := 1252193778639501226234907

theorem tailTrace_7315916 : CollatzResearch.WordTrace tailWord_7315916 prefixEnd_7315916 1252193778639501226234907 := by
  unfold tailWord_7315916
  simp only [CollatzResearch.WordTrace]
  refine ⟨133416688881846632911699801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177888918509128843882266401 133416688881846632911699801)
  ·
    refine ⟨100062516661384974683774851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133416688881846632911699801 100062516661384974683774851)
    ·
      refine ⟨150093774992077462025662277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100062516661384974683774851 150093774992077462025662277)
      ·
        refine ⟨28142582811014524129811677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150093774992077462025662277 28142582811014524129811677)
        ·
          refine ⟨10553468554130446548679379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28142582811014524129811677 10553468554130446548679379)
          ·
            refine ⟨15830202831195669823019069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10553468554130446548679379 15830202831195669823019069)
            ·
              refine ⟨5936326061698376183632151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15830202831195669823019069 5936326061698376183632151)
              ·
                refine ⟨8904489092547564275448227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936326061698376183632151 8904489092547564275448227)
                ·
                  refine ⟨13356733638821346413172341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904489092547564275448227 13356733638821346413172341)
                  ·
                    refine ⟨1252193778639501226234907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13356733638821346413172341 1252193778639501226234907)
                    ·
                      rfl

theorem cell23_7315916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_7315916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315916 prefixEnd_7315916 := by exact prefixLift 7315916
  have htrace : WordTrace (prefixWord ++ tailWord_7315916) baseStart_7315916 baseEnd_7315916 := by
    simpa [prefixWord, tailWord_7315916, baseEnd_7315916] using wordTrace_append hprefix tailTrace_7315916
  have hstable : (prefixWord ++ tailWord_7315916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315916).length < 2 ^ (prefixWord ++ tailWord_7315916).sum := by decide
  have hdescent : baseEnd_7315916 < baseStart_7315916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315925 : List Nat := [1, 3, 2, 3, 1, 13]
def baseStart_7315925 : Nat := 118140960795 + 7315925 * 2 ^ 59
def prefixEnd_7315925 : Nat := 4983230072969 + 3 ^ 40 * 7315925 * 2
def baseEnd_7315925 : Nat := 15459201470141539685153

theorem tailTrace_7315925 : CollatzResearch.WordTrace tailWord_7315925 prefixEnd_7315925 15459201470141539685153 := by
  unfold tailWord_7315925
  simp only [CollatzResearch.WordTrace]
  refine ⟨266833706020660660360477229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177889137347107106906984819 266833706020660660360477229)
  ·
    refine ⟨100062639757747747635178961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266833706020660660360477229 100062639757747747635178961)
    ·
      refine ⟨75046979818310810726384221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100062639757747747635178961 75046979818310810726384221)
      ·
        refine ⟨28142617431866554022394083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75046979818310810726384221 28142617431866554022394083)
        ·
          refine ⟨42213926147799831033591125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28142617431866554022394083 42213926147799831033591125)
          ·
            refine ⟨15459201470141539685153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42213926147799831033591125 15459201470141539685153)
            ·
              rfl

theorem cell23_7315925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 13].length) (baseStart_7315925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315925 prefixEnd_7315925 := by exact prefixLift 7315925
  have htrace : WordTrace (prefixWord ++ tailWord_7315925) baseStart_7315925 baseEnd_7315925 := by
    simpa [prefixWord, tailWord_7315925, baseEnd_7315925] using wordTrace_append hprefix tailTrace_7315925
  have hstable : (prefixWord ++ tailWord_7315925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315925).length < 2 ^ (prefixWord ++ tailWord_7315925).sum := by decide
  have hdescent : baseEnd_7315925 < baseStart_7315925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315929 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 2, 4]
def baseStart_7315929 : Nat := 118140960795 + 7315929 * 2 ^ 59
def prefixEnd_7315929 : Nat := 4983230072969 + 3 ^ 40 * 7315929 * 2
def baseEnd_7315929 : Nat := 1252196003722337375947387

theorem tailTrace_7315929 : CollatzResearch.WordTrace tailWord_7315929 prefixEnd_7315929 1252196003722337375947387 := by
  unfold tailWord_7315929
  simp only [CollatzResearch.WordTrace]
  refine ⟨266833851912646169043622841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177889234608430779362415227 266833851912646169043622841)
  ·
    refine ⟨200125388934484626782717131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266833851912646169043622841 200125388934484626782717131)
    ·
      refine ⟨300188083401726940174075697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200125388934484626782717131 300188083401726940174075697)
      ·
        refine ⟨225141062551295205130556773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300188083401726940174075697 225141062551295205130556773)
        ·
          refine ⟨42213949228367850961979395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225141062551295205130556773 42213949228367850961979395)
          ·
            refine ⟨63320923842551776442969093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42213949228367850961979395 63320923842551776442969093)
            ·
              refine ⟨11872673220478458083056705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63320923842551776442969093 11872673220478458083056705)
              ·
                refine ⟨8904504915358843562292529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11872673220478458083056705 8904504915358843562292529)
                ·
                  refine ⟨6678378686519132671719397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8904504915358843562292529 6678378686519132671719397)
                  ·
                    refine ⟨1252196003722337375947387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678378686519132671719397 1252196003722337375947387)
                    ·
                      rfl

theorem cell23_7315929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_7315929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315929 prefixEnd_7315929 := by exact prefixLift 7315929
  have htrace : WordTrace (prefixWord ++ tailWord_7315929) baseStart_7315929 baseEnd_7315929 := by
    simpa [prefixWord, tailWord_7315929, baseEnd_7315929] using wordTrace_append hprefix tailTrace_7315929
  have hstable : (prefixWord ++ tailWord_7315929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315929).length < 2 ^ (prefixWord ++ tailWord_7315929).sum := by decide
  have hdescent : baseEnd_7315929 < baseStart_7315929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315949 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7315949 : Nat := 118140960795 + 7315949 * 2 ^ 59
def prefixEnd_7315949 : Nat := 4983230072969 + 3 ^ 40 * 7315949 * 2
def baseEnd_7315949 : Nat := 3756598280780102049592069

theorem tailTrace_7315949 : CollatzResearch.WordTrace tailWord_7315949 prefixEnd_7315949 3756598280780102049592069 := by
  unfold tailWord_7315949
  simp only [CollatzResearch.WordTrace]
  refine ⟨266834581372573712459350901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177889720915049141639567267 266834581372573712459350901)
  ·
    refine ⟨25015742003678785543064147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 266834581372573712459350901 25015742003678785543064147)
    ·
      refine ⟨37523613005518178314596221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25015742003678785543064147 37523613005518178314596221)
      ·
        refine ⟨14071354877069316867973583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37523613005518178314596221 14071354877069316867973583)
        ·
          refine ⟨21107032315603975301960375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14071354877069316867973583 21107032315603975301960375)
          ·
            refine ⟨31660548473405962952940563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21107032315603975301960375 31660548473405962952940563)
            ·
              refine ⟨47490822710108944429410845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31660548473405962952940563 47490822710108944429410845)
              ·
                refine ⟨17809058516290854161029067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47490822710108944429410845 17809058516290854161029067)
                ·
                  refine ⟨26713587774436281241543601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17809058516290854161029067 26713587774436281241543601)
                  ·
                    refine ⟨20035190830827210931157701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26713587774436281241543601 20035190830827210931157701)
                    ·
                      refine ⟨3756598280780102049592069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20035190830827210931157701 3756598280780102049592069)
                      ·
                        rfl

theorem cell23_7315949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7315949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315949 prefixEnd_7315949 := by exact prefixLift 7315949
  have htrace : WordTrace (prefixWord ++ tailWord_7315949) baseStart_7315949 baseEnd_7315949 := by
    simpa [prefixWord, tailWord_7315949, baseEnd_7315949] using wordTrace_append hprefix tailTrace_7315949
  have hstable : (prefixWord ++ tailWord_7315949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315949).length < 2 ^ (prefixWord ++ tailWord_7315949).sum := by decide
  have hdescent : baseEnd_7315949 < baseStart_7315949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315955 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 2, 7]
def baseStart_7315955 : Nat := 118140960795 + 7315955 * 2 ^ 59
def prefixEnd_7315955 : Nat := 4983230072969 + 3 ^ 40 * 7315955 * 2
def baseEnd_7315955 : Nat := 1252200453888009675372347

theorem tailTrace_7315955 : CollatzResearch.WordTrace tailWord_7315955 prefixEnd_7315955 1252200453888009675372347 := by
  unfold tailWord_7315955
  simp only [CollatzResearch.WordTrace]
  refine ⟨266834800210551975484069319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177889866807034650322712879 266834800210551975484069319)
  ·
    refine ⟨400252200315827963226103979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266834800210551975484069319 400252200315827963226103979)
    ·
      refine ⟨600378300473741944839155969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400252200315827963226103979 600378300473741944839155969)
      ·
        refine ⟨450283725355306458629366977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600378300473741944839155969 450283725355306458629366977)
        ·
          refine ⟨337712794016479843972025233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450283725355306458629366977 337712794016479843972025233)
          ·
            refine ⟨253284595512359882979018925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337712794016479843972025233 253284595512359882979018925)
            ·
              refine ⟨94981723317134956117132097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253284595512359882979018925 94981723317134956117132097)
              ·
                refine ⟨71236292487851217087849073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94981723317134956117132097 71236292487851217087849073)
                ·
                  refine ⟨53427219365888412815886805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71236292487851217087849073 53427219365888412815886805)
                  ·
                    refine ⟨1252200453888009675372347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53427219365888412815886805 1252200453888009675372347)
                    ·
                      rfl

theorem cell23_7315955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 7].length) (baseStart_7315955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315955 prefixEnd_7315955 := by exact prefixLift 7315955
  have htrace : WordTrace (prefixWord ++ tailWord_7315955) baseStart_7315955 baseEnd_7315955 := by
    simpa [prefixWord, tailWord_7315955, baseEnd_7315955] using wordTrace_append hprefix tailTrace_7315955
  have hstable : (prefixWord ++ tailWord_7315955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315955).length < 2 ^ (prefixWord ++ tailWord_7315955).sum := by decide
  have hdescent : baseEnd_7315955 < baseStart_7315955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315969 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_7315969 : Nat := 118140960795 + 7315969 * 2 ^ 59
def prefixEnd_7315969 : Nat := 4983230072969 + 3 ^ 40 * 7315969 * 2
def baseEnd_7315969 : Nat := 3756608550393191971341977

theorem tailTrace_7315969 : CollatzResearch.WordTrace tailWord_7315969 prefixEnd_7315969 3756608550393191971341977 := by
  unfold tailWord_7315969
  simp only [CollatzResearch.WordTrace]
  refine ⟨266835310832501255875078961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177890207221667503916719307 266835310832501255875078961)
  ·
    refine ⟨200126483124375941906309221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266835310832501255875078961 200126483124375941906309221)
    ·
      refine ⟨37523715585820489107432979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200126483124375941906309221 37523715585820489107432979)
      ·
        refine ⟨56285573378730733661149469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37523715585820489107432979 56285573378730733661149469)
        ·
          refine ⟨21107090017024025122931051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56285573378730733661149469 21107090017024025122931051)
          ·
            refine ⟨31660635025536037684396577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21107090017024025122931051 31660635025536037684396577)
            ·
              refine ⟨23745476269152028263297433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31660635025536037684396577 23745476269152028263297433)
              ·
                refine ⟨17809107201864021197473075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23745476269152028263297433 17809107201864021197473075)
                ·
                  refine ⟨26713660802796031796209613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17809107201864021197473075 26713660802796031796209613)
                  ·
                    refine ⟨10017622801048511923578605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26713660802796031796209613 10017622801048511923578605)
                    ·
                      refine ⟨3756608550393191971341977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10017622801048511923578605 3756608550393191971341977)
                      ·
                        rfl

theorem cell23_7315969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_7315969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315969 prefixEnd_7315969 := by exact prefixLift 7315969
  have htrace : WordTrace (prefixWord ++ tailWord_7315969) baseStart_7315969 baseEnd_7315969 := by
    simpa [prefixWord, tailWord_7315969, baseEnd_7315969] using wordTrace_append hprefix tailTrace_7315969
  have hstable : (prefixWord ++ tailWord_7315969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315969).length < 2 ^ (prefixWord ++ tailWord_7315969).sum := by decide
  have hdescent : baseEnd_7315969 < baseStart_7315969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7315970 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7315970 : Nat := 118140960795 + 7315970 * 2 ^ 59
def prefixEnd_7315970 : Nat := 4983230072969 + 3 ^ 40 * 7315970 * 2
def baseEnd_7315970 : Nat := 3756609063873846467429473

theorem tailTrace_7315970 : CollatzResearch.WordTrace tailWord_7315970 prefixEnd_7315970 3756609063873846467429473 := by
  unfold tailWord_7315970
  simp only [CollatzResearch.WordTrace]
  refine ⟨66708836826374408261466341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177890231536998422030576909 66708836826374408261466341)
  ·
    refine ⟨12507906904945201549024939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66708836826374408261466341 12507906904945201549024939)
    ·
      refine ⟨18761860357417802323537409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12507906904945201549024939 18761860357417802323537409)
      ·
        refine ⟨14071395268063351742653057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18761860357417802323537409 14071395268063351742653057)
        ·
          refine ⟨10553546451047513806989793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14071395268063351742653057 10553546451047513806989793)
          ·
            refine ⟨7915159838285635355242345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10553546451047513806989793 7915159838285635355242345)
            ·
              refine ⟨5936369878714226516431759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7915159838285635355242345 5936369878714226516431759)
              ·
                refine ⟨8904554818071339774647639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936369878714226516431759 8904554818071339774647639)
                ·
                  refine ⟨13356832227107009661971459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904554818071339774647639 13356832227107009661971459)
                  ·
                    refine ⟨20035248340660514492957189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13356832227107009661971459 20035248340660514492957189)
                    ·
                      refine ⟨3756609063873846467429473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20035248340660514492957189 3756609063873846467429473)
                      ·
                        rfl

theorem cell23_7315970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7315970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7315970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7315970 prefixEnd_7315970 := by exact prefixLift 7315970
  have htrace : WordTrace (prefixWord ++ tailWord_7315970) baseStart_7315970 baseEnd_7315970 := by
    simpa [prefixWord, tailWord_7315970, baseEnd_7315970] using wordTrace_append hprefix tailTrace_7315970
  have hstable : (prefixWord ++ tailWord_7315970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7315970).length < 2 ^ (prefixWord ++ tailWord_7315970).sum := by decide
  have hdescent : baseEnd_7315970 < baseStart_7315970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7315970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316003 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 2, 1, 3]
def baseStart_7316003 : Nat := 118140960795 + 7316003 * 2 ^ 59
def prefixEnd_7316003 : Nat := 4983230072969 + 3 ^ 40 * 7316003 * 2
def baseEnd_7316003 : Nat := 3756626008735444838316821

theorem tailTrace_7316003 : CollatzResearch.WordTrace tailWord_7316003 prefixEnd_7316003 3756626008735444838316821 := by
  unfold tailWord_7316003
  simp only [CollatzResearch.WordTrace]
  refine ⟨266836550914378079681816663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177891033942918719787877775 266836550914378079681816663)
  ·
    refine ⟨400254826371567119522724995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266836550914378079681816663 400254826371567119522724995)
    ·
      refine ⟨600382239557350679284087493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400254826371567119522724995 600382239557350679284087493)
      ·
        refine ⟨112571669917003252365766405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 600382239557350679284087493 112571669917003252365766405)
        ·
          refine ⟨21107188109438109818581201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112571669917003252365766405 21107188109438109818581201)
          ·
            refine ⟨15830391082078582363935901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21107188109438109818581201 15830391082078582363935901)
            ·
              refine ⟨5936396655779468386475963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15830391082078582363935901 5936396655779468386475963)
              ·
                refine ⟨8904594983669202579713945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936396655779468386475963 8904594983669202579713945)
                ·
                  refine ⟨6678446237751901934785459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8904594983669202579713945 6678446237751901934785459)
                  ·
                    refine ⟨10017669356627852902178189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6678446237751901934785459 10017669356627852902178189)
                    ·
                      refine ⟨3756626008735444838316821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10017669356627852902178189 3756626008735444838316821)
                      ·
                        rfl

theorem cell23_7316003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_7316003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316003 prefixEnd_7316003 := by exact prefixLift 7316003
  have htrace : WordTrace (prefixWord ++ tailWord_7316003) baseStart_7316003 baseEnd_7316003 := by
    simpa [prefixWord, tailWord_7316003, baseEnd_7316003] using wordTrace_append hprefix tailTrace_7316003
  have hstable : (prefixWord ++ tailWord_7316003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316003).length < 2 ^ (prefixWord ++ tailWord_7316003).sum := by decide
  have hdescent : baseEnd_7316003 < baseStart_7316003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316012 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_7316012 : Nat := 118140960795 + 7316012 * 2 ^ 59
def prefixEnd_7316012 : Nat := 4983230072969 + 3 ^ 40 * 7316012 * 2
def baseEnd_7316012 : Nat := 3756630630061335303104279

theorem tailTrace_7316012 : CollatzResearch.WordTrace tailWord_7316012 prefixEnd_7316012 3756630630061335303104279 := by
  unfold tailWord_7316012
  simp only [CollatzResearch.WordTrace]
  refine ⟨133418439585672737109447145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177891252780896982812596193 133418439585672737109447145)
  ·
    refine ⟨100063829689254552832085359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133418439585672737109447145 100063829689254552832085359)
    ·
      refine ⟨150095744533881829248128039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100063829689254552832085359 150095744533881829248128039)
      ·
        refine ⟨225143616800822743872192059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150095744533881829248128039 225143616800822743872192059)
        ·
          refine ⟨337715425201234115808288089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225143616800822743872192059 337715425201234115808288089)
          ·
            refine ⟨253286568900925586856216067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337715425201234115808288089 253286568900925586856216067)
            ·
              refine ⟨379929853351388380284324101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253286568900925586856216067 379929853351388380284324101)
              ·
                refine ⟨71236847503385321303310769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379929853351388380284324101 71236847503385321303310769)
                ·
                  refine ⟨53427635627538990977483077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71236847503385321303310769 53427635627538990977483077)
                  ·
                    refine ⟨10017681680163560808278077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53427635627538990977483077 10017681680163560808278077)
                    ·
                      refine ⟨3756630630061335303104279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10017681680163560808278077 3756630630061335303104279)
                      ·
                        rfl

theorem cell23_7316012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_7316012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316012 prefixEnd_7316012 := by exact prefixLift 7316012
  have htrace : WordTrace (prefixWord ++ tailWord_7316012) baseStart_7316012 baseEnd_7316012 := by
    simpa [prefixWord, tailWord_7316012, baseEnd_7316012] using wordTrace_append hprefix tailTrace_7316012
  have hstable : (prefixWord ++ tailWord_7316012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316012).length < 2 ^ (prefixWord ++ tailWord_7316012).sum := by decide
  have hdescent : baseEnd_7316012 < baseStart_7316012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316026 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2]
def baseStart_7316026 : Nat := 118140960795 + 7316026 * 2 ^ 59
def prefixEnd_7316026 : Nat := 4983230072969 + 3 ^ 40 * 7316026 * 2
def baseEnd_7316026 : Nat := 3756637818790498248329215

theorem tailTrace_7316026 : CollatzResearch.WordTrace tailWord_7316026 prefixEnd_7316026 3756637818790498248329215 := by
  unfold tailWord_7316026
  simp only [CollatzResearch.WordTrace]
  refine ⟨66709347448323688652475983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177891593195529836406602621 66709347448323688652475983)
  ·
    refine ⟨100064021172485532978713975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66709347448323688652475983 100064021172485532978713975)
    ·
      refine ⟨150096031758728299468070963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100064021172485532978713975 150096031758728299468070963)
      ·
        refine ⟨225144047638092449202106445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150096031758728299468070963 225144047638092449202106445)
        ·
          refine ⟨84429017864284668450789917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225144047638092449202106445 84429017864284668450789917)
          ·
            refine ⟨31660881699106750669046219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84429017864284668450789917 31660881699106750669046219)
            ·
              refine ⟨47491322548660126003569329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31660881699106750669046219 47491322548660126003569329)
              ·
                refine ⟨35618491911495094502676997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47491322548660126003569329 35618491911495094502676997)
                ·
                  refine ⟨6678467233405330219251937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35618491911495094502676997 6678467233405330219251937)
                  ·
                    refine ⟨5008850425053997664438953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6678467233405330219251937 5008850425053997664438953)
                    ·
                      refine ⟨3756637818790498248329215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008850425053997664438953 3756637818790498248329215)
                      ·
                        rfl

theorem cell23_7316026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_7316026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316026 prefixEnd_7316026 := by exact prefixLift 7316026
  have htrace : WordTrace (prefixWord ++ tailWord_7316026) baseStart_7316026 baseEnd_7316026 := by
    simpa [prefixWord, tailWord_7316026, baseEnd_7316026] using wordTrace_append hprefix tailTrace_7316026
  have hstable : (prefixWord ++ tailWord_7316026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316026).length < 2 ^ (prefixWord ++ tailWord_7316026).sum := by decide
  have hdescent : baseEnd_7316026 < baseStart_7316026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316029 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7316029 : Nat := 118140960795 + 7316029 * 2 ^ 59
def prefixEnd_7316029 : Nat := 4983230072969 + 3 ^ 40 * 7316029 * 2
def baseEnd_7316029 : Nat := 3756639359232461736591701

theorem tailTrace_7316029 : CollatzResearch.WordTrace tailWord_7316029 prefixEnd_7316029 3756639359232461736591701 := by
  unfold tailWord_7316029
  simp only [CollatzResearch.WordTrace]
  refine ⟨266837499212283886122263141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177891666141522590748175427 266837499212283886122263141)
  ·
    refine ⟨50032031102303228647924339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266837499212283886122263141 50032031102303228647924339)
    ·
      refine ⟨75048046653454842971886509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50032031102303228647924339 75048046653454842971886509)
      ·
        refine ⟨28143017495045566114457441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75048046653454842971886509 28143017495045566114457441)
        ·
          refine ⟨21107263121284174585843081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28143017495045566114457441 21107263121284174585843081)
          ·
            refine ⟨15830447340963130939382311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21107263121284174585843081 15830447340963130939382311)
            ·
              refine ⟨23745671011444696409073467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15830447340963130939382311 23745671011444696409073467)
              ·
                refine ⟨35618506517167044613610201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23745671011444696409073467 35618506517167044613610201)
                ·
                  refine ⟨26713879887875283460207651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35618506517167044613610201 26713879887875283460207651)
                  ·
                    refine ⟨40070819831812925190311477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26713879887875283460207651 40070819831812925190311477)
                    ·
                      refine ⟨3756639359232461736591701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40070819831812925190311477 3756639359232461736591701)
                      ·
                        rfl

theorem cell23_7316029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7316029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316029 prefixEnd_7316029 := by exact prefixLift 7316029
  have htrace : WordTrace (prefixWord ++ tailWord_7316029) baseStart_7316029 baseEnd_7316029 := by
    simpa [prefixWord, tailWord_7316029, baseEnd_7316029] using wordTrace_append hprefix tailTrace_7316029
  have hstable : (prefixWord ++ tailWord_7316029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316029).length < 2 ^ (prefixWord ++ tailWord_7316029).sum := by decide
  have hdescent : baseEnd_7316029 < baseStart_7316029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316049 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 7]
def baseStart_7316049 : Nat := 118140960795 + 7316049 * 2 ^ 59
def prefixEnd_7316049 : Nat := 4983230072969 + 3 ^ 40 * 7316049 * 2
def baseEnd_7316049 : Nat := 417405514316172406482401

theorem tailTrace_7316049 : CollatzResearch.WordTrace tailWord_7316049 prefixEnd_7316049 417405514316172406482401 := by
  unfold tailWord_7316049
  simp only [CollatzResearch.WordTrace]
  refine ⟨266838228672211429537991201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177892152448140953025327467 266838228672211429537991201)
  ·
    refine ⟨200128671504158572153493401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266838228672211429537991201 200128671504158572153493401)
    ·
      refine ⟨150096503628118929115120051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200128671504158572153493401 150096503628118929115120051)
      ·
        refine ⟨225144755442178393672680077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150096503628118929115120051 225144755442178393672680077)
        ·
          refine ⟨84429283290816897627255029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225144755442178393672680077 84429283290816897627255029)
          ·
            refine ⟨7915245308514084152555159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84429283290816897627255029 7915245308514084152555159)
            ·
              refine ⟨11872867962771126228832739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915245308514084152555159 11872867962771126228832739)
              ·
                refine ⟨17809301944156689343249109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872867962771126228832739 17809301944156689343249109)
                ·
                  refine ⟨417405514316172406482401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17809301944156689343249109 417405514316172406482401)
                  ·
                    rfl

theorem cell23_7316049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 7].length) (baseStart_7316049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316049 prefixEnd_7316049 := by exact prefixLift 7316049
  have htrace : WordTrace (prefixWord ++ tailWord_7316049) baseStart_7316049 baseEnd_7316049 := by
    simpa [prefixWord, tailWord_7316049, baseEnd_7316049] using wordTrace_append hprefix tailTrace_7316049
  have hstable : (prefixWord ++ tailWord_7316049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316049).length < 2 ^ (prefixWord ++ tailWord_7316049).sum := by decide
  have hdescent : baseEnd_7316049 < baseStart_7316049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316060 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_7316060 : Nat := 118140960795 + 7316060 * 2 ^ 59
def prefixEnd_7316060 : Nat := 4983230072969 + 3 ^ 40 * 7316060 * 2
def baseEnd_7316060 : Nat := 3756655277132751115304059

theorem tailTrace_7316060 : CollatzResearch.WordTrace tailWord_7316060 prefixEnd_7316060 3756655277132751115304059 := by
  unfold tailWord_7316060
  simp only [CollatzResearch.WordTrace]
  refine ⟨133419314937585789208320817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177892419916781052277761089 133419314937585789208320817)
  ·
    refine ⟨100064486203189341906240613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133419314937585789208320817 100064486203189341906240613)
    ·
      refine ⟨18762091163098001607420115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100064486203189341906240613 18762091163098001607420115)
      ·
        refine ⟨28143136744647002411130173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18762091163098001607420115 28143136744647002411130173)
        ·
          refine ⟨10553676279242625904173815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28143136744647002411130173 10553676279242625904173815)
          ·
            refine ⟨15830514418863938856260723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10553676279242625904173815 15830514418863938856260723)
            ·
              refine ⟨23745771628295908284391085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15830514418863938856260723 23745771628295908284391085)
              ·
                refine ⟨8904664360610965606646657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23745771628295908284391085 8904664360610965606646657)
                ·
                  refine ⟨6678498270458224204984993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8904664360610965606646657 6678498270458224204984993)
                  ·
                    refine ⟨5008873702843668153738745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6678498270458224204984993 5008873702843668153738745)
                    ·
                      refine ⟨3756655277132751115304059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5008873702843668153738745 3756655277132751115304059)
                      ·
                        rfl

theorem cell23_7316060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_7316060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316060 prefixEnd_7316060 := by exact prefixLift 7316060
  have htrace : WordTrace (prefixWord ++ tailWord_7316060) baseStart_7316060 baseEnd_7316060 := by
    simpa [prefixWord, tailWord_7316060, baseEnd_7316060] using wordTrace_append hprefix tailTrace_7316060
  have hstable : (prefixWord ++ tailWord_7316060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316060).length < 2 ^ (prefixWord ++ tailWord_7316060).sum := by decide
  have hdescent : baseEnd_7316060 < baseStart_7316060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316099 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 4]
def baseStart_7316099 : Nat := 118140960795 + 7316099 * 2 ^ 59
def prefixEnd_7316099 : Nat := 4983230072969 + 3 ^ 40 * 7316099 * 2
def baseEnd_7316099 : Nat := 3756675302878276462716379

theorem tailTrace_7316099 : CollatzResearch.WordTrace tailWord_7316099 prefixEnd_7316099 3756675302878276462716379 := by
  unfold tailWord_7316099
  simp only [CollatzResearch.WordTrace]
  refine ⟨266840052322030288077311351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177893368214686858718207567 266840052322030288077311351)
  ·
    refine ⟨400260078483045432115967027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266840052322030288077311351 400260078483045432115967027)
    ·
      refine ⟨600390117724568148173950541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400260078483045432115967027 600390117724568148173950541)
      ·
        refine ⟨225146294146713055565231453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600390117724568148173950541 225146294146713055565231453)
        ·
          refine ⟨84429860305017395836961795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225146294146713055565231453 84429860305017395836961795)
          ·
            refine ⟨126644790457526093755442693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84429860305017395836961795 126644790457526093755442693)
            ·
              refine ⟨23745898210786142579145505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126644790457526093755442693 23745898210786142579145505)
              ·
                refine ⟨17809423658089606934359129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23745898210786142579145505 17809423658089606934359129)
                ·
                  refine ⟨13357067743567205200769347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17809423658089606934359129 13357067743567205200769347)
                  ·
                    refine ⟨20035601615350807801154021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13357067743567205200769347 20035601615350807801154021)
                    ·
                      refine ⟨3756675302878276462716379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20035601615350807801154021 3756675302878276462716379)
                      ·
                        rfl

theorem cell23_7316099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_7316099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316099 prefixEnd_7316099 := by exact prefixLift 7316099
  have htrace : WordTrace (prefixWord ++ tailWord_7316099) baseStart_7316099 baseEnd_7316099 := by
    simpa [prefixWord, tailWord_7316099, baseEnd_7316099] using wordTrace_append hprefix tailTrace_7316099
  have hstable : (prefixWord ++ tailWord_7316099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316099).length < 2 ^ (prefixWord ++ tailWord_7316099).sum := by decide
  have hdescent : baseEnd_7316099 < baseStart_7316099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316112 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_7316112 : Nat := 118140960795 + 7316112 * 2 ^ 59
def prefixEnd_7316112 : Nat := 4983230072969 + 3 ^ 40 * 7316112 * 2
def baseEnd_7316112 : Nat := 3756681978126784911853819

theorem tailTrace_7316112 : CollatzResearch.WordTrace tailWord_7316112 prefixEnd_7316112 3756681978126784911853819 := by
  unfold tailWord_7316112
  simp only [CollatzResearch.WordTrace]
  refine ⟨133420263235491595648767295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177893684313988794198356393 133420263235491595648767295)
  ·
    refine ⟨200130394853237393473150943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133420263235491595648767295 200130394853237393473150943)
    ·
      refine ⟨300195592279856090209726415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200130394853237393473150943 300195592279856090209726415)
      ·
        refine ⟨450293388419784135314589623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300195592279856090209726415 450293388419784135314589623)
        ·
          refine ⟨675440082629676202971884435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450293388419784135314589623 675440082629676202971884435)
          ·
            refine ⟨1013160123944514304457826653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675440082629676202971884435 1013160123944514304457826653)
            ·
              refine ⟨379935046479192864171684995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013160123944514304457826653 379935046479192864171684995)
              ·
                refine ⟨569902569718789296257527493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379935046479192864171684995 569902569718789296257527493)
                ·
                  refine ⟨106856731822272993048286405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569902569718789296257527493 106856731822272993048286405)
                  ·
                    refine ⟨20035637216676186196553701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106856731822272993048286405 20035637216676186196553701)
                    ·
                      refine ⟨3756681978126784911853819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20035637216676186196553701 3756681978126784911853819)
                      ·
                        rfl

theorem cell23_7316112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_7316112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316112 prefixEnd_7316112 := by exact prefixLift 7316112
  have htrace : WordTrace (prefixWord ++ tailWord_7316112) baseStart_7316112 baseEnd_7316112 := by
    simpa [prefixWord, tailWord_7316112, baseEnd_7316112] using wordTrace_append hprefix tailTrace_7316112
  have hstable : (prefixWord ++ tailWord_7316112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316112).length < 2 ^ (prefixWord ++ tailWord_7316112).sum := by decide
  have hdescent : baseEnd_7316112 < baseStart_7316112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316119 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_7316119 : Nat := 118140960795 + 7316119 * 2 ^ 59
def prefixEnd_7316119 : Nat := 4983230072969 + 3 ^ 40 * 7316119 * 2
def baseEnd_7316119 : Nat := 3756685572491366384466287

theorem tailTrace_7316119 : CollatzResearch.WordTrace tailWord_7316119 prefixEnd_7316119 3756685572491366384466287 := by
  unfold tailWord_7316119
  simp only [CollatzResearch.WordTrace]
  refine ⟨266840781781957831493039411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177893854521305220995359607 266840781781957831493039411)
  ·
    refine ⟨400261172672936747239559117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266840781781957831493039411 400261172672936747239559117)
    ·
      refine ⟨150097939752351280214834669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400261172672936747239559117 150097939752351280214834669)
      ·
        refine ⟨56286727407131730080563001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150097939752351280214834669 56286727407131730080563001)
        ·
          refine ⟨42215045555348797560422251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56286727407131730080563001 42215045555348797560422251)
          ·
            refine ⟨63322568333023196340633377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42215045555348797560422251 63322568333023196340633377)
            ·
              refine ⟨47491926249767397255475033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63322568333023196340633377 47491926249767397255475033)
              ·
                refine ⟨35618944687325547941606275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47491926249767397255475033 35618944687325547941606275)
                ·
                  refine ⟨53428417030988321912409413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35618944687325547941606275 53428417030988321912409413)
                  ·
                    refine ⟨10017828193310310358576765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53428417030988321912409413 10017828193310310358576765)
                    ·
                      refine ⟨3756685572491366384466287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10017828193310310358576765 3756685572491366384466287)
                      ·
                        rfl

theorem cell23_7316119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_7316119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316119 prefixEnd_7316119 := by exact prefixLift 7316119
  have htrace : WordTrace (prefixWord ++ tailWord_7316119) baseStart_7316119 baseEnd_7316119 := by
    simpa [prefixWord, tailWord_7316119, baseEnd_7316119] using wordTrace_append hprefix tailTrace_7316119
  have hstable : (prefixWord ++ tailWord_7316119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316119).length < 2 ^ (prefixWord ++ tailWord_7316119).sum := by decide
  have hdescent : baseEnd_7316119 < baseStart_7316119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316143 : List Nat := [1, 1, 2, 1, 2, 6, 2, 3, 1, 4]
def baseStart_7316143 : Nat := 118140960795 + 7316143 * 2 ^ 59
def prefixEnd_7316143 : Nat := 4983230072969 + 3 ^ 40 * 7316143 * 2
def baseEnd_7316143 : Nat := 1252232632009024763522059

theorem tailTrace_7316143 : CollatzResearch.WordTrace tailWord_7316143 prefixEnd_7316143 1252232632009024763522059 := by
  unfold tailWord_7316143
  simp only [CollatzResearch.WordTrace]
  refine ⟨266841657133870883591913083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177894438089247255727942055 266841657133870883591913083)
  ·
    refine ⟨400262485700806325387869625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266841657133870883591913083 400262485700806325387869625)
    ·
      refine ⟨300196864275604744040902219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400262485700806325387869625 300196864275604744040902219)
      ·
        refine ⟨450295296413407116061353329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300196864275604744040902219 450295296413407116061353329)
        ·
          refine ⟨337721472310055337046014997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450295296413407116061353329 337721472310055337046014997)
          ·
            refine ⟨15830694014533843924031953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 337721472310055337046014997 15830694014533843924031953)
            ·
              refine ⟨11873020510900382943023965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15830694014533843924031953 11873020510900382943023965)
              ·
                refine ⟨4452382691587643603633987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11873020510900382943023965 4452382691587643603633987)
                ·
                  refine ⟨6678574037381465405450981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452382691587643603633987 6678574037381465405450981)
                  ·
                    refine ⟨1252232632009024763522059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678574037381465405450981 1252232632009024763522059)
                    ·
                      rfl

theorem cell23_7316143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 4].length) (baseStart_7316143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316143 prefixEnd_7316143 := by exact prefixLift 7316143
  have htrace : WordTrace (prefixWord ++ tailWord_7316143) baseStart_7316143 baseEnd_7316143 := by
    simpa [prefixWord, tailWord_7316143, baseEnd_7316143] using wordTrace_append hprefix tailTrace_7316143
  have hstable : (prefixWord ++ tailWord_7316143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316143).length < 2 ^ (prefixWord ++ tailWord_7316143).sum := by decide
  have hdescent : baseEnd_7316143 < baseStart_7316143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316186 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_7316186 : Nat := 118140960795 + 7316186 * 2 ^ 59
def prefixEnd_7316186 : Nat := 4983230072969 + 3 ^ 40 * 7316186 * 2
def baseEnd_7316186 : Nat := 1252239991898405874109493

theorem tailTrace_7316186 : CollatzResearch.WordTrace tailWord_7316186 prefixEnd_7316186 1252239991898405874109493 := by
  unfold tailWord_7316186
  simp only [CollatzResearch.WordTrace]
  refine ⟨66710806368178775483932103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177895483648476734623818941 66710806368178775483932103)
  ·
    refine ⟨100066209552268163225898155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66710806368178775483932103 100066209552268163225898155)
    ·
      refine ⟨150099314328402244838847233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100066209552268163225898155 150099314328402244838847233)
      ·
        refine ⟨112574485746301683629135425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150099314328402244838847233 112574485746301683629135425)
        ·
          refine ⟨84430864309726262721851569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112574485746301683629135425 84430864309726262721851569)
          ·
            refine ⟨63323148232294697041388677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84430864309726262721851569 63323148232294697041388677)
            ·
              refine ⟨11873090293555255695260377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63323148232294697041388677 11873090293555255695260377)
              ·
                refine ⟨8904817720166441771445283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11873090293555255695260377 8904817720166441771445283)
                ·
                  refine ⟨13357226580249662657167925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904817720166441771445283 13357226580249662657167925)
                  ·
                    refine ⟨1252239991898405874109493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13357226580249662657167925 1252239991898405874109493)
                    ·
                      rfl

theorem cell23_7316186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_7316186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316186 prefixEnd_7316186 := by exact prefixLift 7316186
  have htrace : WordTrace (prefixWord ++ tailWord_7316186) baseStart_7316186 baseEnd_7316186 := by
    simpa [prefixWord, tailWord_7316186, baseEnd_7316186] using wordTrace_append hprefix tailTrace_7316186
  have hstable : (prefixWord ++ tailWord_7316186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316186).length < 2 ^ (prefixWord ++ tailWord_7316186).sum := by decide
  have hdescent : baseEnd_7316186 < baseStart_7316186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316216 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 2, 4]
def baseStart_7316216 : Nat := 118140960795 + 7316216 * 2 ^ 59
def prefixEnd_7316216 : Nat := 4983230072969 + 3 ^ 40 * 7316216 * 2
def baseEnd_7316216 : Nat := 1252245126704950834984447

theorem tailTrace_7316216 : CollatzResearch.WordTrace tailWord_7316216 prefixEnd_7316216 1252245126704950834984447 := by
  unfold tailWord_7316216
  simp only [CollatzResearch.WordTrace]
  refine ⟨133422159831303208529660251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177896213108404278039547001 133422159831303208529660251)
  ·
    refine ⟨200133239746954812794490377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133422159831303208529660251 200133239746954812794490377)
    ·
      refine ⟨150099929810216109595867783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200133239746954812794490377 150099929810216109595867783)
      ·
        refine ⟨225149894715324164393801675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150099929810216109595867783 225149894715324164393801675)
        ·
          refine ⟨337724842072986246590702513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225149894715324164393801675 337724842072986246590702513)
          ·
            refine ⟨253293631554739684943026885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337724842072986246590702513 253293631554739684943026885)
            ·
              refine ⟨47492555916513690926817541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253293631554739684943026885 47492555916513690926817541)
              ·
                refine ⟨8904854234346317048778289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47492555916513690926817541 8904854234346317048778289)
                ·
                  refine ⟨6678640675759737786583717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8904854234346317048778289 6678640675759737786583717)
                  ·
                    refine ⟨1252245126704950834984447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678640675759737786583717 1252245126704950834984447)
                    ·
                      rfl

theorem cell23_7316216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_7316216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316216 prefixEnd_7316216 := by exact prefixLift 7316216
  have htrace : WordTrace (prefixWord ++ tailWord_7316216) baseStart_7316216 baseEnd_7316216 := by
    simpa [prefixWord, tailWord_7316216, baseEnd_7316216] using wordTrace_append hprefix tailTrace_7316216
  have hstable : (prefixWord ++ tailWord_7316216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316216).length < 2 ^ (prefixWord ++ tailWord_7316216).sum := by decide
  have hdescent : baseEnd_7316216 < baseStart_7316216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316233 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 2, 4]
def baseStart_7316233 : Nat := 118140960795 + 7316233 * 2 ^ 59
def prefixEnd_7316233 : Nat := 4983230072969 + 3 ^ 40 * 7316233 * 2
def baseEnd_7316233 : Nat := 1252248036428659646146921

theorem tailTrace_7316233 : CollatzResearch.WordTrace tailWord_7316233 prefixEnd_7316233 1252248036428659646146921 := by
  unfold tailWord_7316233
  simp only [CollatzResearch.WordTrace]
  refine ⟨266844939703544828962689353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177896626469029885975126235 266844939703544828962689353)
  ·
    refine ⟨200133704777658621722017015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266844939703544828962689353 200133704777658621722017015)
    ·
      refine ⟨300200557166487932583025523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200133704777658621722017015 300200557166487932583025523)
      ·
        refine ⟨450300835749731898874538285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300200557166487932583025523 450300835749731898874538285)
        ·
          refine ⟨168862813406149462077951857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450300835749731898874538285 168862813406149462077951857)
          ·
            refine ⟨126647110054612096558463893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168862813406149462077951857 126647110054612096558463893)
            ·
              refine ⟨5936583283809942026177995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126647110054612096558463893 5936583283809942026177995)
              ·
                refine ⟨8904874925714913039266993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936583283809942026177995 8904874925714913039266993)
                ·
                  refine ⟨6678656194286184779450245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8904874925714913039266993 6678656194286184779450245)
                  ·
                    refine ⟨1252248036428659646146921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678656194286184779450245 1252248036428659646146921)
                    ·
                      rfl

theorem cell23_7316233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 4].length) (baseStart_7316233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316233 prefixEnd_7316233 := by exact prefixLift 7316233
  have htrace : WordTrace (prefixWord ++ tailWord_7316233) baseStart_7316233 baseEnd_7316233 := by
    simpa [prefixWord, tailWord_7316233, baseEnd_7316233] using wordTrace_append hprefix tailTrace_7316233
  have hstable : (prefixWord ++ tailWord_7316233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316233).length < 2 ^ (prefixWord ++ tailWord_7316233).sum := by decide
  have hdescent : baseEnd_7316233 < baseStart_7316233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316256 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7316256 : Nat := 118140960795 + 7316256 * 2 ^ 59
def prefixEnd_7316256 : Nat := 4983230072969 + 3 ^ 40 * 7316256 * 2
def baseEnd_7316256 : Nat := 3756755919341032348453157

theorem tailTrace_7316256 : CollatzResearch.WordTrace tailWord_7316256 prefixEnd_7316256 3756755919341032348453157 := by
  unfold tailWord_7316256
  simp only [CollatzResearch.WordTrace]
  refine ⟨133422889291230751945388311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177897185721641002593851081 133422889291230751945388311)
  ·
    refine ⟨200134333936846127918082467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133422889291230751945388311 200134333936846127918082467)
    ·
      refine ⟨300201500905269191877123701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200134333936846127918082467 300201500905269191877123701)
      ·
        refine ⟨28143890709868986738480347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300201500905269191877123701 28143890709868986738480347)
        ·
          refine ⟨42215836064803480107720521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28143890709868986738480347 42215836064803480107720521)
          ·
            refine ⟨31661877048602610080790391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42215836064803480107720521 31661877048602610080790391)
            ·
              refine ⟨47492815572903915121185587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31661877048602610080790391 47492815572903915121185587)
              ·
                refine ⟨71239223359355872681778381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47492815572903915121185587 71239223359355872681778381)
                ·
                  refine ⟨26714708759758452255666893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71239223359355872681778381 26714708759758452255666893)
                  ·
                    refine ⟨10018015784909419595875085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26714708759758452255666893 10018015784909419595875085)
                    ·
                      refine ⟨3756755919341032348453157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10018015784909419595875085 3756755919341032348453157)
                      ·
                        rfl

theorem cell23_7316256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7316256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316256 prefixEnd_7316256 := by exact prefixLift 7316256
  have htrace : WordTrace (prefixWord ++ tailWord_7316256) baseStart_7316256 baseEnd_7316256 := by
    simpa [prefixWord, tailWord_7316256, baseEnd_7316256] using wordTrace_append hprefix tailTrace_7316256
  have hstable : (prefixWord ++ tailWord_7316256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316256).length < 2 ^ (prefixWord ++ tailWord_7316256).sum := by decide
  have hdescent : baseEnd_7316256 < baseStart_7316256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316260 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_7316260 : Nat := 118140960795 + 7316260 * 2 ^ 59
def prefixEnd_7316260 : Nat := 4983230072969 + 3 ^ 40 * 7316260 * 2
def baseEnd_7316260 : Nat := 3756757973263650332803139

theorem tailTrace_7316260 : CollatzResearch.WordTrace tailWord_7316260 prefixEnd_7316260 3756757973263650332803139 := by
  unfold tailWord_7316260
  simp only [CollatzResearch.WordTrace]
  refine ⟨133422962237223506286961117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177897282982964675049281489 133422962237223506286961117)
  ·
    refine ⟨50033610838958814857610419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133422962237223506286961117 50033610838958814857610419)
    ·
      refine ⟨75050416258438222286415629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50033610838958814857610419 75050416258438222286415629)
      ·
        refine ⟨28143906096914333357405861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75050416258438222286415629 28143906096914333357405861)
        ·
          refine ⟨5276982393171437504513599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28143906096914333357405861 5276982393171437504513599)
          ·
            refine ⟨7915473589757156256770399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276982393171437504513599 7915473589757156256770399)
            ·
              refine ⟨11873210384635734385155599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915473589757156256770399 11873210384635734385155599)
              ·
                refine ⟨17809815576953601577733399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873210384635734385155599 17809815576953601577733399)
                ·
                  refine ⟨26714723365430402366600099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17809815576953601577733399 26714723365430402366600099)
                  ·
                    refine ⟨40072085048145603549900149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26714723365430402366600099 40072085048145603549900149)
                    ·
                      refine ⟨3756757973263650332803139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40072085048145603549900149 3756757973263650332803139)
                      ·
                        rfl

theorem cell23_7316260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_7316260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316260 prefixEnd_7316260 := by exact prefixLift 7316260
  have htrace : WordTrace (prefixWord ++ tailWord_7316260) baseStart_7316260 baseEnd_7316260 := by
    simpa [prefixWord, tailWord_7316260, baseEnd_7316260] using wordTrace_append hprefix tailTrace_7316260
  have hstable : (prefixWord ++ tailWord_7316260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316260).length < 2 ^ (prefixWord ++ tailWord_7316260).sum := by decide
  have hdescent : baseEnd_7316260 < baseStart_7316260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316279 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_7316279 : Nat := 118140960795 + 7316279 * 2 ^ 59
def prefixEnd_7316279 : Nat := 4983230072969 + 3 ^ 40 * 7316279 * 2
def baseEnd_7316279 : Nat := 3756767729396085758465551

theorem tailTrace_7316279 : CollatzResearch.WordTrace tailWord_7316279 prefixEnd_7316279 3756767729396085758465551 := by
  unfold tailWord_7316279
  simp only [CollatzResearch.WordTrace]
  refine ⟨266846617461378178818863891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177897744974252119212575927 266846617461378178818863891)
  ·
    refine ⟨400269926192067268228295837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266846617461378178818863891 400269926192067268228295837)
    ·
      refine ⟨150101222322025225585610939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400269926192067268228295837 150101222322025225585610939)
      ·
        refine ⟨225151833483037838378416409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150101222322025225585610939 225151833483037838378416409)
        ·
          refine ⟨168863875112278378783812307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225151833483037838378416409 168863875112278378783812307)
          ·
            refine ⟨253295812668417568175718461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168863875112278378783812307 253295812668417568175718461)
            ·
              refine ⟨94985929750656588065894423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253295812668417568175718461 94985929750656588065894423)
              ·
                refine ⟨142478894625984882098841635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94985929750656588065894423 142478894625984882098841635)
                ·
                  refine ⟨213718341938977323148262453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142478894625984882098841635 213718341938977323148262453)
                  ·
                    refine ⟨20036094556779124045149605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 213718341938977323148262453 20036094556779124045149605)
                    ·
                      refine ⟨3756767729396085758465551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20036094556779124045149605 3756767729396085758465551)
                      ·
                        rfl

theorem cell23_7316279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_7316279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316279 prefixEnd_7316279 := by exact prefixLift 7316279
  have htrace : WordTrace (prefixWord ++ tailWord_7316279) baseStart_7316279 baseEnd_7316279 := by
    simpa [prefixWord, tailWord_7316279, baseEnd_7316279] using wordTrace_append hprefix tailTrace_7316279
  have hstable : (prefixWord ++ tailWord_7316279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316279).length < 2 ^ (prefixWord ++ tailWord_7316279).sum := by decide
  have hdescent : baseEnd_7316279 < baseStart_7316279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316313 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 1, 4, 2]
def baseStart_7316313 : Nat := 118140960795 + 7316313 * 2 ^ 59
def prefixEnd_7316313 : Nat := 4983230072969 + 3 ^ 40 * 7316313 * 2
def baseEnd_7316313 : Nat := 3756785187738338625440395

theorem tailTrace_7316313 : CollatzResearch.WordTrace tailWord_7316313 prefixEnd_7316313 3756785187738338625440395 := by
  unfold tailWord_7316313
  simp only [CollatzResearch.WordTrace]
  refine ⟨266847857543255002625601593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177898571695503335083734395 266847857543255002625601593)
  ·
    refine ⟨200135893157441251969201195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266847857543255002625601593 200135893157441251969201195)
    ·
      refine ⟨300203839736161877953801793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200135893157441251969201195 300203839736161877953801793)
      ·
        refine ⟨225152879802121408465351345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300203839736161877953801793 225152879802121408465351345)
        ·
          refine ⟨168864659851591056349013509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225152879802121408465351345 168864659851591056349013509)
          ·
            refine ⟨31662123722173323065440033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168864659851591056349013509 31662123722173323065440033)
            ·
              refine ⟨23746592791629992299080025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31662123722173323065440033 23746592791629992299080025)
              ·
                refine ⟨17809944593722494224310019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23746592791629992299080025 17809944593722494224310019)
                ·
                  refine ⟨26714916890583741336465029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17809944593722494224310019 26714916890583741336465029)
                  ·
                    refine ⟨5009046916984451500587193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26714916890583741336465029 5009046916984451500587193)
                    ·
                      refine ⟨3756785187738338625440395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009046916984451500587193 3756785187738338625440395)
                      ·
                        rfl

theorem cell23_7316313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_7316313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316313 prefixEnd_7316313 := by exact prefixLift 7316313
  have htrace : WordTrace (prefixWord ++ tailWord_7316313) baseStart_7316313 baseEnd_7316313 := by
    simpa [prefixWord, tailWord_7316313, baseEnd_7316313] using wordTrace_append hprefix tailTrace_7316313
  have hstable : (prefixWord ++ tailWord_7316313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316313).length < 2 ^ (prefixWord ++ tailWord_7316313).sum := by decide
  have hdescent : baseEnd_7316313 < baseStart_7316313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316319 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 9]
def baseStart_7316319 : Nat := 118140960795 + 7316319 * 2 ^ 59
def prefixEnd_7316319 : Nat := 4983230072969 + 3 ^ 40 * 7316319 * 2
def baseEnd_7316319 : Nat := 417420918735807289107263

theorem tailTrace_7316319 : CollatzResearch.WordTrace tailWord_7316319 prefixEnd_7316319 417420918735807289107263 := by
  unfold tailWord_7316319
  simp only [CollatzResearch.WordTrace]
  refine ⟨266848076381233265650320011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177898717587488843766880007 266848076381233265650320011)
  ·
    refine ⟨400272114571849898475480017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266848076381233265650320011 400272114571849898475480017)
    ·
      refine ⟨300204085928887423856610013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400272114571849898475480017 300204085928887423856610013)
      ·
        refine ⟨112576532223332783946228755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300204085928887423856610013 112576532223332783946228755)
        ·
          refine ⟨168864798334999175919343133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112576532223332783946228755 168864798334999175919343133)
          ·
            refine ⟨63324299375624690969753675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168864798334999175919343133 63324299375624690969753675)
            ·
              refine ⟨94986449063437036454630513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63324299375624690969753675 94986449063437036454630513)
              ·
                refine ⟨71239836797577777340972885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94986449063437036454630513 71239836797577777340972885)
                ·
                  refine ⟨417420918735807289107263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71239836797577777340972885 417420918735807289107263)
                  ·
                    rfl

theorem cell23_7316319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 9].length) (baseStart_7316319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316319 prefixEnd_7316319 := by exact prefixLift 7316319
  have htrace : WordTrace (prefixWord ++ tailWord_7316319) baseStart_7316319 baseEnd_7316319 := by
    simpa [prefixWord, tailWord_7316319, baseEnd_7316319] using wordTrace_append hprefix tailTrace_7316319
  have hstable : (prefixWord ++ tailWord_7316319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316319).length < 2 ^ (prefixWord ++ tailWord_7316319).sum := by decide
  have hdescent : baseEnd_7316319 < baseStart_7316319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316383 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 2, 5]
def baseStart_7316383 : Nat := 118140960795 + 7316383 * 2 ^ 59
def prefixEnd_7316383 : Nat := 4983230072969 + 3 ^ 40 * 7316383 * 2
def baseEnd_7316383 : Nat := 1252273710461384450521691

theorem tailTrace_7316383 : CollatzResearch.WordTrace tailWord_7316383 prefixEnd_7316383 1252273710461384450521691 := by
  unfold tailWord_7316383
  simp only [CollatzResearch.WordTrace]
  refine ⟨266850410653001404580649803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177900273768667603053766535 266850410653001404580649803)
  ·
    refine ⟨400275615979502106870974705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266850410653001404580649803 400275615979502106870974705)
    ·
      refine ⟨300206711984626580153231029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400275615979502106870974705 300206711984626580153231029)
      ·
        refine ⟨28144379248558741889365409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300206711984626580153231029 28144379248558741889365409)
        ·
          refine ⟨21108284436419056417024057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28144379248558741889365409 21108284436419056417024057)
          ·
            refine ⟨15831213327314292312768043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21108284436419056417024057 15831213327314292312768043)
            ·
              refine ⟨23746819990971438469152065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831213327314292312768043 23746819990971438469152065)
              ·
                refine ⟨17810114993228578851864049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23746819990971438469152065 17810114993228578851864049)
                ·
                  refine ⟨13357586244921434138898037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17810114993228578851864049 13357586244921434138898037)
                  ·
                    refine ⟨1252273710461384450521691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13357586244921434138898037 1252273710461384450521691)
                    ·
                      rfl

theorem cell23_7316383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_7316383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316383 prefixEnd_7316383 := by exact prefixLift 7316383
  have htrace : WordTrace (prefixWord ++ tailWord_7316383) baseStart_7316383 baseEnd_7316383 := by
    simpa [prefixWord, tailWord_7316383, baseEnd_7316383] using wordTrace_append hprefix tailTrace_7316383
  have hstable : (prefixWord ++ tailWord_7316383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316383).length < 2 ^ (prefixWord ++ tailWord_7316383).sum := by decide
  have hdescent : baseEnd_7316383 < baseStart_7316383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316423 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_7316423 : Nat := 118140960795 + 7316423 * 2 ^ 59
def prefixEnd_7316423 : Nat := 4983230072969 + 3 ^ 40 * 7316423 * 2
def baseEnd_7316423 : Nat := 3756841670610333195064889

theorem tailTrace_7316423 : CollatzResearch.WordTrace tailWord_7316423 prefixEnd_7316423 3756841670610333195064889 := by
  unfold tailWord_7316423
  simp only [CollatzResearch.WordTrace]
  refine ⟨266851869572856491412105923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177901246381904327608070615 266851869572856491412105923)
  ·
    refine ⟨400277804359284737118158885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266851869572856491412105923 400277804359284737118158885)
    ·
      refine ⟨75052088317365888209654791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400277804359284737118158885 75052088317365888209654791)
      ·
        refine ⟨112578132476048832314482187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75052088317365888209654791 112578132476048832314482187)
        ·
          refine ⟨168867198714073248471723281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112578132476048832314482187 168867198714073248471723281)
          ·
            refine ⟨126650399035554936353792461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168867198714073248471723281 126650399035554936353792461)
            ·
              refine ⟨47493899638333101132672173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126650399035554936353792461 47493899638333101132672173)
              ·
                refine ⟨17810212364374912924752065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47493899638333101132672173 17810212364374912924752065)
                ·
                  refine ⟨13357659273281184693564049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17810212364374912924752065 13357659273281184693564049)
                  ·
                    refine ⟨10018244454960888520173037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13357659273281184693564049 10018244454960888520173037)
                    ·
                      refine ⟨3756841670610333195064889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10018244454960888520173037 3756841670610333195064889)
                      ·
                        rfl

theorem cell23_7316423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_7316423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316423 prefixEnd_7316423 := by exact prefixLift 7316423
  have htrace : WordTrace (prefixWord ++ tailWord_7316423) baseStart_7316423 baseEnd_7316423 := by
    simpa [prefixWord, tailWord_7316423, baseEnd_7316423] using wordTrace_append hprefix tailTrace_7316423
  have hstable : (prefixWord ++ tailWord_7316423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316423).length < 2 ^ (prefixWord ++ tailWord_7316423).sum := by decide
  have hdescent : baseEnd_7316423 < baseStart_7316423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316447 : List Nat := [1, 1, 2, 3, 5, 1, 1, 4, 1, 4]
def baseStart_7316447 : Nat := 118140960795 + 7316447 * 2 ^ 59
def prefixEnd_7316447 : Nat := 4983230072969 + 3 ^ 40 * 7316447 * 2
def baseEnd_7316447 : Nat := 1252284664715347033721593

theorem tailTrace_7316447 : CollatzResearch.WordTrace tailWord_7316447 prefixEnd_7316447 1252284664715347033721593 := by
  unfold tailWord_7316447
  simp only [CollatzResearch.WordTrace]
  refine ⟨266852744924769543510979595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177901829949846362340653063 266852744924769543510979595)
  ·
    refine ⟨400279117387154315266469393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266852744924769543510979595 400279117387154315266469393)
    ·
      refine ⟨300209338040365736449852045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400279117387154315266469393 300209338040365736449852045)
      ·
        refine ⟨112578501765137151168694517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300209338040365736449852045 112578501765137151168694517)
        ·
          refine ⟨10554234540481607922065111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112578501765137151168694517 10554234540481607922065111)
          ·
            refine ⟨15831351810722411883097667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10554234540481607922065111 15831351810722411883097667)
            ·
              refine ⟨23747027716083617824646501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831351810722411883097667 23747027716083617824646501)
              ·
                refine ⟨4452567696765678342121219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23747027716083617824646501 4452567696765678342121219)
                ·
                  refine ⟨6678851545148517513181829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452567696765678342121219 6678851545148517513181829)
                  ·
                    refine ⟨1252284664715347033721593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678851545148517513181829 1252284664715347033721593)
                    ·
                      rfl

theorem cell23_7316447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 4].length) (baseStart_7316447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316447 prefixEnd_7316447 := by exact prefixLift 7316447
  have htrace : WordTrace (prefixWord ++ tailWord_7316447) baseStart_7316447 baseEnd_7316447 := by
    simpa [prefixWord, tailWord_7316447, baseEnd_7316447] using wordTrace_append hprefix tailTrace_7316447
  have hstable : (prefixWord ++ tailWord_7316447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316447).length < 2 ^ (prefixWord ++ tailWord_7316447).sum := by decide
  have hdescent : baseEnd_7316447 < baseStart_7316447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316468 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7316468 : Nat := 118140960795 + 7316468 * 2 ^ 59
def prefixEnd_7316468 : Nat := 4983230072969 + 3 ^ 40 * 7316468 * 2
def baseEnd_7316468 : Nat := 1252288259079928506334061

theorem tailTrace_7316468 : CollatzResearch.WordTrace tailWord_7316468 prefixEnd_7316468 1252288259079928506334061 := by
  unfold tailWord_7316468
  simp only [CollatzResearch.WordTrace]
  refine ⟨133426755428846732048747029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177902340571795642731662705 133426755428846732048747029)
  ·
    refine ⟨6254379160727190564785017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133426755428846732048747029 6254379160727190564785017)
    ·
      refine ⟨4690784370545392923588763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6254379160727190564785017 4690784370545392923588763)
      ·
        refine ⟨7036176555818089385383145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690784370545392923588763 7036176555818089385383145)
        ·
          refine ⟨5277132416863567039037359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7036176555818089385383145 5277132416863567039037359)
          ·
            refine ⟨7915698625295350558556039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277132416863567039037359 7915698625295350558556039)
            ·
              refine ⟨11873547937943025837834059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915698625295350558556039 11873547937943025837834059)
              ·
                refine ⟨17810321906914538756751089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873547937943025837834059 17810321906914538756751089)
                ·
                  refine ⟨13357741430185904067563317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17810321906914538756751089 13357741430185904067563317)
                  ·
                    refine ⟨1252288259079928506334061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13357741430185904067563317 1252288259079928506334061)
                    ·
                      rfl

theorem cell23_7316468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7316468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316468 prefixEnd_7316468 := by exact prefixLift 7316468
  have htrace : WordTrace (prefixWord ++ tailWord_7316468) baseStart_7316468 baseEnd_7316468 := by
    simpa [prefixWord, tailWord_7316468, baseEnd_7316468] using wordTrace_append hprefix tailTrace_7316468
  have hstable : (prefixWord ++ tailWord_7316468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316468).length < 2 ^ (prefixWord ++ tailWord_7316468).sum := by decide
  have hdescent : baseEnd_7316468 < baseStart_7316468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316473 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 1, 5]
def baseStart_7316473 : Nat := 118140960795 + 7316473 * 2 ^ 59
def prefixEnd_7316473 : Nat := 4983230072969 + 3 ^ 40 * 7316473 * 2
def baseEnd_7316473 : Nat := 1252289114881019333146553

theorem tailTrace_7316473 : CollatzResearch.WordTrace tailWord_7316473 prefixEnd_7316473 1252289114881019333146553 := by
  unfold tailWord_7316473
  simp only [CollatzResearch.WordTrace]
  refine ⟨266853693222675349951426073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177902462148450233300950715 266853693222675349951426073)
  ·
    refine ⟨200140269917006512463569555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266853693222675349951426073 200140269917006512463569555)
    ·
      refine ⟨300210404875509768695354333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200140269917006512463569555 300210404875509768695354333)
      ·
        refine ⟨112578901828316163260757875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300210404875509768695354333 112578901828316163260757875)
        ·
          refine ⟨168868352742474244891136813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112578901828316163260757875 168868352742474244891136813)
          ·
            refine ⟨63325632278427841834176305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168868352742474244891136813 63325632278427841834176305)
            ·
              refine ⟨47494224208820881375632229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63325632278427841834176305 47494224208820881375632229)
              ·
                refine ⟨8905167039153915257931043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47494224208820881375632229 8905167039153915257931043)
                ·
                  refine ⟨13357750558730872886896565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8905167039153915257931043 13357750558730872886896565)
                  ·
                    refine ⟨1252289114881019333146553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13357750558730872886896565 1252289114881019333146553)
                    ·
                      rfl

theorem cell23_7316473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_7316473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316473 prefixEnd_7316473 := by exact prefixLift 7316473
  have htrace : WordTrace (prefixWord ++ tailWord_7316473) baseStart_7316473 baseEnd_7316473 := by
    simpa [prefixWord, tailWord_7316473, baseEnd_7316473] using wordTrace_append hprefix tailTrace_7316473
  have hstable : (prefixWord ++ tailWord_7316473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316473).length < 2 ^ (prefixWord ++ tailWord_7316473).sum := by decide
  have hdescent : baseEnd_7316473 < baseStart_7316473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316490 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_7316490 : Nat := 118140960795 + 7316490 * 2 ^ 59
def prefixEnd_7316490 : Nat := 4983230072969 + 3 ^ 40 * 7316490 * 2
def baseEnd_7316490 : Nat := 1252292024604728144309027

theorem tailTrace_7316490 : CollatzResearch.WordTrace tailWord_7316490 prefixEnd_7316490 1252292024604728144309027 := by
  unfold tailWord_7316490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66713578315903440463698731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177902875509075841236529949 66713578315903440463698731)
  ·
    refine ⟨100070367473855160695548097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66713578315903440463698731 100070367473855160695548097)
    ·
      refine ⟨75052775605391370521661073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100070367473855160695548097 75052775605391370521661073)
      ·
        refine ⟨56289581704043527891245805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75052775605391370521661073 56289581704043527891245805)
        ·
          refine ⟨21108593139016322959217177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56289581704043527891245805 21108593139016322959217177)
          ·
            refine ⟨15831444854262242219412883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21108593139016322959217177 15831444854262242219412883)
            ·
              refine ⟨23747167281393363329119325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831444854262242219412883 23747167281393363329119325)
              ·
                refine ⟨8905187730522511248419747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23747167281393363329119325 8905187730522511248419747)
                ·
                  refine ⟨13357781595783766872629621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8905187730522511248419747 13357781595783766872629621)
                  ·
                    refine ⟨1252292024604728144309027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13357781595783766872629621 1252292024604728144309027)
                    ·
                      rfl

theorem cell23_7316490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_7316490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316490 prefixEnd_7316490 := by exact prefixLift 7316490
  have htrace : WordTrace (prefixWord ++ tailWord_7316490) baseStart_7316490 baseEnd_7316490 := by
    simpa [prefixWord, tailWord_7316490, baseEnd_7316490] using wordTrace_append hprefix tailTrace_7316490
  have hstable : (prefixWord ++ tailWord_7316490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316490).length < 2 ^ (prefixWord ++ tailWord_7316490).sum := by decide
  have hdescent : baseEnd_7316490 < baseStart_7316490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316513 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7316513 : Nat := 118140960795 + 7316513 * 2 ^ 59
def prefixEnd_7316513 : Nat := 4983230072969 + 3 ^ 40 * 7316513 * 2
def baseEnd_7316513 : Nat := 3756887883869237842939475

theorem tailTrace_7316513 : CollatzResearch.WordTrace tailWord_7316513 prefixEnd_7316513 3756887883869237842939475 := by
  unfold tailWord_7316513
  simp only [CollatzResearch.WordTrace]
  refine ⟨266855152142530436782882193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177903434761686957855254795 266855152142530436782882193)
  ·
    refine ⟨200141364106897827587161645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266855152142530436782882193 200141364106897827587161645)
    ·
      refine ⟨75053011540086685345185617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200141364106897827587161645 75053011540086685345185617)
      ·
        refine ⟨56289758655065014008889213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75053011540086685345185617 56289758655065014008889213)
        ·
          refine ⟨21108659495649380253333455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56289758655065014008889213 21108659495649380253333455)
          ·
            refine ⟨31662989243474070380000183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21108659495649380253333455 31662989243474070380000183)
            ·
              refine ⟨47494483865211105570000275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31662989243474070380000183 47494483865211105570000275)
              ·
                refine ⟨71241725797816658355000413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47494483865211105570000275 71241725797816658355000413)
                ·
                  refine ⟨26715647174181246883125155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71241725797816658355000413 26715647174181246883125155)
                  ·
                    refine ⟨40073470761271870324687733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26715647174181246883125155 40073470761271870324687733)
                    ·
                      refine ⟨3756887883869237842939475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40073470761271870324687733 3756887883869237842939475)
                      ·
                        rfl

theorem cell23_7316513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7316513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316513 prefixEnd_7316513 := by exact prefixLift 7316513
  have htrace : WordTrace (prefixWord ++ tailWord_7316513) baseStart_7316513 baseEnd_7316513 := by
    simpa [prefixWord, tailWord_7316513, baseEnd_7316513] using wordTrace_append hprefix tailTrace_7316513
  have hstable : (prefixWord ++ tailWord_7316513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316513).length < 2 ^ (prefixWord ++ tailWord_7316513).sum := by decide
  have hdescent : baseEnd_7316513 < baseStart_7316513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316543 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 3]
def baseStart_7316543 : Nat := 118140960795 + 7316543 * 2 ^ 59
def prefixEnd_7316543 : Nat := 4983230072969 + 3 ^ 40 * 7316543 * 2
def baseEnd_7316543 : Nat := 3756903288288872725564337

theorem tailTrace_7316543 : CollatzResearch.WordTrace tailWord_7316543 prefixEnd_7316543 3756903288288872725564337 := by
  unfold tailWord_7316543
  simp only [CollatzResearch.WordTrace]
  refine ⟨266856246332421751906474283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177904164221614501270982855 266856246332421751906474283)
  ·
    refine ⟨400284369498632627859711425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266856246332421751906474283 400284369498632627859711425)
    ·
      refine ⟨300213277123974470894783569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400284369498632627859711425 300213277123974470894783569)
      ·
        refine ⟨225159957842980853171087677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300213277123974470894783569 225159957842980853171087677)
        ·
          refine ⟨84434984191117819939157879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225159957842980853171087677 84434984191117819939157879)
          ·
            refine ⟨126652476286676729908736819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84434984191117819939157879 126652476286676729908736819)
            ·
              refine ⟨189978714430015094863105229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126652476286676729908736819 189978714430015094863105229)
              ·
                refine ⟨71242017911255660573664461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189978714430015094863105229 71242017911255660573664461)
                ·
                  refine ⟨26715756716720872715124173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71242017911255660573664461 26715756716720872715124173)
                  ·
                    refine ⟨10018408768770327268171565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26715756716720872715124173 10018408768770327268171565)
                    ·
                      refine ⟨3756903288288872725564337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10018408768770327268171565 3756903288288872725564337)
                      ·
                        rfl

theorem cell23_7316543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_7316543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316543 prefixEnd_7316543 := by exact prefixLift 7316543
  have htrace : WordTrace (prefixWord ++ tailWord_7316543) baseStart_7316543 baseEnd_7316543 := by
    simpa [prefixWord, tailWord_7316543, baseEnd_7316543] using wordTrace_append hprefix tailTrace_7316543
  have hstable : (prefixWord ++ tailWord_7316543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316543).length < 2 ^ (prefixWord ++ tailWord_7316543).sum := by decide
  have hdescent : baseEnd_7316543 < baseStart_7316543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316550 : List Nat := [6, 1, 1, 1, 1, 2, 11]
def baseStart_7316550 : Nat := 118140960795 + 7316550 * 2 ^ 59
def prefixEnd_7316550 : Nat := 4983230072969 + 3 ^ 40 * 7316550 * 2
def baseEnd_7316550 : Nat := 46381566452511780224405

theorem tailTrace_7316550 : CollatzResearch.WordTrace tailWord_7316550 prefixEnd_7316550 46381566452511780224405 := by
  unfold tailWord_7316550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339265676356137253186847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177904334428930928067986069 8339265676356137253186847)
  ·
    refine ⟨12508898514534205879780271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8339265676356137253186847 12508898514534205879780271)
    ·
      refine ⟨18763347771801308819670407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12508898514534205879780271 18763347771801308819670407)
      ·
        refine ⟨28145021657701963229505611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18763347771801308819670407 28145021657701963229505611)
        ·
          refine ⟨42217532486552944844258417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28145021657701963229505611 42217532486552944844258417)
          ·
            refine ⟨31663149364914708633193813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42217532486552944844258417 31663149364914708633193813)
            ·
              refine ⟨46381566452511780224405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31663149364914708633193813 46381566452511780224405)
              ·
                rfl

theorem cell23_7316550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 11].length) (baseStart_7316550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316550 prefixEnd_7316550 := by exact prefixLift 7316550
  have htrace : WordTrace (prefixWord ++ tailWord_7316550) baseStart_7316550 baseEnd_7316550 := by
    simpa [prefixWord, tailWord_7316550, baseEnd_7316550] using wordTrace_append hprefix tailTrace_7316550
  have hstable : (prefixWord ++ tailWord_7316550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316550).length < 2 ^ (prefixWord ++ tailWord_7316550).sum := by decide
  have hdescent : baseEnd_7316550 < baseStart_7316550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316600 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 3, 4, 2]
def baseStart_7316600 : Nat := 118140960795 + 7316600 * 2 ^ 59
def prefixEnd_7316600 : Nat := 4983230072969 + 3 ^ 40 * 7316600 * 2
def baseEnd_7316600 : Nat := 3756932556686179002551575

theorem tailTrace_7316600 : CollatzResearch.WordTrace tailWord_7316600 prefixEnd_7316600 3756932556686179002551575 := by
  unfold tailWord_7316600
  simp only [CollatzResearch.WordTrace]
  refine ⟨133429162646607625320649627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177905550195476833760866169 133429162646607625320649627)
  ·
    refine ⟨200143743969911437980974441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133429162646607625320649627 200143743969911437980974441)
    ·
      refine ⟨150107807977433578485730831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200143743969911437980974441 150107807977433578485730831)
      ·
        refine ⟨225161711966150367728596247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150107807977433578485730831 225161711966150367728596247)
        ·
          refine ⟨337742567949225551592894371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225161711966150367728596247 337742567949225551592894371)
          ·
            refine ⟨506613851923838327389341557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337742567949225551592894371 506613851923838327389341557)
            ·
              refine ⟨47495048617859843192750771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506613851923838327389341557 47495048617859843192750771)
              ·
                refine ⟨71242572926789764789126157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47495048617859843192750771 71242572926789764789126157)
                ·
                  refine ⟨26715964847546161795922309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71242572926789764789126157 26715964847546161795922309)
                  ·
                    refine ⟨5009243408914905336735433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26715964847546161795922309 5009243408914905336735433)
                    ·
                      refine ⟨3756932556686179002551575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009243408914905336735433 3756932556686179002551575)
                      ·
                        rfl

theorem cell23_7316600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_7316600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316600 prefixEnd_7316600 := by exact prefixLift 7316600
  have htrace : WordTrace (prefixWord ++ tailWord_7316600) baseStart_7316600 baseEnd_7316600 := by
    simpa [prefixWord, tailWord_7316600, baseEnd_7316600] using wordTrace_append hprefix tailTrace_7316600
  have hstable : (prefixWord ++ tailWord_7316600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316600).length < 2 ^ (prefixWord ++ tailWord_7316600).sum := by decide
  have hdescent : baseEnd_7316600 < baseStart_7316600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316603 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 3]
def baseStart_7316603 : Nat := 118140960795 + 7316603 * 2 ^ 59
def prefixEnd_7316603 : Nat := 4983230072969 + 3 ^ 40 * 7316603 * 2
def baseEnd_7316603 : Nat := 3756934097128142490814061

theorem tailTrace_7316603 : CollatzResearch.WordTrace tailWord_7316603 prefixEnd_7316603 3756934097128142490814061 := by
  unfold tailWord_7316603
  simp only [CollatzResearch.WordTrace]
  refine ⟨266858434712204382153658463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177905623141469588102438975 266858434712204382153658463)
  ·
    refine ⟨400287652068306573230487695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266858434712204382153658463 400287652068306573230487695)
    ·
      refine ⟨600431478102459859845731543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400287652068306573230487695 600431478102459859845731543)
      ·
        refine ⟨900647217153689789768597315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600431478102459859845731543 900647217153689789768597315)
        ·
          refine ⟨1350970825730534684652895973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900647217153689789768597315 1350970825730534684652895973)
          ·
            refine ⟨253307029824475253372417995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1350970825730534684652895973 253307029824475253372417995)
            ·
              refine ⟨379960544736712880058626993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253307029824475253372417995 379960544736712880058626993)
              ·
                refine ⟨284970408552534660043970245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379960544736712880058626993 284970408552534660043970245)
                ·
                  refine ⟨53431951603600248758244421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284970408552534660043970245 53431951603600248758244421)
                  ·
                    refine ⟨10018490925675046642170829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53431951603600248758244421 10018490925675046642170829)
                    ·
                      refine ⟨3756934097128142490814061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10018490925675046642170829 3756934097128142490814061)
                      ·
                        rfl

theorem cell23_7316603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 3].length) (baseStart_7316603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316603 prefixEnd_7316603 := by exact prefixLift 7316603
  have htrace : WordTrace (prefixWord ++ tailWord_7316603) baseStart_7316603 baseEnd_7316603 := by
    simpa [prefixWord, tailWord_7316603, baseEnd_7316603] using wordTrace_append hprefix tailTrace_7316603
  have hstable : (prefixWord ++ tailWord_7316603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316603).length < 2 ^ (prefixWord ++ tailWord_7316603).sum := by decide
  have hdescent : baseEnd_7316603 < baseStart_7316603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316604 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_7316604 : Nat := 118140960795 + 7316604 * 2 ^ 59
def prefixEnd_7316604 : Nat := 4983230072969 + 3 ^ 40 * 7316604 * 2
def baseEnd_7316604 : Nat := 3756934610608796986901557

theorem tailTrace_7316604 : CollatzResearch.WordTrace tailWord_7316604 prefixEnd_7316604 3756934610608796986901557 := by
  unfold tailWord_7316604
  simp only [CollatzResearch.WordTrace]
  refine ⟨133429235592600379662222433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177905647456800506216296577 133429235592600379662222433)
  ·
    refine ⟨100071926694450284746666825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133429235592600379662222433 100071926694450284746666825)
    ·
      refine ⟨75053945020837713560000119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100071926694450284746666825 75053945020837713560000119)
      ·
        refine ⟨112580917531256570340000179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75053945020837713560000119 112580917531256570340000179)
        ·
          refine ⟨168871376296884855510000269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112580917531256570340000179 168871376296884855510000269)
          ·
            refine ⟨63326766111331820816250101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168871376296884855510000269 63326766111331820816250101)
            ·
              refine ⟨5936884322937358201523447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63326766111331820816250101 5936884322937358201523447)
              ·
                refine ⟨8905326484406037302285171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936884322937358201523447 8905326484406037302285171)
                ·
                  refine ⟨13357989726609055953427757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8905326484406037302285171 13357989726609055953427757)
                  ·
                    refine ⟨5009246147478395982535409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13357989726609055953427757 5009246147478395982535409)
                    ·
                      refine ⟨3756934610608796986901557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009246147478395982535409 3756934610608796986901557)
                      ·
                        rfl

theorem cell23_7316604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_7316604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316604 prefixEnd_7316604 := by exact prefixLift 7316604
  have htrace : WordTrace (prefixWord ++ tailWord_7316604) baseStart_7316604 baseEnd_7316604 := by
    simpa [prefixWord, tailWord_7316604, baseEnd_7316604] using wordTrace_append hprefix tailTrace_7316604
  have hstable : (prefixWord ++ tailWord_7316604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316604).length < 2 ^ (prefixWord ++ tailWord_7316604).sum := by decide
  have hdescent : baseEnd_7316604 < baseStart_7316604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316634 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7316634 : Nat := 118140960795 + 7316634 * 2 ^ 59
def prefixEnd_7316634 : Nat := 4983230072969 + 3 ^ 40 * 7316634 * 2
def baseEnd_7316634 : Nat := 3756950015028431869526419

theorem tailTrace_7316634 : CollatzResearch.WordTrace tailWord_7316634 prefixEnd_7316634 3756950015028431869526419 := by
  unfold tailWord_7316634
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714891343773018612009239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177906376916728049632024637 66714891343773018612009239)
  ·
    refine ⟨100072337015659527918013859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66714891343773018612009239 100072337015659527918013859)
    ·
      refine ⟨150108505523489291877020789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100072337015659527918013859 150108505523489291877020789)
      ·
        refine ⟨14072672392827121113470699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150108505523489291877020789 14072672392827121113470699)
        ·
          refine ⟨21109008589240681670206049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14072672392827121113470699 21109008589240681670206049)
          ·
            refine ⟨15831756441930511252654537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21109008589240681670206049 15831756441930511252654537)
            ·
              refine ⟨11873817331447883439490903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15831756441930511252654537 11873817331447883439490903)
              ·
                refine ⟨17810725997171825159236355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873817331447883439490903 17810725997171825159236355)
                ·
                  refine ⟨26716088995757737738854533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17810725997171825159236355 26716088995757737738854533)
                  ·
                    refine ⟨5009266686704575826035225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26716088995757737738854533 5009266686704575826035225)
                    ·
                      refine ⟨3756950015028431869526419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009266686704575826035225 3756950015028431869526419)
                      ·
                        rfl

theorem cell23_7316634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7316634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316634 prefixEnd_7316634 := by exact prefixLift 7316634
  have htrace : WordTrace (prefixWord ++ tailWord_7316634) baseStart_7316634 baseEnd_7316634 := by
    simpa [prefixWord, tailWord_7316634, baseEnd_7316634] using wordTrace_append hprefix tailTrace_7316634
  have hstable : (prefixWord ++ tailWord_7316634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316634).length < 2 ^ (prefixWord ++ tailWord_7316634).sum := by decide
  have hdescent : baseEnd_7316634 < baseStart_7316634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316657 : List Nat := [1, 2, 2, 5, 1, 1, 1, 5, 5]
def baseStart_7316657 : Nat := 118140960795 + 7316657 * 2 ^ 59
def prefixEnd_7316657 : Nat := 4983230072969 + 3 ^ 40 * 7316657 * 2
def baseEnd_7316657 : Nat := 417440202787053919948757

theorem tailTrace_7316657 : CollatzResearch.WordTrace tailWord_7316657 prefixEnd_7316657 417440202787053919948757 := by
  unfold tailWord_7316657
  simp only [CollatzResearch.WordTrace]
  refine ⟨266860404254008749376124225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177906936169339166250749483 266860404254008749376124225)
  ·
    refine ⟨200145303190506562032093169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266860404254008749376124225 200145303190506562032093169)
    ·
      refine ⟨150108977392879921524069877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200145303190506562032093169 150108977392879921524069877)
      ·
        refine ⟨14072716630582492642881551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150108977392879921524069877 14072716630582492642881551)
        ·
          refine ⟨21109074945873738964322327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14072716630582492642881551 21109074945873738964322327)
          ·
            refine ⟨31663612418810608446483491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21109074945873738964322327 31663612418810608446483491)
            ·
              refine ⟨47495418628215912669725237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31663612418810608446483491 47495418628215912669725237)
              ·
                refine ⟨4452695496395241812786741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47495418628215912669725237 4452695496395241812786741)
                ·
                  refine ⟨417440202787053919948757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4452695496395241812786741 417440202787053919948757)
                  ·
                    rfl

theorem cell23_7316657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 5].length) (baseStart_7316657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316657 prefixEnd_7316657 := by exact prefixLift 7316657
  have htrace : WordTrace (prefixWord ++ tailWord_7316657) baseStart_7316657 baseEnd_7316657 := by
    simpa [prefixWord, tailWord_7316657, baseEnd_7316657] using wordTrace_append hprefix tailTrace_7316657
  have hstable : (prefixWord ++ tailWord_7316657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316657).length < 2 ^ (prefixWord ++ tailWord_7316657).sum := by decide
  have hdescent : baseEnd_7316657 < baseStart_7316657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316685 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_7316685 : Nat := 118140960795 + 7316685 * 2 ^ 59
def prefixEnd_7316685 : Nat := 4983230072969 + 3 ^ 40 * 7316685 * 2
def baseEnd_7316685 : Nat := 3756976202541811169988685

theorem tailTrace_7316685 : CollatzResearch.WordTrace tailWord_7316685 prefixEnd_7316685 3756976202541811169988685 := by
  unfold tailWord_7316685
  simp only [CollatzResearch.WordTrace]
  refine ⟨266861425497907310158143509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177907616998604873438762339 266861425497907310158143509)
  ·
    refine ⟨12509129320214405163662977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 266861425497907310158143509 12509129320214405163662977)
    ·
      refine ⟨9381846990160803872747233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12509129320214405163662977 9381846990160803872747233)
      ·
        refine ⟨7036385242620602904560425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9381846990160803872747233 7036385242620602904560425)
        ·
          refine ⟨5277288931965452178420319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7036385242620602904560425 5277288931965452178420319)
          ·
            refine ⟨7915933397948178267630479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277288931965452178420319 7915933397948178267630479)
            ·
              refine ⟨11873900096922267401445719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915933397948178267630479 11873900096922267401445719)
              ·
                refine ⟨17810850145383401102168579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873900096922267401445719 17810850145383401102168579)
                ·
                  refine ⟨26716275218075101653252869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17810850145383401102168579 26716275218075101653252869)
                  ·
                    refine ⟨5009301603389081559984913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26716275218075101653252869 5009301603389081559984913)
                    ·
                      refine ⟨3756976202541811169988685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5009301603389081559984913 3756976202541811169988685)
                      ·
                        rfl

theorem cell23_7316685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_7316685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316685 prefixEnd_7316685 := by exact prefixLift 7316685
  have htrace : WordTrace (prefixWord ++ tailWord_7316685) baseStart_7316685 baseEnd_7316685 := by
    simpa [prefixWord, tailWord_7316685, baseEnd_7316685] using wordTrace_append hprefix tailTrace_7316685
  have hstable : (prefixWord ++ tailWord_7316685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316685).length < 2 ^ (prefixWord ++ tailWord_7316685).sum := by decide
  have hdescent : baseEnd_7316685 < baseStart_7316685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316690 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7316690 : Nat := 118140960795 + 7316690 * 2 ^ 59
def prefixEnd_7316690 : Nat := 4983230072969 + 3 ^ 40 * 7316690 * 2
def baseEnd_7316690 : Nat := 3756978769945083650426161

theorem tailTrace_7316690 : CollatzResearch.WordTrace tailWord_7316690 prefixEnd_7316690 3756978769945083650426161 := by
  unfold tailWord_7316690
  simp only [CollatzResearch.WordTrace]
  refine ⟨66715401965722299003018881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177907738575259464008050349 66715401965722299003018881)
  ·
    refine ⟨50036551474291724252264161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66715401965722299003018881 50036551474291724252264161)
    ·
      refine ⟨37527413605718793189198121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50036551474291724252264161 37527413605718793189198121)
      ·
        refine ⟨28145560204289094891898591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37527413605718793189198121 28145560204289094891898591)
        ·
          refine ⟨42218340306433642337847887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28145560204289094891898591 42218340306433642337847887)
          ·
            refine ⟨63327510459650463506771831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42218340306433642337847887 63327510459650463506771831)
            ·
              refine ⟨94991265689475695260157747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63327510459650463506771831 94991265689475695260157747)
              ·
                refine ⟨142486898534213542890236621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94991265689475695260157747 142486898534213542890236621)
                ·
                  refine ⟨53432586950330078583838733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142486898534213542890236621 53432586950330078583838733)
                  ·
                    refine ⟨20037220106373779468939525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53432586950330078583838733 20037220106373779468939525)
                    ·
                      refine ⟨3756978769945083650426161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20037220106373779468939525 3756978769945083650426161)
                      ·
                        rfl

theorem cell23_7316690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7316690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316690 prefixEnd_7316690 := by exact prefixLift 7316690
  have htrace : WordTrace (prefixWord ++ tailWord_7316690) baseStart_7316690 baseEnd_7316690 := by
    simpa [prefixWord, tailWord_7316690, baseEnd_7316690] using wordTrace_append hprefix tailTrace_7316690
  have hstable : (prefixWord ++ tailWord_7316690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316690).length < 2 ^ (prefixWord ++ tailWord_7316690).sum := by decide
  have hdescent : baseEnd_7316690 < baseStart_7316690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316730 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 6]
def baseStart_7316730 : Nat := 118140960795 + 7316730 * 2 ^ 59
def prefixEnd_7316730 : Nat := 4983230072969 + 3 ^ 40 * 7316730 * 2
def baseEnd_7316730 : Nat := 417444367685695943769553

theorem tailTrace_7316730 : CollatzResearch.WordTrace tailWord_7316730 prefixEnd_7316730 417444367685695943769553 := by
  unfold tailWord_7316730
  simp only [CollatzResearch.WordTrace]
  refine ⟨66715766695686070710882911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177908711188496188562354429 66715766695686070710882911)
  ·
    refine ⟨100073650043529106066324367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66715766695686070710882911 100073650043529106066324367)
    ·
      refine ⟨150110475065293659099486551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100073650043529106066324367 150110475065293659099486551)
      ·
        refine ⟨225165712597940488649229827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150110475065293659099486551 225165712597940488649229827)
        ·
          refine ⟨337748568896910732973844741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225165712597940488649229827 337748568896910732973844741)
          ·
            refine ⟨63327856668170762432595889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337748568896910732973844741 63327856668170762432595889)
            ·
              refine ⟨47495892501128071824446917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63327856668170762432595889 47495892501128071824446917)
              ·
                refine ⟨8905479843961513467083797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47495892501128071824446917 8905479843961513467083797)
                ·
                  refine ⟨417444367685695943769553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8905479843961513467083797 417444367685695943769553)
                  ·
                    rfl

theorem cell23_7316730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_7316730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316730 prefixEnd_7316730 := by exact prefixLift 7316730
  have htrace : WordTrace (prefixWord ++ tailWord_7316730) baseStart_7316730 baseEnd_7316730 := by
    simpa [prefixWord, tailWord_7316730, baseEnd_7316730] using wordTrace_append hprefix tailTrace_7316730
  have hstable : (prefixWord ++ tailWord_7316730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316730).length < 2 ^ (prefixWord ++ tailWord_7316730).sum := by decide
  have hdescent : baseEnd_7316730 < baseStart_7316730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316734 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_7316734 : Nat := 118140960795 + 7316734 * 2 ^ 59
def prefixEnd_7316734 : Nat := 4983230072969 + 3 ^ 40 * 7316734 * 2
def baseEnd_7316734 : Nat := 1252333787697960492758653

theorem tailTrace_7316734 : CollatzResearch.WordTrace tailWord_7316734 prefixEnd_7316734 1252333787697960492758653 := by
  unfold tailWord_7316734
  simp only [CollatzResearch.WordTrace]
  refine ⟨33357901584341223940834657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177908808449819861017784837 33357901584341223940834657)
  ·
    refine ⟨25018426188255917955625993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33357901584341223940834657 25018426188255917955625993)
    ·
      refine ⟨18763819641191938466719495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25018426188255917955625993 18763819641191938466719495)
      ·
        refine ⟨28145729461787907700079243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18763819641191938466719495 28145729461787907700079243)
        ·
          refine ⟨42218594192681861550118865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28145729461787907700079243 42218594192681861550118865)
          ·
            refine ⟨31663945644511396162589149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42218594192681861550118865 31663945644511396162589149)
            ·
              refine ⟨11873979616691773560970931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31663945644511396162589149 11873979616691773560970931)
              ·
                refine ⟨17810969425037660341456397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873979616691773560970931 17810969425037660341456397)
                ·
                  refine ⟨6679113534389122628046149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17810969425037660341456397 6679113534389122628046149)
                  ·
                    refine ⟨1252333787697960492758653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6679113534389122628046149 1252333787697960492758653)
                    ·
                      rfl

theorem cell23_7316734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_7316734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316734 prefixEnd_7316734 := by exact prefixLift 7316734
  have htrace : WordTrace (prefixWord ++ tailWord_7316734) baseStart_7316734 baseEnd_7316734 := by
    simpa [prefixWord, tailWord_7316734, baseEnd_7316734] using wordTrace_append hprefix tailTrace_7316734
  have hstable : (prefixWord ++ tailWord_7316734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316734).length < 2 ^ (prefixWord ++ tailWord_7316734).sum := by decide
  have hdescent : baseEnd_7316734 < baseStart_7316734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316747 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 6]
def baseStart_7316747 : Nat := 118140960795 + 7316747 * 2 ^ 59
def prefixEnd_7316747 : Nat := 4983230072969 + 3 ^ 40 * 7316747 * 2
def baseEnd_7316747 : Nat := 417445337593598880823711

theorem tailTrace_7316747 : CollatzResearch.WordTrace tailWord_7316747 prefixEnd_7316747 417445337593598880823711 := by
  unfold tailWord_7316747
  simp only [CollatzResearch.WordTrace]
  refine ⟨266863686823682694746900495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177909124549121796497933663 266863686823682694746900495)
  ·
    refine ⟨400295530235524042120350743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266863686823682694746900495 400295530235524042120350743)
    ·
      refine ⟨600443295353286063180526115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400295530235524042120350743 600443295353286063180526115)
      ·
        refine ⟨900664943029929094770789173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600443295353286063180526115 900664943029929094770789173)
        ·
          refine ⟨84437338409055852634761485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 900664943029929094770789173 84437338409055852634761485)
          ·
            refine ⟨31664001903395944738035557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84437338409055852634761485 31664001903395944738035557)
            ·
              refine ⟨5937000356886739638381667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31664001903395944738035557 5937000356886739638381667)
              ·
                refine ⟨8905500535330109457572501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5937000356886739638381667 8905500535330109457572501)
                ·
                  refine ⟨417445337593598880823711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8905500535330109457572501 417445337593598880823711)
                  ·
                    rfl

theorem cell23_7316747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 6].length) (baseStart_7316747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316747 prefixEnd_7316747 := by exact prefixLift 7316747
  have htrace : WordTrace (prefixWord ++ tailWord_7316747) baseStart_7316747 baseEnd_7316747 := by
    simpa [prefixWord, tailWord_7316747, baseEnd_7316747] using wordTrace_append hprefix tailTrace_7316747
  have hstable : (prefixWord ++ tailWord_7316747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316747).length < 2 ^ (prefixWord ++ tailWord_7316747).sum := by decide
  have hdescent : baseEnd_7316747 < baseStart_7316747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316757 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_7316757 : Nat := 118140960795 + 7316757 * 2 ^ 59
def prefixEnd_7316757 : Nat := 4983230072969 + 3 ^ 40 * 7316757 * 2
def baseEnd_7316757 : Nat := 3757013173148934888288353

theorem tailTrace_7316757 : CollatzResearch.WordTrace tailWord_7316757 prefixEnd_7316757 3757013173148934888288353 := by
  unfold tailWord_7316757
  simp only [CollatzResearch.WordTrace]
  refine ⟨266864051553646466454764525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177909367702430977636509683 266864051553646466454764525)
  ·
    refine ⟨100074019332617424920536697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266864051553646466454764525 100074019332617424920536697)
    ·
      refine ⟨75055514499463068690402523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100074019332617424920536697 75055514499463068690402523)
      ·
        refine ⟨112583271749194603035603785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75055514499463068690402523 112583271749194603035603785)
        ·
          refine ⟨84437453811895952276702839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112583271749194603035603785 84437453811895952276702839)
          ·
            refine ⟨126656180717843928415054259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84437453811895952276702839 126656180717843928415054259)
            ·
              refine ⟨189984271076765892622581389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126656180717843928415054259 189984271076765892622581389)
              ·
                refine ⟨71244101653787209733468021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189984271076765892622581389 71244101653787209733468021)
                ·
                  refine ⟨6679134530042550912512627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71244101653787209733468021 6679134530042550912512627)
                  ·
                    refine ⟨10018701795063826368768941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6679134530042550912512627 10018701795063826368768941)
                    ·
                      refine ⟨3757013173148934888288353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10018701795063826368768941 3757013173148934888288353)
                      ·
                        rfl

theorem cell23_7316757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_7316757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316757 prefixEnd_7316757 := by exact prefixLift 7316757
  have htrace : WordTrace (prefixWord ++ tailWord_7316757) baseStart_7316757 baseEnd_7316757 := by
    simpa [prefixWord, tailWord_7316757, baseEnd_7316757] using wordTrace_append hprefix tailTrace_7316757
  have hstable : (prefixWord ++ tailWord_7316757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316757).length < 2 ^ (prefixWord ++ tailWord_7316757).sum := by decide
  have hdescent : baseEnd_7316757 < baseStart_7316757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316800 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_7316800 : Nat := 118140960795 + 7316800 * 2 ^ 59
def prefixEnd_7316800 : Nat := 4983230072969 + 3 ^ 40 * 7316800 * 2
def baseEnd_7316800 : Nat := 3757035252817078220050655

theorem tailTrace_7316800 : CollatzResearch.WordTrace tailWord_7316800 prefixEnd_7316800 3757035252817078220050655 := by
  unfold tailWord_7316800
  simp only [CollatzResearch.WordTrace]
  refine ⟨133432809946245342399289927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177910413261660456532386569 133432809946245342399289927)
  ·
    refine ⟨200149214919368013598934891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133432809946245342399289927 200149214919368013598934891)
    ·
      refine ⟨300223822379052020398402337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200149214919368013598934891 300223822379052020398402337)
      ·
        refine ⟨225167866784289015298801753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300223822379052020398402337 225167866784289015298801753)
        ·
          refine ⟨168875900088216761474101315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225167866784289015298801753 168875900088216761474101315)
          ·
            refine ⟨253313850132325142211151973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168875900088216761474101315 253313850132325142211151973)
            ·
              refine ⟨47496346899810964164590995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253313850132325142211151973 47496346899810964164590995)
              ·
                refine ⟨71244520349716446246886493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47496346899810964164590995 71244520349716446246886493)
                ·
                  refine ⟨26716695131143667342582435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71244520349716446246886493 26716695131143667342582435)
                  ·
                    refine ⟨40075042696715501013873653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26716695131143667342582435 40075042696715501013873653)
                    ·
                      refine ⟨3757035252817078220050655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40075042696715501013873653 3757035252817078220050655)
                      ·
                        rfl

theorem cell23_7316800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_7316800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316800 prefixEnd_7316800 := by exact prefixLift 7316800
  have htrace : WordTrace (prefixWord ++ tailWord_7316800) baseStart_7316800 baseEnd_7316800 := by
    simpa [prefixWord, tailWord_7316800, baseEnd_7316800] using wordTrace_append hprefix tailTrace_7316800
  have hstable : (prefixWord ++ tailWord_7316800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316800).length < 2 ^ (prefixWord ++ tailWord_7316800).sum := by decide
  have hdescent : baseEnd_7316800 < baseStart_7316800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316807 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 1, 6]
def baseStart_7316807 : Nat := 118140960795 + 7316807 * 2 ^ 59
def prefixEnd_7316807 : Nat := 4983230072969 + 3 ^ 40 * 7316807 * 2
def baseEnd_7316807 : Nat := 1252346282393886564221041

theorem tailTrace_7316807 : CollatzResearch.WordTrace tailWord_7316807 prefixEnd_7316807 1252346282393886564221041 := by
  unfold tailWord_7316807
  simp only [CollatzResearch.WordTrace]
  refine ⟨266865875203465324994084675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177910583468976883329389783 266865875203465324994084675)
  ·
    refine ⟨400298812805197987491127013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266865875203465324994084675 400298812805197987491127013)
    ·
      refine ⟨75056027400974622654586315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400298812805197987491127013 75056027400974622654586315)
      ·
        refine ⟨112584041101461933981879473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75056027400974622654586315 112584041101461933981879473)
        ·
          refine ⟨84438030826096450486409605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112584041101461933981879473 84438030826096450486409605)
          ·
            refine ⟨15832130779893084466201801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84438030826096450486409605 15832130779893084466201801)
            ·
              refine ⟨11874098084919813349651351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15832130779893084466201801 11874098084919813349651351)
              ·
                refine ⟨17811147127379720024477027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11874098084919813349651351 17811147127379720024477027)
                ·
                  refine ⟨26716720691069580036715541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17811147127379720024477027 26716720691069580036715541)
                  ·
                    refine ⟨1252346282393886564221041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26716720691069580036715541 1252346282393886564221041)
                    ·
                      rfl

theorem cell23_7316807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_7316807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316807 prefixEnd_7316807 := by exact prefixLift 7316807
  have htrace : WordTrace (prefixWord ++ tailWord_7316807) baseStart_7316807 baseEnd_7316807 := by
    simpa [prefixWord, tailWord_7316807, baseEnd_7316807] using wordTrace_append hprefix tailTrace_7316807
  have hstable : (prefixWord ++ tailWord_7316807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316807).length < 2 ^ (prefixWord ++ tailWord_7316807).sum := by decide
  have hdescent : baseEnd_7316807 < baseStart_7316807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316810 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_7316810 : Nat := 118140960795 + 7316810 * 2 ^ 59
def prefixEnd_7316810 : Nat := 4983230072969 + 3 ^ 40 * 7316810 * 2
def baseEnd_7316810 : Nat := 3757040387623623180925609

theorem tailTrace_7316810 : CollatzResearch.WordTrace tailWord_7316810 prefixEnd_7316810 3757040387623623180925609 := by
  unfold tailWord_7316810
  simp only [CollatzResearch.WordTrace]
  refine ⟨66716496155613614126610971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177910656414969637670962589 66716496155613614126610971)
  ·
    refine ⟨100074744233420421189916457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66716496155613614126610971 100074744233420421189916457)
    ·
      refine ⟨75056058175065315892437343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100074744233420421189916457 75056058175065315892437343)
      ·
        refine ⟨112584087262597973838656015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75056058175065315892437343 112584087262597973838656015)
        ·
          refine ⟨168876130893896960757984023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112584087262597973838656015 168876130893896960757984023)
          ·
            refine ⟨253314196340845441136976035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168876130893896960757984023 253314196340845441136976035)
            ·
              refine ⟨379971294511268161705464053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253314196340845441136976035 379971294511268161705464053)
              ·
                refine ⟨35622308860431390159887255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379971294511268161705464053 35622308860431390159887255)
                ·
                  refine ⟨53433463290647085239830883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35622308860431390159887255 53433463290647085239830883)
                  ·
                    refine ⟨80150194935970627859746325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53433463290647085239830883 80150194935970627859746325)
                    ·
                      refine ⟨3757040387623623180925609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80150194935970627859746325 3757040387623623180925609)
                      ·
                        rfl

theorem cell23_7316810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_7316810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316810 prefixEnd_7316810 := by exact prefixLift 7316810
  have htrace : WordTrace (prefixWord ++ tailWord_7316810) baseStart_7316810 baseEnd_7316810 := by
    simpa [prefixWord, tailWord_7316810, baseEnd_7316810] using wordTrace_append hprefix tailTrace_7316810
  have hstable : (prefixWord ++ tailWord_7316810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316810).length < 2 ^ (prefixWord ++ tailWord_7316810).sum := by decide
  have hdescent : baseEnd_7316810 < baseStart_7316810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316817 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_7316817 : Nat := 118140960795 + 7316817 * 2 ^ 59
def prefixEnd_7316817 : Nat := 4983230072969 + 3 ^ 40 * 7316817 * 2
def baseEnd_7316817 : Nat := 3757043981988204653538077

theorem tailTrace_7316817 : CollatzResearch.WordTrace tailWord_7316817 prefixEnd_7316817 3757043981988204653538077 := by
  unfold tailWord_7316817
  simp only [CollatzResearch.WordTrace]
  refine ⟨266866239933429096701948705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177910826622286064467965803 266866239933429096701948705)
  ·
    refine ⟨200149679950071822526461529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266866239933429096701948705 200149679950071822526461529)
    ·
      refine ⟨150112259962553866894846147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200149679950071822526461529 150112259962553866894846147)
      ·
        refine ⟨225168389943830800342269221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150112259962553866894846147 225168389943830800342269221)
        ·
          refine ⟨42219073114468275064175479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225168389943830800342269221 42219073114468275064175479)
          ·
            refine ⟨63328609671702412596263219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42219073114468275064175479 63328609671702412596263219)
            ·
              refine ⟨94992914507553618894394829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63328609671702412596263219 94992914507553618894394829)
              ·
                refine ⟨35622342940332607085398061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94992914507553618894394829 35622342940332607085398061)
                ·
                  refine ⟨13358378602624727657024273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35622342940332607085398061 13358378602624727657024273)
                  ·
                    refine ⟨10018783951968545742768205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13358378602624727657024273 10018783951968545742768205)
                    ·
                      refine ⟨3757043981988204653538077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10018783951968545742768205 3757043981988204653538077)
                      ·
                        rfl

theorem cell23_7316817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_7316817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316817 prefixEnd_7316817 := by exact prefixLift 7316817
  have htrace : WordTrace (prefixWord ++ tailWord_7316817) baseStart_7316817 baseEnd_7316817 := by
    simpa [prefixWord, tailWord_7316817, baseEnd_7316817] using wordTrace_append hprefix tailTrace_7316817
  have hstable : (prefixWord ++ tailWord_7316817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316817).length < 2 ^ (prefixWord ++ tailWord_7316817).sum := by decide
  have hdescent : baseEnd_7316817 < baseStart_7316817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316864 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 2, 1, 3]
def baseStart_7316864 : Nat := 118140960795 + 7316864 * 2 ^ 59
def prefixEnd_7316864 : Nat := 4983230072969 + 3 ^ 40 * 7316864 * 2
def baseEnd_7316864 : Nat := 3757068115578965969650361

theorem tailTrace_7316864 : CollatzResearch.WordTrace tailWord_7316864 prefixEnd_7316864 3757068115578965969650361 := by
  unfold tailWord_7316864
  simp only [CollatzResearch.WordTrace]
  refine ⟨133433977082129411864454823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177911969442839215819273097 133433977082129411864454823)
  ·
    refine ⟨200150965623194117796682235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133433977082129411864454823 200150965623194117796682235)
    ·
      refine ⟨300226448434791176695023353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200150965623194117796682235 300226448434791176695023353)
      ·
        refine ⟨225169836326093382521267515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300226448434791176695023353 225169836326093382521267515)
        ·
          refine ⟨337754754489140073781901273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225169836326093382521267515 337754754489140073781901273)
          ·
            refine ⟨253316065866855055336425955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337754754489140073781901273 253316065866855055336425955)
            ·
              refine ⟨379974098800282583004638933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253316065866855055336425955 379974098800282583004638933)
              ·
                refine ⟨8905642940631623039171225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 379974098800282583004638933 8905642940631623039171225)
                ·
                  refine ⟨6679232205473717279378419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8905642940631623039171225 6679232205473717279378419)
                  ·
                    refine ⟨10018848308210575919067629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6679232205473717279378419 10018848308210575919067629)
                    ·
                      refine ⟨3757068115578965969650361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10018848308210575919067629 3757068115578965969650361)
                      ·
                        rfl

theorem cell23_7316864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_7316864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316864 prefixEnd_7316864 := by exact prefixLift 7316864
  have htrace : WordTrace (prefixWord ++ tailWord_7316864) baseStart_7316864 baseEnd_7316864 := by
    simpa [prefixWord, tailWord_7316864, baseEnd_7316864] using wordTrace_append hprefix tailTrace_7316864
  have hstable : (prefixWord ++ tailWord_7316864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316864).length < 2 ^ (prefixWord ++ tailWord_7316864).sum := by decide
  have hdescent : baseEnd_7316864 < baseStart_7316864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316937 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 3]
def baseStart_7316937 : Nat := 118140960795 + 7316937 * 2 ^ 59
def prefixEnd_7316937 : Nat := 4983230072969 + 3 ^ 40 * 7316937 * 2
def baseEnd_7316937 : Nat := 3757105599666744184037525

theorem tailTrace_7316937 : CollatzResearch.WordTrace tailWord_7316937 prefixEnd_7316937 3757105599666744184037525 := by
  unfold tailWord_7316937
  simp only [CollatzResearch.WordTrace]
  refine ⟨266870616692994357196317065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177913744461996238130878043 266870616692994357196317065)
  ·
    refine ⟨200152962519745767897237799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266870616692994357196317065 200152962519745767897237799)
    ·
      refine ⟨300229443779618651845856699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200152962519745767897237799 300229443779618651845856699)
      ·
        refine ⟨450344165669427977768785049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300229443779618651845856699 450344165669427977768785049)
        ·
          refine ⟨337758124252070983326588787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450344165669427977768785049 337758124252070983326588787)
          ·
            refine ⟨506637186378106474989883181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337758124252070983326588787 506637186378106474989883181)
            ·
              refine ⟨189988944891789928121206193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506637186378106474989883181 189988944891789928121206193)
              ·
                refine ⟨142491708668842446090904645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189988944891789928121206193 142491708668842446090904645)
                ·
                  refine ⟨26717195375407958642044621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142491708668842446090904645 26717195375407958642044621)
                  ·
                    refine ⟨10018948265777984490766733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26717195375407958642044621 10018948265777984490766733)
                    ·
                      refine ⟨3757105599666744184037525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10018948265777984490766733 3757105599666744184037525)
                      ·
                        rfl

theorem cell23_7316937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_7316937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316937 prefixEnd_7316937 := by exact prefixLift 7316937
  have htrace : WordTrace (prefixWord ++ tailWord_7316937) baseStart_7316937 baseEnd_7316937 := by
    simpa [prefixWord, tailWord_7316937, baseEnd_7316937] using wordTrace_append hprefix tailTrace_7316937
  have hstable : (prefixWord ++ tailWord_7316937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316937).length < 2 ^ (prefixWord ++ tailWord_7316937).sum := by decide
  have hdescent : baseEnd_7316937 < baseStart_7316937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7316961 : List Nat := [1, 2, 3, 1, 2, 3, 4, 2, 5]
def baseStart_7316961 : Nat := 118140960795 + 7316961 * 2 ^ 59
def prefixEnd_7316961 : Nat := 4983230072969 + 3 ^ 40 * 7316961 * 2
def baseEnd_7316961 : Nat := 417457547022494676681935

theorem tailTrace_7316961 : CollatzResearch.WordTrace tailWord_7316961 prefixEnd_7316961 417457547022494676681935 := by
  unfold tailWord_7316961
  simp only [CollatzResearch.WordTrace]
  refine ⟨266871492044907409295190737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177914328029938272863460491 266871492044907409295190737)
  ·
    refine ⟨200153619033680556971393053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266871492044907409295190737 200153619033680556971393053)
    ·
      refine ⟨75057607137630208864272395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200153619033680556971393053 75057607137630208864272395)
      ·
        refine ⟨112586410706445313296408593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75057607137630208864272395 112586410706445313296408593)
        ·
          refine ⟨84439808029833984972306445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112586410706445313296408593 84439808029833984972306445)
          ·
            refine ⟨31664928011187744364614917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84439808029833984972306445 31664928011187744364614917)
            ·
              refine ⟨5937174002097702068365297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31664928011187744364614917 5937174002097702068365297)
              ·
                refine ⟨4452880501573276551273973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937174002097702068365297 4452880501573276551273973)
                ·
                  refine ⟨417457547022494676681935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4452880501573276551273973 417457547022494676681935)
                  ·
                    rfl

theorem cell23_7316961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 5].length) (baseStart_7316961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7316961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7316961 prefixEnd_7316961 := by exact prefixLift 7316961
  have htrace : WordTrace (prefixWord ++ tailWord_7316961) baseStart_7316961 baseEnd_7316961 := by
    simpa [prefixWord, tailWord_7316961, baseEnd_7316961] using wordTrace_append hprefix tailTrace_7316961
  have hstable : (prefixWord ++ tailWord_7316961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7316961).length < 2 ^ (prefixWord ++ tailWord_7316961).sum := by decide
  have hdescent : baseEnd_7316961 < baseStart_7316961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7316961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7317021 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_7317021 : Nat := 118140960795 + 7317021 * 2 ^ 59
def prefixEnd_7317021 : Nat := 4983230072969 + 3 ^ 40 * 7317021 * 2
def baseEnd_7317021 : Nat := 1252382910680573951795713

theorem tailTrace_7317021 : CollatzResearch.WordTrace tailWord_7317021 prefixEnd_7317021 1252382910680573951795713 := by
  unfold tailWord_7317021
  simp only [CollatzResearch.WordTrace]
  refine ⟨266873680424690039542374917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177915786949793359694916611 266873680424690039542374917)
  ·
    refine ⟨50038815079629382414195297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 266873680424690039542374917 50038815079629382414195297)
    ·
      refine ⟨37529111309722036810646473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50038815079629382414195297 37529111309722036810646473)
      ·
        refine ⟨28146833482291527607984855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37529111309722036810646473 28146833482291527607984855)
        ·
          refine ⟨42220250223437291411977283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28146833482291527607984855 42220250223437291411977283)
          ·
            refine ⟨63330375335155937117965925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42220250223437291411977283 63330375335155937117965925)
            ·
              refine ⟨11874445375341738209618611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63330375335155937117965925 11874445375341738209618611)
              ·
                refine ⟨17811668063012607314427917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11874445375341738209618611 17811668063012607314427917)
                ·
                  refine ⟨6679375523629727742910469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17811668063012607314427917 6679375523629727742910469)
                  ·
                    refine ⟨1252382910680573951795713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6679375523629727742910469 1252382910680573951795713)
                    ·
                      rfl

theorem cell23_7317021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_7317021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7317021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7317021 prefixEnd_7317021 := by exact prefixLift 7317021
  have htrace : WordTrace (prefixWord ++ tailWord_7317021) baseStart_7317021 baseEnd_7317021 := by
    simpa [prefixWord, tailWord_7317021, baseEnd_7317021] using wordTrace_append hprefix tailTrace_7317021
  have hstable : (prefixWord ++ tailWord_7317021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7317021).length < 2 ^ (prefixWord ++ tailWord_7317021).sum := by decide
  have hdescent : baseEnd_7317021 < baseStart_7317021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7317021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
